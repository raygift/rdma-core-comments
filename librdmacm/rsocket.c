/*
 * Copyright (c) 2008-2019 Intel Corporation.  All rights reserved.
 *
 * This software is available to you under a choice of one of two
 * licenses.  You may choose to be licensed under the terms of the GNU
 * General Public License (GPL) Version 2, available from the file
 * COPYING in the main directory of this source tree, or the
 * OpenIB.org BSD license below:
 *
 *     Redistribution and use in source and binary forms, with or
 *     without modification, are permitted provided that the following
 *     conditions are met:
 *
 *      - Redistributions of source code must retain the above
 *        copyright notice, this list of conditions and the following
 *        disclaimer.
 *
 *      - Redistributions in binary form must reproduce the above
 *        copyright notice, this list of conditions and the following
 *        disclaimer in the documentation and/or other materials
 *        provided with the distribution.
 *
 * THE SOFTWARE IS PROVIDED "AS IS", WITHOUT WARRANTY OF ANY KIND,
 * EXPRESS OR IMPLIED, INCLUDING BUT NOT LIMITED TO THE WARRANTIES OF
 * MERCHANTABILITY, FITNESS FOR A PARTICULAR PURPOSE AND
 * NONINFRINGEMENT. IN NO EVENT SHALL THE AUTHORS OR COPYRIGHT HOLDERS
 * BE LIABLE FOR ANY CLAIM, DAMAGES OR OTHER LIABILITY, WHETHER IN AN
 * ACTION OF CONTRACT, TORT OR OTHERWISE, ARISING FROM, OUT OF OR IN
 * CONNECTION WITH THE SOFTWARE OR THE USE OR OTHER DEALINGS IN THE
 * SOFTWARE.
 *
 */
#define _GNU_SOURCE
#include <config.h>

#include <sys/types.h>
#include <sys/socket.h>
#include <sys/time.h>
#include <endian.h>
#include <stdarg.h>
#include <netdb.h>
#include <unistd.h>
#include <fcntl.h>
#include <stdio.h>
#include <stddef.h>
#include <string.h>
#include <netinet/tcp.h>
#include <sys/epoll.h>
#include <sys/eventfd.h>
#include <search.h>
#include <time.h>
#include <byteswap.h>
#include <util/compiler.h>
#include <util/util.h>
#include <ccan/container_of.h>

#include <rdma/rdma_cma.h>
#include <rdma/rdma_verbs.h>
#include <rdma/rsocket.h>
#include "cma.h"
#include "indexer.h"

#define RS_OLAP_START_SIZE 2048
#define RS_MAX_TRANSFER 65536
#define RS_SNDLOWAT 2048
#define RS_QP_MIN_SIZE 16
#define RS_QP_MAX_SIZE 0xFFFE
#define RS_QP_CTRL_SIZE 4	/* must be power of 2 */
#define RS_CONN_RETRIES 6
#define RS_SGL_SIZE 2
static struct index_map idm;
static pthread_mutex_t mut = PTHREAD_MUTEX_INITIALIZER;
static pthread_mutex_t svc_mut = PTHREAD_MUTEX_INITIALIZER;

struct rsocket;

enum {
	RS_SVC_NOOP,
	RS_SVC_ADD_DGRAM,
	RS_SVC_REM_DGRAM,
	RS_SVC_ADD_KEEPALIVE,
	RS_SVC_REM_KEEPALIVE,
	RS_SVC_MOD_KEEPALIVE,
	RS_SVC_ADD_CM,
	RS_SVC_REM_CM,
};

struct rs_svc_msg {
	uint32_t cmd;
	uint32_t status;
	struct rsocket *rs;
};

/* rsocket 会创建线程处理链接，rs_svc 用来记录创建的线程ip，以及线程运行所需的相关信息
 * rsocket service 结构体
 * 存在 tcp_svc ，udp_svc，listen_svc，connect_svc 几种
 * 结构体中记录有需要执行svc 的rsocket 实例，svc 的线程号，上下文等
 */
struct rs_svc {// 每个svc 可以对应多个rsocket 
	pthread_t id;// 创建的线程id
	int sock[2];// 线程通信管道socketpait
	int cnt;// 线程正在服务的rsocket 对象数量
	int size;// 线程能够服务的rsocket 对象容量
	int context_size;// 线程服务的每个rsocket 对应的context 的空间大小
	void *(*run)(void *svc);
	struct rsocket **rss;// 线程正在服务的rsocket 数组指针
	void *contexts;// 线程服务的所有rsocket 的context 集中存放的位置
};

static struct pollfd *udp_svc_fds;
static void *udp_svc_run(void *arg);
static struct rs_svc udp_svc = {
	.context_size = sizeof(*udp_svc_fds),
	.run = udp_svc_run
};
static uint64_t *tcp_svc_timeouts;
static void *tcp_svc_run(void *arg);
static struct rs_svc tcp_svc = {
	.context_size = sizeof(*tcp_svc_timeouts),
	.run = tcp_svc_run
};
static void *cm_svc_run(void *arg);
static struct rs_svc listen_svc = {
	.context_size = sizeof(struct pollfd),
	.run = cm_svc_run
};
static struct rs_svc connect_svc = {
	.context_size = sizeof(struct pollfd),
	.run = cm_svc_run
};

static struct rs_svc accept_svc = {
	.context_size = sizeof(struct pollfd),
	.run = cm_svc_run
};

static uint32_t pollcnt;
static bool suspendpoll;
static int pollsignal = -1;

static uint16_t def_iomap_size = 0;
static uint16_t def_inline = 64;
static uint16_t def_sqsize = 384;
static uint16_t def_rqsize = 384;
static uint32_t def_mem = (1 << 17);
static uint32_t def_wmem = (1 << 17);
static uint32_t polling_time = 10;
static int wake_up_interval = 5000;

/*
 * Immediate data format is determined by the upper bits
 * bit 31: message type, 0 - data, 1 - control
 * bit 30: buffers updated, 0 - target, 1 - direct-receive
 * bit 29: more data, 0 - end of transfer, 1 - more data available
 *
 * for data transfers:
 * bits [28:0]: bytes transferred
 * for control messages:
 * SGL, CTRL
 * bits [28-0]: receive credits granted
 * IOMAP_SGL
 * bits [28-16]: reserved, bits [15-0]: index
 */

enum {
	RS_OP_DATA,
	RS_OP_RSVD_DATA_MORE,
	RS_OP_WRITE, /* opcode is not transmitted over the network */
	RS_OP_RSVD_DRA_MORE,
	RS_OP_SGL,
	RS_OP_RSVD,
	RS_OP_IOMAP_SGL,
	RS_OP_CTRL
};
#define rs_msg_set(op, data)  ((op << 29) | (uint32_t) (data))
#define rs_msg_op(imm_data)   (imm_data >> 29)
#define rs_msg_data(imm_data) (imm_data & 0x1FFFFFFF)/* 将imm_data 高3位设置为0 */
#define RS_MSG_SIZE	      sizeof(uint32_t)

#define RS_WR_ID_FLAG_RECV (((uint64_t) 1) << 63)
#define RS_WR_ID_FLAG_MSG_SEND (((uint64_t) 1) << 62) /* See RS_OPT_MSG_SEND */
#define rs_send_wr_id(data) ((uint64_t) data) /* data 高位补0，最高位是0 表示是send wr */
#define rs_recv_wr_id(data) (RS_WR_ID_FLAG_RECV | (uint64_t) data) /* data 高位补0，最高位设为1 表示是recv wr */
#define rs_wr_is_recv(wr_id) (wr_id & RS_WR_ID_FLAG_RECV)
#define rs_wr_is_msg_send(wr_id) (wr_id & RS_WR_ID_FLAG_MSG_SEND)
#define rs_wr_data(wr_id) ((uint32_t) wr_id)

enum {
	RS_CTRL_DISCONNECT,
	RS_CTRL_KEEPALIVE,
	RS_CTRL_SHUTDOWN
};

struct rs_msg {
	uint32_t op;
	uint32_t data;
};

struct ds_qp;

struct ds_rmsg {
	struct ds_qp	*qp;
	uint32_t	offset;
	uint32_t	length;
};

struct ds_smsg {
	struct ds_smsg	*next;
};

struct rs_sge {
	uint64_t addr;
	uint32_t key;
	uint32_t length;
};

struct rs_iomap {
	uint64_t offset;
	struct rs_sge sge;
};

struct rs_iomap_mr {
	uint64_t offset;
	struct ibv_mr *mr;
	dlist_entry entry;
	_Atomic(int) refcnt;
	int index;	/* -1 if mapping is local and not in iomap_list */
};

#define RS_MAX_CTRL_MSG    (sizeof(struct rs_sge))
#define rs_host_is_net()   (__BYTE_ORDER == __BIG_ENDIAN)
#define RS_CONN_FLAG_NET   (1 << 0)
#define RS_CONN_FLAG_IOMAP (1 << 1)

struct rs_conn_data {
	uint8_t		  version;				// 当前版本为1
	uint8_t		  flags;				 // RS_CONN_FLAG_NET 如果主机时大端，设为1；为write 确定字节顺序
	__be16		  credits;				// 初始的receive credits 数量
	uint8_t		  reserved[3];			// 设为 0
	uint8_t		  target_iomap_size;	// 
	struct rs_sge	  target_sgl;		// 将本地接收 credits 信息的receive buffer 信息暴露给对端，以便对端进行update credits 操作；
										// target SGL 的地址，大小（entries 数量），以及rkey；
										// 远端将接收到的target_sgl 复制到它们的rs->remote_sgl 中保存（未来使用remote SGL 执行 update credits 操作）

	struct rs_sge	  data_buf;			// 用来告知远端 本地的receive buffer 地址等信息
										// 初始的receive buffer 地址，大小（字节数），以及rkey
										// 远端将接收到的 data_buf 复制到它们的第一个target_sgl[0]中（复制到target SGE 是为了将自己的receive buffer地址发送给对方）
										// 与target_sgl 配合使用
};

struct rs_conn_private_data {
	union {
		struct rs_conn_data		conn_data;
		struct {
			struct ib_connect_hdr	ib_hdr;
			struct rs_conn_data	conn_data;
		} af_ib;
	};
};

/*
 * rsocket states are ordered as passive, connecting, connected, disconnected.
 */
enum rs_state {
	rs_init,
	rs_bound	   =		    0x0001,
	rs_listening	   =		    0x0002,
	rs_opening	   =		    0x0004,
	rs_resolving_addr  = rs_opening |   0x0010,
	rs_resolving_route = rs_opening |   0x0020,
	rs_connecting      = rs_opening |   0x0040,
	rs_accepting       = rs_opening |   0x0080,
	rs_connected	   =		    0x0100,
	rs_writable 	   =		    0x0200,
	rs_readable	   =		    0x0400,
	rs_connect_rdwr    = rs_connected | rs_readable | rs_writable,
	rs_connect_error   =		    0x0800,
	rs_disconnected	   =		    0x1000,
	rs_error	   =		    0x2000,
};

#define RS_OPT_SWAP_SGL   (1 << 0)
/*
 * iWarp does not support RDMA write with immediate data.  For iWarp, we
 * transfer rsocket messages as inline sends.
 */
#define RS_OPT_MSG_SEND   (1 << 1)
#define RS_OPT_UDP_SVC    (1 << 2)
#define RS_OPT_KEEPALIVE  (1 << 3)
#define RS_OPT_CM_SVC	  (1 << 4)

union socket_addr {
	struct sockaddr		sa;
	struct sockaddr_in	sin;
	struct sockaddr_in6	sin6;
};

struct ds_header {
	uint8_t		  version;
	uint8_t		  length;
	__be16		  port;
	union {
		__be32  ipv4;
		struct {
			__be32 flowinfo;
			uint8_t  addr[16];
		} ipv6;
	} addr;
};

#define DS_IPV4_HDR_LEN  8
#define DS_IPV6_HDR_LEN 24

struct ds_dest {
	union socket_addr addr;	/* must be first */
	struct ds_qp	  *qp;
	struct ibv_ah	  *ah;
	uint32_t	   qpn;
};

struct ds_qp {
	dlist_entry	  list;
	struct rsocket	  *rs;
	struct rdma_cm_id *cm_id;
	struct ds_header  hdr;
	struct ds_dest	  dest;

	struct ibv_mr	  *smr;
	struct ibv_mr	  *rmr;
	uint8_t		  *rbuf;

	int		  cq_armed;
};

struct rsocket {
	int		  type;
	int		  index;
	fastlock_t	  slock;
	fastlock_t	  rlock;
	fastlock_t	  cq_lock;
	fastlock_t	  cq_wait_lock;
	fastlock_t	  map_lock; /* acquire slock first if needed */

	union {
		/* data stream */
		struct {
			struct rdma_cm_id *cm_id;
			uint64_t	  tcp_opts;
			unsigned int	  keepalive_time;
			int		  accept_queue[2];// socketpair() 创建的socket 对，都可以用于读写；写socket 0 后，再读取socket 0会被阻塞，只能从socket 1 成功读取；读、写操作可位于同一进程，也可位于不同进程

			unsigned int	  ctrl_seqno; 				// 记录发送过的ctrl 消息数量，包括update credits 和其他ctrl 消息；每执行一次 ctrl 发送，加1（iWarp 额外再加1）
			unsigned int	  ctrl_max_seqno;			// rsocket 创建时初始化为4，控制可发送的ctrl 消息数量，每获得一次ctrl 消息发送wc ，max_seqno 加1
			uint16_t	  sseq_no;// 发送消息的序号，每执行一次发送（send/write），序号加1
			uint16_t	  sseq_comp;// send squence completion
			uint16_t	  rseq_no;				// 记录接收端为了接收 rdma_write_with_imm 而事先执行过的 ibv_post_recv() 次数
			uint16_t	  rseq_comp;			// 当前可接收的rdma write with imm 操作的最大次数，初始时赋值为 rq_size 的一半（用于控制接收方接收速度，当 rseq_comp 小于 rseq_no 时）

// remote 相关属性，记录的是本地提供给远端 rdma write 时需要使用到的信息，本地通过更新 remote 相关属性，控制远端写入时使用的内存

			int		  remote_sge;						// 被远端写内存时，使用的 rbuf 内存分区号；初始为0；当接收到对端的连接后，将对应remote_sge 更新为1；后续接收完数据后，主动调用 rs_send_credits() 将 remote_sge+1 ；当增长到 2 时重置为0，循环使用
			struct rs_sge	  remote_sgl;				// 记录 连接建立时，对端传输来的 conn->target_sgl 信息，用来进行 credits 更新使用
			struct rs_sge	  remote_iomap;	// （iomap 相关，暂不涉及）

// target 相关属性，记录的是主动执行 rdma write data（而非update credits 或 发送ctrl）操作时，向远端写入需要用到的信息
// 当收到远端的update credits 时，需要更新本地可更新 target 相关属性，从而控制写入到远端的内存位置
// 向远端write data数据（而非更新sge 或发送ctrl 消息）时，发送数据是向 tcp->target_sgl[tcp->target_sge].addr 地址发送
			struct ibv_mr	  *target_mr;				// 本机写远端内存时，远端注册的 mr
			int		  target_sge;						// 记录使用的target_sql 中元素的序号，target_sgl 长度为2，因此序号为0或1
			int		  target_iomap_size;
			void		  *target_buffer_list;			// 本机申请target_buffer_list
			volatile struct rs_sge	  *target_sgl;		// 每个target_sgl 的成员，对应一个远端 receive buffer 的信息；
														// 本机将target_sgl 初始化为target_buffer_list地址；将建立连接时收到的对端remote buffer信息存储在target_sql[0]

			struct rs_iomap   *target_iomap;

			int		  rbuf_msg_index;	// recv buffer msg index，msg 位于recv buffer 的位置
			int		  rbuf_bytes_avail;	// recv bffer 中可用的字节数
			int		  rbuf_free_offset;	//recv buffer 空闲空间的起始偏移量
			int		  rbuf_offset;		// recv buffer 偏移量
			struct ibv_mr	  *rmr;
			uint8_t		  *rbuf;

			int		  sbuf_bytes_avail;		// send buffer 中可用的字节数，rs_init_bufs初始时为 sbuf_size；rs_poll_cq() 中获得发送数据消息的完成事件后，sbuf_bytes_avail 增加已完成发送的数据长度；每执行一次发送，需要减去发送的数据长度
			struct ibv_mr	  *smr;
			struct ibv_sge	  ssgl[2];// send sgl，包含两个ibv_sge元素，记录了addr,length,lkey；初始时两个元素的addr 均在rs_init_bufs() 中被设为sbuf起始地址；在rs_sbuf_left() 中使用 rs->sbuf[rs->sbuf_size] 地址减去ssgl[0].addr 得到send buf 中未发送的长度
		};
    		/* datagram */
		struct {
			struct ds_qp	  *qp_list;
			void		  *dest_map;
			struct ds_dest    *conn_dest;

			int		  udp_sock;
			int		  epfd;
			int		  rqe_avail;
			struct ds_smsg	  *smsg_free;
		};
	};

	int		  opts;
	int		  fd_flags;
	uint64_t	  so_opts;
	uint64_t	  ipv6_opts;
	void		  *optval;
	size_t		  optlen;
	int		  state;
	int		  cq_armed;// 标识cq 是否被执行过ibv_req_notify_cq()；若为执行过，在rs_process_cq()中执行并将cq_armed设为1
	int		  retries;
	int		  err;

	int		  sqe_avail;// 获取数据（而非控制）消息发送完成事件后，sqe_avail 加1；每执行一次数据发送，sqe_avail减1；每执行一次rdma send，sqe_avail 额外再减1
	uint32_t	  sbuf_size;// send buffer 大小，单位为字节，rs_alloc()中被初始化为1 << 17，在rs_init_bufs() 中初始时会据此申请send mr
	uint16_t	  sq_size;// 
	uint16_t	  sq_inline;


	// 接收数据使用到的核心概念为 recv queue
	// msg 为recv queue 中的元素，单个 msg 大小为32位，使用宏 RS_MSG_SIZE 表示
	// 在使用rdma send 的iWarp协议中，total_rbuf_size 等于 rq_size + rq size * RS_MSG_SIZE（暂不深究）
	// 在RoCEv2 中，rbuf_size 初始在 rs_alloc() 被设为 def_mem = (1 << 17)，
	uint32_t	  rbuf_size;
	uint16_t	  rq_size;				// recv queue 的大小，初始在 rs_alloc() 中被设为静态常量 def_sqsize 的值 384；在 rs_set_qp_size() 中进行适配，保证不大于rdma 设备的 max_qp_wr，且不小于 宏 RS_QP_MIN_SIZE 16
										// rq_size 是 rbuf_msg_index 属性的最大值
	int		  rmsg_head;				// rmsg 队首索引
	int		  rmsg_tail;				// rmsg 队尾索引；若tail 增长到 rq_size , 则重置为0
	union {
		struct rs_msg	  *rmsg;		// rmsg 队列指针，rmsg 不等于 recv queue 中的 msg；rmsg 同时记录了 32位的 op 和32位的 data；
		struct ds_rmsg	  *dmsg;
	};

	uint8_t		  *sbuf;// sbuf 指向send buffer 的起始地址；由于需存储ctrl 消息，在rs_init_bufs() 中分配的send buffer 大小可能会比sbuf_size 要更大
	struct rs_iomap_mr *remote_iomappings;
	dlist_entry	  iomap_list;
	dlist_entry	  iomap_queue;
	int		  iomap_pending;
	int		  unack_cqe;// rs_get_cq_event()执行ibv_get_cq_event()正常返回后，unack_cqe加1；
};

#define DS_UDP_TAG 0x55555555

struct ds_udp_header {
	__be32		  tag;
	uint8_t		  version;
	uint8_t		  op;
	uint8_t		  length;
	uint8_t		  reserved;
	__be32		  qpn;  /* lower 8-bits reserved */
	union {
		__be32	 ipv4;
		uint8_t  ipv6[16];
	} addr;
};

#define DS_UDP_IPV4_HDR_LEN 16
#define DS_UDP_IPV6_HDR_LEN 28

#define ds_next_qp(qp) container_of((qp)->list.next, struct ds_qp, list)

static void write_all(int fd, const void *msg, size_t len)
{
	// FIXME: if fd is a socket this really needs to handle EINTR and other conditions.
	ssize_t __attribute__((unused)) rc = write(fd, msg, len);
	assert(rc == len);
}

static void read_all(int fd, void *msg, size_t len)
{
	// FIXME: if fd is a socket this really needs to handle EINTR and other conditions.
	ssize_t __attribute__((unused)) rc = read(fd, msg, len);
	assert(rc == len);
}

static uint64_t rs_time_us(void)
{
	struct timespec now;

	clock_gettime(CLOCK_MONOTONIC, &now);
	return now.tv_sec * 1000000 + now.tv_nsec / 1000;
}

static void ds_insert_qp(struct rsocket *rs, struct ds_qp *qp)
{
	if (!rs->qp_list)
		dlist_init(&qp->list);
	else
		dlist_insert_head(&qp->list, &rs->qp_list->list);
	rs->qp_list = qp;
}

static void ds_remove_qp(struct rsocket *rs, struct ds_qp *qp)
{
	if (qp->list.next != &qp->list) {
		rs->qp_list = ds_next_qp(qp);
		dlist_remove(&qp->list);
	} else {
		rs->qp_list = NULL;
	}
}
// 向执行svc 的子线程发送消息，子线程在 cm_svc_run 中获取cmd并执行；
// 子线程还会对所服务的rsocket fd 进行监听，获取到事件后执行相应操作：
// 1. 若主线程在listen，则子线程执行listen_svc，监听到事件后执行rs_accept；
// 2. 若主线程在connect，则子线程执行connect_svc，若根据rs 状态判断主线程仍未完成connect 操作，则执行connect 动作；否则在子线程中处理异常主线程未能处理的cm_event
// svc 执行完毕后，通知父线程执行结果；父线程等待子进程返回执行结果并退出
static int rs_notify_svc(struct rs_svc *svc, struct rsocket *rs, int cmd)
{
	// printf("rs_notify_svc rs %d cmd %d\n",rs->index,cmd);
	struct rs_svc_msg msg;
	int ret;

	pthread_mutex_lock(&svc_mut);
	if (!svc->cnt) {// svc->cnt == 0 表示尚未给rsocket 实例创建过线程；
		ret = socketpair(AF_UNIX, SOCK_STREAM, 0, svc->sock);// 创建 socketpair 流管道，用于在线程间通信，保存在svc->sock 属性中
		printf("rsocket debug: rs_notify_svc socketpair ret %d, svc->sock %d %d\n",ret,svc->sock[0],svc->sock[1]);
		if (ret)
			goto unlock;

		ret = pthread_create(&svc->id, NULL, svc->run, svc);// 创建新线程，从 svc->run（在文件开头已经将run 赋值为 cm_svc_run ） 开始执行，并传入参数为svc
		if (ret) {// 创建线程失败，关闭管道
			ret = ERR(ret);
			goto closepair;
		}
	}
// rsocket 已创建并运行新线程
	msg.cmd = cmd;
	msg.status = EINVAL;
	msg.rs = rs;
	write_all(svc->sock[0], &msg, sizeof(msg));// 将msg 写入到socket[0]中，与子线程通信
	read_all(svc->sock[0], &msg, sizeof(msg));// 从socket[0]中读取数据，存入msg 中，从子线程读取信息
	ret = rdma_seterrno(msg.status);// 设置errno
	if (svc->cnt)// svc->cnt 不为0，表示rsocket service 中已经有rsocket 实例被加入
		goto unlock;// 跳过等待其他线程，跳过关闭socketpair

	pthread_join(svc->id, NULL);// 访问子线程，在该线程退出之前阻塞等待
closepair:
	close(svc->sock[0]);
	close(svc->sock[1]);
unlock:
	pthread_mutex_unlock(&svc_mut);
	return ret;
}

static int ds_compare_addr(const void *dst1, const void *dst2)
{
	const struct sockaddr *sa1, *sa2;
	size_t len;

	sa1 = (const struct sockaddr *) dst1;
	sa2 = (const struct sockaddr *) dst2;

	len = (sa1->sa_family == AF_INET6 && sa2->sa_family == AF_INET6) ?
	      sizeof(struct sockaddr_in6) : sizeof(struct sockaddr_in);
	return memcmp(dst1, dst2, len);
}

static int rs_value_to_scale(int value, int bits)
{
	return value <= (1 << (bits - 1)) ?
	       value : (1 << (bits - 1)) | (value >> bits);
}

static int rs_scale_to_value(int value, int bits)
{
	return value <= (1 << (bits - 1)) ?
	       value : (value & ~(1 << (bits - 1))) << bits;
}

/* gcc > ~5 will not allow (void)fscanf to suppress -Wunused-result, but this
   will do it.  In this case ignoring the result is OK (but horribly
   unfriendly to user) since the library has a sane default. */
#define failable_fscanf(f, fmt, ...)                                           \
	{                                                                      \
		int rc = fscanf(f, fmt, __VA_ARGS__);                          \
		(void) rc;                                                     \
	}

static void rs_configure(void)
{
	FILE *f;
	static int init;

	if (init)
		return;

	pthread_mutex_lock(&mut);
	if (init)
		goto out;

	if (ucma_init()) // 确定存在rdma 设备且支持ib 协议
		goto out;
	ucma_ib_init();

	if ((f = fopen(RS_CONF_DIR "/polling_time", "r"))) {
		failable_fscanf(f, "%u", &polling_time);
		fclose(f);
	}

	f = fopen(RS_CONF_DIR "/wake_up_interval", "r");
	if (f) {
		failable_fscanf(f, "%d", &wake_up_interval);
		fclose(f);
	}
	if ((f = fopen(RS_CONF_DIR "/inline_default", "r"))) {
		failable_fscanf(f, "%hu", &def_inline);
		fclose(f);
	}

	if ((f = fopen(RS_CONF_DIR "/sqsize_default", "r"))) {
		failable_fscanf(f, "%hu", &def_sqsize);
		fclose(f);
	}

	if ((f = fopen(RS_CONF_DIR "/rqsize_default", "r"))) {
		failable_fscanf(f, "%hu", &def_rqsize);
		fclose(f);
	}

	if ((f = fopen(RS_CONF_DIR "/mem_default", "r"))) {
		failable_fscanf(f, "%u", &def_mem);
		fclose(f);

		if (def_mem < 1)
			def_mem = 1;
	}

	if ((f = fopen(RS_CONF_DIR "/wmem_default", "r"))) {
		failable_fscanf(f, "%u", &def_wmem);
		fclose(f);
		if (def_wmem < RS_SNDLOWAT)
			def_wmem = RS_SNDLOWAT << 1;
	}

	if ((f = fopen(RS_CONF_DIR "/iomap_size", "r"))) {
		failable_fscanf(f, "%hu", &def_iomap_size);
		fclose(f);

		/* round to supported values */
		def_iomap_size = (uint8_t) rs_value_to_scale(
			(uint16_t) rs_scale_to_value(def_iomap_size, 8), 8);
	}
	init = 1;
out:
	pthread_mutex_unlock(&mut);
}

static int rs_insert(struct rsocket *rs, int index)
{
	pthread_mutex_lock(&mut);
	rs->index = idm_set(&idm, index, rs);// 将rs 存入index_map 中，原样返回index
	pthread_mutex_unlock(&mut);
	return rs->index;
}

static void rs_remove(struct rsocket *rs)
{
	pthread_mutex_lock(&mut);
	idm_clear(&idm, rs->index);
	pthread_mutex_unlock(&mut);
}

/* We only inherit from listening sockets */
static struct rsocket *rs_alloc(struct rsocket *inherited_rs, int type)
{
	struct rsocket *rs;

	rs = calloc(1, sizeof(*rs));
	if (!rs)
		return NULL;

	rs->type = type;
	rs->index = -1;
	if (type == SOCK_DGRAM) {
		rs->udp_sock = -1;
		rs->epfd = -1;
	}

	if (inherited_rs) {
		rs->sbuf_size = inherited_rs->sbuf_size;
		rs->rbuf_size = inherited_rs->rbuf_size;
		rs->sq_inline = inherited_rs->sq_inline;
		rs->sq_size = inherited_rs->sq_size;
		rs->rq_size = inherited_rs->rq_size;
		if (type == SOCK_STREAM) {
			rs->ctrl_max_seqno = inherited_rs->ctrl_max_seqno;
			rs->target_iomap_size = inherited_rs->target_iomap_size;
		}
	} else {
		rs->sbuf_size = def_wmem;
		rs->rbuf_size = def_mem;
		rs->sq_inline = def_inline;
		rs->sq_size = def_sqsize;
		rs->rq_size = def_rqsize;
		if (type == SOCK_STREAM) {
			rs->ctrl_max_seqno = RS_QP_CTRL_SIZE;
			rs->target_iomap_size = def_iomap_size;
		}
	}
	fastlock_init(&rs->slock);
	fastlock_init(&rs->rlock);
	fastlock_init(&rs->cq_lock);
	fastlock_init(&rs->cq_wait_lock);
	fastlock_init(&rs->map_lock);
	dlist_init(&rs->iomap_list);
	dlist_init(&rs->iomap_queue);
	return rs;
}

static int rs_set_nonblocking(struct rsocket *rs, int arg)
{
	struct ds_qp *qp;
	int ret = 0;

	if (rs->type == SOCK_STREAM) {
		if (rs->cm_id->recv_cq_channel)
			ret = fcntl(rs->cm_id->recv_cq_channel->fd, F_SETFL, arg);

		if (rs->state == rs_listening)
			ret = fcntl(rs->accept_queue[0], F_SETFL, arg);// 将socketpair() 创建的 socket 0 设为非阻塞
		else if (!ret && rs->state < rs_connected)
			ret = fcntl(rs->cm_id->channel->fd, F_SETFL, arg);
	} else {
		ret = fcntl(rs->epfd, F_SETFL, arg);
		if (!ret && rs->qp_list) {
			qp = rs->qp_list;
			do {
				ret = fcntl(qp->cm_id->recv_cq_channel->fd,
					    F_SETFL, arg);
				qp = ds_next_qp(qp);
			} while (qp != rs->qp_list && !ret);
		}
	}

	return ret;
}

/*
设置 send queue 和 recv queue 的大小
确保不超过设备支持的最大queue size 及 RS_QP_MAX_SIZE，且不小于 RS_QP_MIN_SIZE
*/
static void rs_set_qp_size(struct rsocket *rs)
{
	uint16_t max_size;

	max_size = min(ucma_max_qpsize(rs->cm_id), RS_QP_MAX_SIZE);// max size 设为 设备本身的max qp size 与 RS_QP_MAX_SIZE 中较小的值，保证不超过两者任一
// 下面将 rs的send queue 和recv queue 大小设为max size 与min size 之间的值
	if (rs->sq_size > max_size)
		rs->sq_size = max_size;
	else if (rs->sq_size < RS_QP_MIN_SIZE)
		rs->sq_size = RS_QP_MIN_SIZE;

	if (rs->rq_size > max_size)
		rs->rq_size = max_size;
	else if (rs->rq_size < RS_QP_MIN_SIZE)
		rs->rq_size = RS_QP_MIN_SIZE;
}

static void ds_set_qp_size(struct rsocket *rs)
{
	uint16_t max_size;

	max_size = min(ucma_max_qpsize(NULL), RS_QP_MAX_SIZE);

	if (rs->sq_size > max_size)
		rs->sq_size = max_size;
	if (rs->rq_size > max_size)
		rs->rq_size = max_size;

	if (rs->rq_size > (rs->rbuf_size / RS_SNDLOWAT))
		rs->rq_size = rs->rbuf_size / RS_SNDLOWAT;
	else
		rs->rbuf_size = rs->rq_size * RS_SNDLOWAT;

	if (rs->sq_size > (rs->sbuf_size / RS_SNDLOWAT))
		rs->sq_size = rs->sbuf_size / RS_SNDLOWAT;
	else
		rs->sbuf_size = rs->sq_size * RS_SNDLOWAT;
}

/*
 * 初始化缓存区
 * 共需要注册三个内存缓冲区
 * 1. sbuf：send buffer ，发送数据时首先将数据存入send buffer，执行rdma write/send 时，将sbuf 的地址作为参数传给 ibv_post_send()
 * 			sbuf 对应的 memroy region 为 smr，只需要local write 权限，只提供给本机进行写入
 * 2. target_buffer_list
 * 			target_mr
 * 3. rbuf：recv buffer，用来接收数据，
 */
static int rs_init_bufs(struct rsocket *rs)
{
	uint32_t total_rbuf_size, total_sbuf_size;
	size_t len;

	rs->rmsg = calloc(rs->rq_size + 1, sizeof(*rs->rmsg));//在内存中动态地分配 rs->rq_size + 1 个长度为 sizeof(*rs->rmsg) 的连续空间，并将每一个字节都初始化为 0
	if (!rs->rmsg)
		return ERR(ENOMEM);

	total_sbuf_size = rs->sbuf_size;// 获取 rs 的 send buffer 大小，并赋值给total_sbuf_size
	if (rs->sq_inline < RS_MAX_CTRL_MSG)// TODO：若sql_inline 小于RS_MAX_CTRL_MSG，表示不使用rdma send 发送控制数据，使用rdma write 发送控制数据需要 total_sbuf_size 中增加ctrl 消息长度
		total_sbuf_size += RS_MAX_CTRL_MSG * RS_QP_CTRL_SIZE;
	rs->sbuf = calloc(total_sbuf_size, 1);// 申请send buffer 内存
	if (!rs->sbuf)
		return ERR(ENOMEM);

	rs->smr = rdma_reg_msgs(rs->cm_id, rs->sbuf, total_sbuf_size);// 注册send buffer 对应的send memory region，起始地址为 rs->sbuf，大小为 total_sbuf_size，权限为IBV_ACCESS_LOCAL_WRITE
	if (!rs->smr)
		return -1;

	len = sizeof(*rs->target_sgl) * RS_SGL_SIZE +
	      sizeof(*rs->target_iomap) * rs->target_iomap_size;// 若有iomap，需额外处理。TODO：iomap逻辑尚不清楚
	rs->target_buffer_list = malloc(len);// 申请send 对应的target buffer 内存
	if (!rs->target_buffer_list)
		return ERR(ENOMEM);

	rs->target_mr = rdma_reg_write(rs->cm_id, rs->target_buffer_list, len);// 注册send 对应target buffer 的memory region，权限为local write 和remote write
	if (!rs->target_mr)
		return -1;

	memset(rs->target_buffer_list, 0, len);
	rs->target_sgl = rs->target_buffer_list;// 将target buffer list 起始地址赋值给 target_sgl
	if (rs->target_iomap_size)
		rs->target_iomap = (struct rs_iomap *) (rs->target_sgl + RS_SGL_SIZE);

	total_rbuf_size = rs->rbuf_size;// 获取 rs->rbuf_size 的值，并赋值给 total_rbuf_size
	if (rs->opts & RS_OPT_MSG_SEND)
		total_rbuf_size += rs->rq_size * RS_MSG_SIZE;// 若操作类型为 MSG SEND，则在 rs->rbuf_size 基础上将 total_rbuf_size 加上要发送的单个MSG 大小MSG_SIZE * 要发送的MSG 个数rq_size
	rs->rbuf = calloc(total_rbuf_size, 1);// 申请 total_rbuf_size 字节的内存空间初始化每字节为0，并将起始地址保存于 rs->rbuf
	if (!rs->rbuf)
		return ERR(ENOMEM);

	rs->rmr = rdma_reg_write(rs->cm_id, rs->rbuf, total_rbuf_size);// 注册recv 对应的memory region，权限为local write 和remote write
	if (!rs->rmr)
		return -1;

	rs->ssgl[0].addr = rs->ssgl[1].addr = (uintptr_t) rs->sbuf;// 将rs->sbuf 赋值给 rs 的send sgl[1].addr ，也赋值给rs 的 send sgl[0].addr
	rs->sbuf_bytes_avail = rs->sbuf_size;// 将rs->sbuf_size 赋值给 rs send buffer bytes available ，表示rs send buffer 可用字节为sbuf_size 个，可用字节与send buffer 大小一致
	rs->ssgl[0].lkey = rs->ssgl[1].lkey = rs->smr->lkey;// send sgl[0].local key 与 send sgl[1].local key 都设为send mr local key

	rs->rbuf_free_offset = rs->rbuf_size >> 1; // recv buffer free offset 初始化为rbuf_size 的一半
	rs->rbuf_bytes_avail = rs->rbuf_size >> 1;// rbuf 可用字节数同样初始化为rbuf_size 的一半
	rs->sqe_avail = rs->sq_size - rs->ctrl_max_seqno;// 可用的send queue element 初始化为 send queue size 减去 rs->ctrl_max_seqno
	rs->rseq_comp = rs->rq_size >> 1;// recv seqence completion ，初始值为 rq_size 的一半，当rseq_no 的值达到rseq_comp 时，需要更新credits，并增大rseq_comp
	return 0;
}

static int ds_init_bufs(struct ds_qp *qp)
{
	qp->rbuf = calloc(qp->rs->rbuf_size + sizeof(struct ibv_grh), 1);
	if (!qp->rbuf)
		return ERR(ENOMEM);

	qp->smr = rdma_reg_msgs(qp->cm_id, qp->rs->sbuf, qp->rs->sbuf_size);
	if (!qp->smr)
		return -1;

	qp->rmr = rdma_reg_msgs(qp->cm_id, qp->rbuf, qp->rs->rbuf_size +
						     sizeof(struct ibv_grh));
	if (!qp->rmr)
		return -1;

	return 0;
}

/*
 * If a user is waiting on a datagram rsocket through poll or select, then
 * we need the first completion to generate an event on the related epoll fd
 * in order to signal the user.  We arm the CQ on creation for this purpose
 * 
 * 显示创建cm_id->recv_cq_channel
 */
static int rs_create_cq(struct rsocket *rs, struct rdma_cm_id *cm_id)
{
	cm_id->recv_cq_channel = ibv_create_comp_channel(cm_id->verbs);
	if (!cm_id->recv_cq_channel)
		return -1;

	cm_id->recv_cq = ibv_create_cq(cm_id->verbs, rs->sq_size + rs->rq_size,
				       cm_id, cm_id->recv_cq_channel, 0);
	if (!cm_id->recv_cq)
		goto err1;

	if (rs->fd_flags & O_NONBLOCK) {
		if (set_fd_nonblock(cm_id->recv_cq_channel->fd, true))
			goto err2;
	}

	ibv_req_notify_cq(cm_id->recv_cq, 0);
	cm_id->send_cq_channel = cm_id->recv_cq_channel;
	cm_id->send_cq = cm_id->recv_cq;
	return 0;

err2:
	ibv_destroy_cq(cm_id->recv_cq);
	cm_id->recv_cq = NULL;
err1:
	ibv_destroy_comp_channel(cm_id->recv_cq_channel);
	cm_id->recv_cq_channel = NULL;
	return -1;
}

static inline int rs_post_recv(struct rsocket *rs)
{
	struct ibv_recv_wr wr, *bad;
	struct ibv_sge sge;

	wr.next = NULL;
	if (!(rs->opts & RS_OPT_MSG_SEND)) {// rdma write 相关处理
		wr.wr_id = rs_recv_wr_id(0);// recv wr 的64 位最高位设为1，低63位都为0
		wr.sg_list = NULL;
		wr.num_sge = 0;
	} else {// iwarp rdma send
		wr.wr_id = rs_recv_wr_id(rs->rbuf_msg_index);// 将 recv buffer 位于recv queue 的序号 index 作为work request 的 id，且将其转为64 位无符号整型，最高位设为1 表示为recv wr
		sge.addr = (uintptr_t) rs->rbuf + rs->rbuf_size +
			   (rs->rbuf_msg_index * RS_MSG_SIZE);// recv buffer 起始位置 + 每个recv buffer 大小 + 
		sge.length = RS_MSG_SIZE;
		sge.lkey = rs->rmr->lkey;

		wr.sg_list = &sge;
		wr.num_sge = 1;
		if(++rs->rbuf_msg_index == rs->rq_size)
			rs->rbuf_msg_index = 0;
	}

	return rdma_seterrno(ibv_post_recv(rs->cm_id->qp, &wr, &bad));
}

static inline int ds_post_recv(struct rsocket *rs, struct ds_qp *qp, uint32_t offset)
{
	struct ibv_recv_wr wr, *bad;
	struct ibv_sge sge[2];

	sge[0].addr = (uintptr_t) qp->rbuf + rs->rbuf_size;
	sge[0].length = sizeof(struct ibv_grh);
	sge[0].lkey = qp->rmr->lkey;
	sge[1].addr = (uintptr_t) qp->rbuf + offset;
	sge[1].length = RS_SNDLOWAT;
	sge[1].lkey = qp->rmr->lkey;

	wr.wr_id = rs_recv_wr_id(offset);// 将32 位offset 扩展为64位，最高位设为1 表示wr 是recv wr
	wr.next = NULL;
	wr.sg_list = sge;
	wr.num_sge = 2;

	return rdma_seterrno(ibv_post_recv(qp->cm_id->qp, &wr, &bad));
}

static int rs_create_ep(struct rsocket *rs)
{
	struct ibv_qp_init_attr qp_attr;
	int i, ret;

	rs_set_qp_size(rs);// 设置rs send queue 及recv queue 的size 不超过最大最小值范围
	if (rs->cm_id->verbs->device->transport_type == IBV_TRANSPORT_IWARP)// 若传输协议为iwarp ，则使用rs->opts 标志将rdma write 改为rdma send
		rs->opts |= RS_OPT_MSG_SEND;
	ret = rs_create_cq(rs, rs->cm_id);
	if (ret)
		return ret;

	memset(&qp_attr, 0, sizeof qp_attr);
	qp_attr.qp_context = rs;
	qp_attr.send_cq = rs->cm_id->send_cq;
	qp_attr.recv_cq = rs->cm_id->recv_cq;
	qp_attr.qp_type = IBV_QPT_RC;
	qp_attr.sq_sig_all = 1;
	qp_attr.cap.max_send_wr = rs->sq_size;
	qp_attr.cap.max_recv_wr = rs->rq_size;
	qp_attr.cap.max_send_sge = 2;
	qp_attr.cap.max_recv_sge = 1;
	qp_attr.cap.max_inline_data = rs->sq_inline;

	ret = rdma_create_qp(rs->cm_id, NULL, &qp_attr);
	if (ret)
		return ret;

	rs->sq_inline = qp_attr.cap.max_inline_data;
	if ((rs->opts & RS_OPT_MSG_SEND) && (rs->sq_inline < RS_MSG_SIZE))// 使用rdma send 但 sq_inline 小于单个msg 的大小，则无法完成msg 发送
		return ERR(ENOTSUP);

	ret = rs_init_bufs(rs);// 初始化send/recv buffer，send/recv mr 等
	if (ret)
		return ret;

	for (i = 0; i < rs->rq_size; i++) {// 提交多个recv wr，数量与recv queue size 相同
		ret = rs_post_recv(rs);
		if (ret)
			return ret;
	}
	return 0;
}

static void rs_release_iomap_mr(struct rs_iomap_mr *iomr)
{
	if (atomic_fetch_sub(&iomr->refcnt, 1) != 1)
		return;

	dlist_remove(&iomr->entry);
	ibv_dereg_mr(iomr->mr);
	if (iomr->index >= 0)
		iomr->mr = NULL;
	else
		free(iomr);
}

static void rs_free_iomappings(struct rsocket *rs)
{
	struct rs_iomap_mr *iomr;

	while (!dlist_empty(&rs->iomap_list)) {
		iomr = container_of(rs->iomap_list.next,
				    struct rs_iomap_mr, entry);
		riounmap(rs->index, iomr->mr->addr, iomr->mr->length);
	}
	while (!dlist_empty(&rs->iomap_queue)) {
		iomr = container_of(rs->iomap_queue.next,
				    struct rs_iomap_mr, entry);
		riounmap(rs->index, iomr->mr->addr, iomr->mr->length);
	}
}

static void ds_free_qp(struct ds_qp *qp)
{
	if (qp->smr)
		rdma_dereg_mr(qp->smr);

	if (qp->rbuf) {
		if (qp->rmr)
			rdma_dereg_mr(qp->rmr);
		free(qp->rbuf);
	}

	if (qp->cm_id) {
		if (qp->cm_id->qp) {
			tdelete(&qp->dest.addr, &qp->rs->dest_map, ds_compare_addr);
			epoll_ctl(qp->rs->epfd, EPOLL_CTL_DEL,
				  qp->cm_id->recv_cq_channel->fd, NULL);
			rdma_destroy_qp(qp->cm_id);
		}
		rdma_destroy_id(qp->cm_id);
	}

	free(qp);
}

static void ds_free(struct rsocket *rs)
{
	struct ds_qp *qp;

	if (rs->udp_sock >= 0)
		close(rs->udp_sock);

	if (rs->index >= 0)
		rs_remove(rs);

	if (rs->dmsg)
		free(rs->dmsg);

	while ((qp = rs->qp_list)) {
		ds_remove_qp(rs, qp);
		ds_free_qp(qp);
	}

	if (rs->epfd >= 0)
		close(rs->epfd);

	if (rs->sbuf)
		free(rs->sbuf);

	tdestroy(rs->dest_map, free);
	fastlock_destroy(&rs->map_lock);
	fastlock_destroy(&rs->cq_wait_lock);
	fastlock_destroy(&rs->cq_lock);
	fastlock_destroy(&rs->rlock);
	fastlock_destroy(&rs->slock);
	free(rs);
}

static void rs_free(struct rsocket *rs)
{
	if (rs->type == SOCK_DGRAM) {
		ds_free(rs);
		return;
	}

	if (rs->rmsg)
		free(rs->rmsg);

	if (rs->sbuf) {
		if (rs->smr)
			rdma_dereg_mr(rs->smr);
		free(rs->sbuf);
	}

	if (rs->rbuf) {
		if (rs->rmr)
			rdma_dereg_mr(rs->rmr);
		free(rs->rbuf);
	}

	if (rs->target_buffer_list) {
		if (rs->target_mr)
			rdma_dereg_mr(rs->target_mr);
		free(rs->target_buffer_list);
	}

	if (rs->index >= 0)
		rs_remove(rs);

	if (rs->cm_id) {
		rs_free_iomappings(rs);
		if (rs->cm_id->qp) {
			ibv_ack_cq_events(rs->cm_id->recv_cq, rs->unack_cqe);
			rdma_destroy_qp(rs->cm_id);
		}
		rdma_destroy_id(rs->cm_id);
	}

	if (rs->accept_queue[0] > 0 || rs->accept_queue[1] > 0) {
		close(rs->accept_queue[0]);
		close(rs->accept_queue[1]);
	}

	fastlock_destroy(&rs->map_lock);
	fastlock_destroy(&rs->cq_wait_lock);
	fastlock_destroy(&rs->cq_lock);
	fastlock_destroy(&rs->rlock);
	fastlock_destroy(&rs->slock);
	free(rs);
}

/*
返回值为消息中头部连接信息之后的数据起始位置相对于消息起始位置的偏移量
*/
static size_t rs_conn_data_offset(struct rsocket *rs)
{
	return (rs->cm_id->route.addr.src_addr.sa_family == AF_IB) ?
		sizeof(struct ib_connect_hdr) : 0;
}

static void rs_format_conn_data(struct rsocket *rs, struct rs_conn_data *conn)
{
	conn->version = 1;
	conn->flags = RS_CONN_FLAG_IOMAP |
		      (rs_host_is_net() ? RS_CONN_FLAG_NET : 0);
	conn->credits = htobe16(rs->rq_size);// *注意：credits 值为rs recv queue size
	memset(conn->reserved, 0, sizeof conn->reserved);
	conn->target_iomap_size = (uint8_t) rs_value_to_scale(rs->target_iomap_size, 8);

	conn->target_sgl.addr = (__force uint64_t)htobe64((uintptr_t) rs->target_sgl);		// 目标sgl 地址 即为rs 记录的target_sgl
	conn->target_sgl.length = (__force uint32_t)htobe32(RS_SGL_SIZE);					// 目标sgl 长度为2
	conn->target_sgl.key = (__force uint32_t)htobe32(rs->target_mr->rkey);				// 目标mr

	conn->data_buf.addr = (__force uint64_t)htobe64((uintptr_t) rs->rbuf);				// 将本地的 receive buffer 地址传递给对端
	conn->data_buf.length = (__force uint32_t)htobe32(rs->rbuf_size >> 1);				// receive buffer 长度赋值为 recv buffer size 的一半，即对端一次只会写满rbuf 的一半
	conn->data_buf.key = (__force uint32_t)htobe32(rs->rmr->rkey);						// receive buffer 对应的mr 的remote key，供对端执行 rdma write 操作
}

static void rs_save_conn_data(struct rsocket *rs, struct rs_conn_data *conn)
{
	rs->remote_sgl.addr = be64toh((__force __be64)conn->target_sgl.addr);// 将对端传递的target sgl 信息存储到 remote sgl 中
	rs->remote_sgl.length = be32toh((__force __be32)conn->target_sgl.length);
	rs->remote_sgl.key = be32toh((__force __be32)conn->target_sgl.key);
	rs->remote_sge = 1;
	if ((rs_host_is_net() && !(conn->flags & RS_CONN_FLAG_NET)) ||
	    (!rs_host_is_net() && (conn->flags & RS_CONN_FLAG_NET)))
		rs->opts = RS_OPT_SWAP_SGL;// 根据对端传递的flags 提供的是网络序且本机主机序与网络序不同，或者对端传递来的flags 表明不是网络序且本机主机序与网络序相同，将rs->opts 设为SWAP SGL表示需要进行网络序主机序转换

	if (conn->flags & RS_CONN_FLAG_IOMAP) {
		rs->remote_iomap.addr = rs->remote_sgl.addr +
					sizeof(rs->remote_sgl) * rs->remote_sgl.length;
		rs->remote_iomap.length = rs_scale_to_value(conn->target_iomap_size, 8);
		rs->remote_iomap.key = rs->remote_sgl.key;
	}
// 因为建立连接时，target_sgl 是第一次被使用，因此直接将对端发送来的recv buf 相关信息存入target_sgl 索引为0 的第一个位置
	rs->target_sgl[0].addr = be64toh((__force __be64)conn->data_buf.addr);// 将对端的recv buffer 存储到本端的target sgl[0] 中
	rs->target_sgl[0].length = be32toh((__force __be32)conn->data_buf.length);
	rs->target_sgl[0].key = be32toh((__force __be32)conn->data_buf.key);

	rs->sseq_comp = be16toh(conn->credits);// send sequence completion 设为对端传递来的值，根据rs_format_conn_data()，此值是对端的rbuf_size 的一半
}

static int ds_init(struct rsocket *rs, int domain)
{
	rs->udp_sock = socket(domain, SOCK_DGRAM, 0);
	if (rs->udp_sock < 0)
		return rs->udp_sock;

	rs->epfd = epoll_create(2);
	if (rs->epfd < 0)
		return rs->epfd;

	return 0;
}

static int ds_init_ep(struct rsocket *rs)
{
	struct ds_smsg *msg;
	int i, ret;

	ds_set_qp_size(rs);

	rs->sbuf = calloc(rs->sq_size, RS_SNDLOWAT);
	if (!rs->sbuf)
		return ERR(ENOMEM);

	rs->dmsg = calloc(rs->rq_size + 1, sizeof(*rs->dmsg));
	if (!rs->dmsg)
		return ERR(ENOMEM);

	rs->sqe_avail = rs->sq_size;
	rs->rqe_avail = rs->rq_size;

	rs->smsg_free = (struct ds_smsg *) rs->sbuf;
	msg = rs->smsg_free;
	for (i = 0; i < rs->sq_size - 1; i++) {
		msg->next = (void *) msg + RS_SNDLOWAT;
		msg = msg->next;
	}
	msg->next = NULL;

	ret = rs_notify_svc(&udp_svc, rs, RS_SVC_ADD_DGRAM);
	if (ret)
		return ret;

	rs->state = rs_readable | rs_writable;
	return 0;
}

int rsocket(int domain, int type, int protocol)
{
	struct rsocket *rs;
	int index, ret;

	if ((domain != AF_INET && domain != AF_INET6 && domain != AF_IB) ||
	    ((type != SOCK_STREAM) && (type != SOCK_DGRAM)) ||
	    (type == SOCK_STREAM && protocol && protocol != IPPROTO_TCP) ||
	    (type == SOCK_DGRAM && protocol && protocol != IPPROTO_UDP))
		return ERR(ENOTSUP);

	rs_configure();// TODO
	rs = rs_alloc(NULL, type); // 从正在监听的socket 继承一系列属性
	if (!rs)
		return ERR(ENOMEM);

	if (type == SOCK_STREAM) {// tcp 类型
		ret = rdma_create_id(NULL, &rs->cm_id, rs, RDMA_PS_TCP);// 创建cm_id，赋值给 rs->cm_id，并将rs 设为cm_id 的context
		if (ret)
			goto err;

		rs->cm_id->route.addr.src_addr.sa_family = domain;
		index = rs->cm_id->channel->fd; // 将cm_id -> event channel ->fd 赋值给 index
	} else {
		ret = ds_init(rs, domain);
		if (ret)
			goto err;

		index = rs->udp_sock;
	}

	ret = rs_insert(rs, index);// 将 rs->cm_id->channel->fd 在全局idm 中的索引值 赋值给 rs->index，将rs 存入index_map 中
	if (ret < 0)
		goto err;

	return rs->index;// rs->index 即为上述index，也即 cm_id->channel->fd

err:
	rs_free(rs);
	return ret;
}

int rbind(int socket, const struct sockaddr *addr, socklen_t addrlen)
{
	struct rsocket *rs;
	int ret;

	rs = idm_lookup(&idm, socket);// 根据fd 找到对应rsocket 实例
	if (!rs)
		return ERR(EBADF);
	if (rs->type == SOCK_STREAM) {// tcp bind
		ret = rdma_bind_addr(rs->cm_id, (struct sockaddr *) addr);// 完成cm_id 与 ip 地址的绑定
		if (!ret)
			rs->state = rs_bound;
	} else {
		if (rs->state == rs_init) {
			ret = ds_init_ep(rs);
			if (ret)
				return ret;
		}
		ret = bind(rs->udp_sock, addr, addrlen);
	}
	return ret;
}

int rlisten(int socket, int backlog)
{
	struct rsocket *rs;
	int ret;

	rs = idm_lookup(&idm, socket);
	if (!rs)
		return ERR(EBADF);

	if (rs->state == rs_listening)
		return 0;

	ret = rdma_listen(rs->cm_id, backlog);
	if (ret)
		return ret;

	ret = socketpair(AF_UNIX, SOCK_STREAM, 0, rs->accept_queue);// socketpair()函数用于创建一对无名的、相互连接的socket；用户使用socket()系统调用编写应用程序时，通过一个数字来表示一个socket，所有的操作都在该数字上进行，这个数字称为套接字描述符。在系统调用 的实现函数里，这个数字就会被映射成一个表示socket的结构体，该结构体保存了该socket的所有属性和数据。
	if (ret)
		return ret;

	if (rs->fd_flags & O_NONBLOCK) {
		ret = set_fd_nonblock(rs->accept_queue[0], true);// 将socket 对的第一个socket 设为非阻塞
		if (ret)
			return ret;
	}

	ret = set_fd_nonblock(rs->cm_id->channel->fd, true);
	if (ret)
		return ret;

	ret = rs_notify_svc(&listen_svc, rs, RS_SVC_ADD_CM);// 创建子线程，对rs fd
	if (ret)
		return ret;

	rs->state = rs_listening;
	return 0;
}

/* Accepting new connection requests is currently a blocking operation */
static void rs_accept(struct rsocket *rs)
{
	struct rsocket *new_rs;
	struct rdma_conn_param param;
	struct rs_conn_data *creq, cresp;
	struct rdma_cm_id *cm_id;
	int ret;

	ret = rdma_get_request(rs->cm_id, &cm_id);// 创建新的qp，并获得对应cm_id，cm_id 的event 中包括了client 连接请求传递来的private_data
	if (ret)
		return;

	new_rs = rs_alloc(rs, rs->type);// server 从原rs 继承一些连接size参数，并创建新的rs 实例
	if (!new_rs)
		goto err;
	new_rs->cm_id = cm_id;

	ret = rs_insert(new_rs, new_rs->cm_id->channel->fd);
	if (ret < 0)
		goto err;

	creq = (struct rs_conn_data *)
	       (new_rs->cm_id->event->param.conn.private_data + rs_conn_data_offset(rs));// 将client 发送来的private_data 封装为一个rs_conn_data 数据
	if (creq->version != 1)
		goto err;

	ret = rs_create_ep(new_rs);// server创建处理client 请求的新的endpoint，初始化rbuf、sbuf 和target_buffer_list
	if (ret)
		goto err;

	rs_save_conn_data(new_rs, creq);// 根据client 发送来的private_data ，更新new_rs 中remote_sgl 和target_sgl 相关信息
	// agent执行完 rs_save_conn_data() 之后
	// agent->target_sgl[0].addr = client->rbuf
	// agent->remote_sgl.addr = client->target_sgl
	param = new_rs->cm_id->event->param.conn;
	rs_format_conn_data(new_rs, &cresp);// 将agent 的buffer 信息发送给client
	param.private_data = &cresp;
	param.private_data_len = sizeof cresp;
	//printf("rsocket debug: sizeof cresp %ld\n",sizeof cresp);
	//printf("rsocket debug: before rdma_accept(new_rs->cm_id, &param); fcntl %u, O_NONBLOCK %u\n",fcntl(new_rs->cm_id->channel->fd,F_GETFL),O_NONBLOCK),;
	ret = rdma_accept(new_rs->cm_id, &param);
	//printf("rsocket debug: fcntl %u\n",fcntl(new_rs->cm_id->channel->fd,F_GETFL));
// rdma_accept 执行之后 param 的private_data 被写入到 new_rs->cm_id->channel->fd 中
	if (!ret)
		new_rs->state = rs_connect_rdwr;
	else if (errno == EAGAIN || errno == EWOULDBLOCK)
		new_rs->state = rs_accepting;
	else
		goto err;

	write_all(rs->accept_queue[1], &new_rs, sizeof(new_rs));// 向创建的socket 1 写入数据
	return;

err:
	rdma_reject(cm_id, NULL, 0);
	if (new_rs)
		rs_free(new_rs);
}
// raccept 并未执行创建socket，相关socket 已经在rlisten 时通过 rs_notify_svc 创建了子线程，用于执行rs_accept 操作
// raccept 只是从
int raccept(int socket, struct sockaddr *addr, socklen_t *addrlen)
{
	struct rsocket *rs, *new_rs;
	int ret;

	rs = idm_lookup(&idm, socket);
	if (!rs)
		return ERR(EBADF);

	if (rs->state != rs_listening)
		return ERR(EBADF);

	ret = read(rs->accept_queue[0], &new_rs, sizeof(new_rs));// 从创建的socket 0 中读取数据
	if (ret != sizeof(new_rs))
		return ret;

	if (addr && addrlen)
		rgetpeername(new_rs->index, addr, addrlen);
	/* The app can still drive the CM state on failure */
	int save_errno = errno;
	rs_notify_svc(&accept_svc, new_rs, RS_SVC_ADD_CM);
	errno = save_errno;
	return new_rs->index;
}

static int rs_do_connect(struct rsocket *rs)
{
	struct rdma_conn_param param;
	struct rs_conn_private_data cdata;
	struct rs_conn_data *creq, *cresp;
	int to, ret;

	fastlock_acquire(&rs->slock);
	switch (rs->state) {
	case rs_init:
	case rs_bound:
resolve_addr:
		to = 1000 << rs->retries++;
		ret = rdma_resolve_addr(rs->cm_id, NULL,
					&rs->cm_id->route.addr.dst_addr, to);// 执行完rdma_resolve_addr 后，cm_id 根据路由表查到可到达目标地址的本地rdma 设备确定完成绑定
		if (!ret)
			goto resolve_route;// 执行完rdma_resolve_addr 后，转向resolve route
		if (errno == EAGAIN || errno == EWOULDBLOCK)
			rs->state = rs_resolving_addr;
		break;
	case rs_resolving_addr:
		ret = ucma_complete(rs->cm_id);
		if (ret) {
			if (errno == ETIMEDOUT && rs->retries <= RS_CONN_RETRIES)
				goto resolve_addr;
			break;
		}

		rs->retries = 0;
resolve_route:
		to = 1000 << rs->retries++;
		if (rs->optval) {
			ret = rdma_set_option(rs->cm_id,  RDMA_OPTION_IB,
					      RDMA_OPTION_IB_PATH, rs->optval,
					      rs->optlen);
			free(rs->optval);
			rs->optval = NULL;
			if (!ret) {
				rs->state = rs_resolving_route;
				goto resolving_route;
			}
		} else {
			ret = rdma_resolve_route(rs->cm_id, to);// 获取到目标addr 的路径， the call obtains a path record 供新建的connection 使用
			if (!ret)
				goto do_connect;// 完成resolv route，转向 do_connect
		}
		if (errno == EAGAIN || errno == EWOULDBLOCK)
			rs->state = rs_resolving_route;
		break;
	case rs_resolving_route:
resolving_route:
		ret = ucma_complete(rs->cm_id);
		if (ret) {
			if (errno == ETIMEDOUT && rs->retries <= RS_CONN_RETRIES)
				goto resolve_route;
			break;
		}
do_connect:
		ret = rs_create_ep(rs);// 创建endpoint，包括创建cq，初始化buffer 及mr 等 ，并提交rs->rbuf_size 个recv wr
		if (ret)
			break;

		memset(&param, 0, sizeof param);
		creq = (void *) &cdata + rs_conn_data_offset(rs);// creq 的值为局部变量cdata 的地址加上消息头部连接信息之后数据部分的偏移量，即消息中conn data数据的起始地址
		rs_format_conn_data(rs, creq);// 对要发送消息中的rs连接信息（sgl.addr,sgl_length,sgl rkey）部分复制给creq ，同时完成 主机序->网络序的转换
		// 下面从creq 中获取private_data，赋值给param.private_data
		param.private_data = (void *) creq - rs_conn_data_offset(rs);// 由于上面将creq 加上conn data偏移量，creq指向了conn data 起始地址，将此地址减去偏移量，再次得到发送消息的起始地址
		param.private_data_len = sizeof(*creq) + rs_conn_data_offset(rs);// *creq 得到的是conn data，其长度加上消息头部长度即为整个private data 长度
		param.flow_control = 1;
		param.retry_count = 7;
		param.rnr_retry_count = 7;
		/* work-around: iWarp issues RDMA read during connection */
		if (rs->opts & RS_OPT_MSG_SEND)
			param.initiator_depth = 1;
		rs->retries = 0;

		ret = rdma_connect(rs->cm_id, &param);// 执行rdma connect，若成功返回0
		// rdma_connect 执行之后 param 的private_data 被写入到rs->cm_id->channel->fd 中
		if (!ret)
			goto connected;// 执行rdma connect 成功，转向connected
		if (errno == EAGAIN || errno == EWOULDBLOCK)
			rs->state = rs_connecting;
		break;
	case rs_connecting:
		ret = ucma_complete(rs->cm_id);
		if (ret)
			break;
connected:
		cresp = (struct rs_conn_data *) rs->cm_id->event->param.conn.private_data;// 获取对端传递来的private data 指针
		if (cresp->version != 1) {
			ret = ERR(ENOTSUP);
			break;
		}

		rs_save_conn_data(rs, cresp);// 保存对端传递来的remote mr，rkey 等信息
		rs->state = rs_connect_rdwr;
		break;
	case rs_accepting:
		if (!(rs->fd_flags & O_NONBLOCK))
			set_fd_nonblock(rs->cm_id->channel->fd, true);

		ret = ucma_complete(rs->cm_id);
		if (ret)
			break;

		rs->state = rs_connect_rdwr;
		break;
	case rs_connect_error:
	case rs_disconnected:
	case rs_error:
		ret = ERR(ENOTCONN);
		goto unlock;
	default:
		ret = (rs->state & rs_connected) ? 0 : ERR(EINVAL);
		goto unlock;
	}

	if (ret) {
		if (errno == EAGAIN || errno == EWOULDBLOCK) {
			errno = EINPROGRESS;
		} else {
			rs->state = rs_connect_error;
			rs->err = errno;
		}
	}
unlock:
	fastlock_release(&rs->slock);
	return ret;
}

static int rs_any_addr(const union socket_addr *addr)
{
	if (addr->sa.sa_family == AF_INET) {
		return (addr->sin.sin_addr.s_addr == htobe32(INADDR_ANY) ||
			addr->sin.sin_addr.s_addr == htobe32(INADDR_LOOPBACK));
	} else {
		return (!memcmp(&addr->sin6.sin6_addr, &in6addr_any, 16) ||
			!memcmp(&addr->sin6.sin6_addr, &in6addr_loopback, 16));
	}
}

static int ds_get_src_addr(struct rsocket *rs,
			   const struct sockaddr *dest_addr, socklen_t dest_len,
			   union socket_addr *src_addr, socklen_t *src_len)
{
	int sock, ret;
	__be16 port;

	*src_len = sizeof(*src_addr);
	ret = getsockname(rs->udp_sock, &src_addr->sa, src_len);
	if (ret || !rs_any_addr(src_addr))
		return ret;

	port = src_addr->sin.sin_port;
	sock = socket(dest_addr->sa_family, SOCK_DGRAM, 0);
	if (sock < 0)
		return sock;

	ret = connect(sock, dest_addr, dest_len);
	if (ret)
		goto out;

	*src_len = sizeof(*src_addr);
	ret = getsockname(sock, &src_addr->sa, src_len);
	src_addr->sin.sin_port = port;
out:
	close(sock);
	return ret;
}

static void ds_format_hdr(struct ds_header *hdr, union socket_addr *addr)
{
	if (addr->sa.sa_family == AF_INET) {
		hdr->version = 4;
		hdr->length = DS_IPV4_HDR_LEN;
		hdr->port = addr->sin.sin_port;
		hdr->addr.ipv4 = addr->sin.sin_addr.s_addr;
	} else {
		hdr->version = 6;
		hdr->length = DS_IPV6_HDR_LEN;
		hdr->port = addr->sin6.sin6_port;
		hdr->addr.ipv6.flowinfo= addr->sin6.sin6_flowinfo;
		memcpy(&hdr->addr.ipv6.addr, &addr->sin6.sin6_addr, 16);
	}
}

static int ds_add_qp_dest(struct ds_qp *qp, union socket_addr *addr,
			  socklen_t addrlen)
{
	struct ibv_port_attr port_attr;
	struct ibv_ah_attr attr;
	int ret;

	memcpy(&qp->dest.addr, addr, addrlen);
	qp->dest.qp = qp;
	qp->dest.qpn = qp->cm_id->qp->qp_num;

	ret = ibv_query_port(qp->cm_id->verbs, qp->cm_id->port_num, &port_attr);
	if (ret)
		return ret;

	memset(&attr, 0, sizeof attr);
	attr.dlid = port_attr.lid;
	attr.port_num = qp->cm_id->port_num;
	qp->dest.ah = ibv_create_ah(qp->cm_id->pd, &attr);
	if (!qp->dest.ah)
		return ERR(ENOMEM);

	tsearch(&qp->dest.addr, &qp->rs->dest_map, ds_compare_addr);
	return 0;
}

static int ds_create_qp(struct rsocket *rs, union socket_addr *src_addr,
			socklen_t addrlen, struct ds_qp **new_qp)
{
	struct ds_qp *qp;
	struct ibv_qp_init_attr qp_attr;
	struct epoll_event event;
	int i, ret;

	qp = calloc(1, sizeof(*qp));
	if (!qp)
		return ERR(ENOMEM);

	qp->rs = rs;
	ret = rdma_create_id(NULL, &qp->cm_id, qp, RDMA_PS_UDP);
	if (ret)
		goto err;

	ds_format_hdr(&qp->hdr, src_addr);
	ret = rdma_bind_addr(qp->cm_id, &src_addr->sa);
	if (ret)
		goto err;

	ret = ds_init_bufs(qp);
	if (ret)
		goto err;

	ret = rs_create_cq(rs, qp->cm_id);
	if (ret)
		goto err;

	memset(&qp_attr, 0, sizeof qp_attr);
	qp_attr.qp_context = qp;
	qp_attr.send_cq = qp->cm_id->send_cq;
	qp_attr.recv_cq = qp->cm_id->recv_cq;
	qp_attr.qp_type = IBV_QPT_UD;
	qp_attr.sq_sig_all = 1;
	qp_attr.cap.max_send_wr = rs->sq_size;
	qp_attr.cap.max_recv_wr = rs->rq_size;
	qp_attr.cap.max_send_sge = 1;
	qp_attr.cap.max_recv_sge = 2;
	qp_attr.cap.max_inline_data = rs->sq_inline;
	ret = rdma_create_qp(qp->cm_id, NULL, &qp_attr);
	if (ret)
		goto err;

	rs->sq_inline = qp_attr.cap.max_inline_data;
	ret = ds_add_qp_dest(qp, src_addr, addrlen);
	if (ret)
		goto err;

	event.events = EPOLLIN;
	event.data.ptr = qp;
	ret = epoll_ctl(rs->epfd,  EPOLL_CTL_ADD,
			qp->cm_id->recv_cq_channel->fd, &event);
	if (ret)
		goto err;

	for (i = 0; i < rs->rq_size; i++) {
		ret = ds_post_recv(rs, qp, i * RS_SNDLOWAT);
		if (ret)
			goto err;
	}

	ds_insert_qp(rs, qp);
	*new_qp = qp;
	return 0;
err:
	ds_free_qp(qp);
	return ret;
}

static int ds_get_qp(struct rsocket *rs, union socket_addr *src_addr,
		     socklen_t addrlen, struct ds_qp **qp)
{
	if (rs->qp_list) {
		*qp = rs->qp_list;
		do {
			if (!ds_compare_addr(rdma_get_local_addr((*qp)->cm_id),
					     src_addr))
				return 0;

			*qp = ds_next_qp(*qp);
		} while (*qp != rs->qp_list);
	}

	return ds_create_qp(rs, src_addr, addrlen, qp);
}

static int ds_get_dest(struct rsocket *rs, const struct sockaddr *addr,
		       socklen_t addrlen, struct ds_dest **dest)
{
	union socket_addr src_addr;
	socklen_t src_len;
	struct ds_qp *qp;
	struct ds_dest **tdest, *new_dest;
	int ret = 0;

	fastlock_acquire(&rs->map_lock);
	tdest = tfind(addr, &rs->dest_map, ds_compare_addr);
	if (tdest)
		goto found;

	ret = ds_get_src_addr(rs, addr, addrlen, &src_addr, &src_len);
	if (ret)
		goto out;

	ret = ds_get_qp(rs, &src_addr, src_len, &qp);
	if (ret)
		goto out;

	tdest = tfind(addr, &rs->dest_map, ds_compare_addr);
	if (!tdest) {
		new_dest = calloc(1, sizeof(*new_dest));
		if (!new_dest) {
			ret = ERR(ENOMEM);
			goto out;
		}

		memcpy(&new_dest->addr, addr, addrlen);
		new_dest->qp = qp;
		tdest = tsearch(&new_dest->addr, &rs->dest_map, ds_compare_addr);
	}

found:
	*dest = *tdest;
out:
	fastlock_release(&rs->map_lock);
	return ret;
}
/*
将 addr 赋值给 cm_id->route.addr.dst_addr ，并执行connect
*/
int rconnect(int socket, const struct sockaddr *addr, socklen_t addrlen)
{
	struct rsocket *rs;
	int ret, save_errno;

	rs = idm_lookup(&idm, socket);
	if (!rs)
		return ERR(EBADF);
	if (rs->type == SOCK_STREAM) {
		memcpy(&rs->cm_id->route.addr.dst_addr, addr, addrlen);
		ret = rs_do_connect(rs);
		if (ret == -1 && errno == EINPROGRESS) {
			save_errno = errno;
			/* The app can still drive the CM state on failure */
			rs_notify_svc(&connect_svc, rs, RS_SVC_ADD_CM);
			errno = save_errno;
		}
	} else {
		if (rs->state == rs_init) {
			ret = ds_init_ep(rs);
			if (ret)
				return ret;
		}

		fastlock_acquire(&rs->slock);
		ret = connect(rs->udp_sock, addr, addrlen);
		if (!ret)
			ret = ds_get_dest(rs, addr, addrlen, &rs->conn_dest);
		fastlock_release(&rs->slock);
	}
	return ret;
}
/*
 * 获取send buffer 中ctrl buffer 的地址
 * 由于ctrl msg 与 data 使用同一块send buffer
 * 需要根据 ctrl msg 的序号 * 单个ctrl msg 大小，得到当前ctrl msg 相对于sbuf 起始地址的偏移量，再得到当前ctrl msg 起始地址
 *
 */
static void *rs_get_ctrl_buf(struct rsocket *rs)
{
	return rs->sbuf + rs->sbuf_size +
		RS_MAX_CTRL_MSG * (rs->ctrl_seqno & (RS_QP_CTRL_SIZE - 1));
}

/*
 * 将 msg 作为 imm_data 通过 rs->cm_id->qp 发送
 * 当 rs->opts 表明为iWarp 使用的send 时，使用 send opcode 发送
 * 否则针对RoCE，使用 write_with_imm 发送
 * 同为RoCE 发送write_with_imm ，与 rs_post_write_msg 的区别是
 */ 
static int rs_post_msg(struct rsocket *rs, uint32_t msg)
{
	struct ibv_send_wr wr, *bad;
	struct ibv_sge sge;

	wr.wr_id = rs_send_wr_id(msg);// 将无符号32 位整形msg 扩展为64 位，扩展时高位补0，最高位为0 表示是send wr
	wr.next = NULL;
	if (!(rs->opts & RS_OPT_MSG_SEND)) {// RoCE 使用write with imm 发送rsocket message
		wr.sg_list = NULL;
		wr.num_sge = 0;
		wr.opcode = IBV_WR_RDMA_WRITE_WITH_IMM;
		wr.send_flags = 0;
		wr.imm_data = htobe32(msg);
	} else { // iWarp 使用 send 发送 rsocket message
		sge.addr = (uintptr_t) &msg;
		sge.lkey = 0;
		sge.length = sizeof msg;
		wr.sg_list = &sge;
		wr.num_sge = 1;
		wr.opcode = IBV_WR_SEND;
		wr.send_flags = IBV_SEND_INLINE;
	}

	return rdma_seterrno(ibv_post_send(rs->cm_id->qp, &wr, &bad));
}

/*
 * 使用 rdma write 发送，wr.send_flags 为传入的 flags
 *
 */
static int rs_post_write(struct rsocket *rs,
			 struct ibv_sge *sgl, int nsge,
			 uint32_t wr_data, int flags,
			 uint64_t addr, uint32_t rkey)
{
	struct ibv_send_wr wr, *bad;

	wr.wr_id = rs_send_wr_id(wr_data);// wr_id 高位补0，最高位是0 表示是send wr
	wr.next = NULL;
	wr.sg_list = sgl;
	wr.num_sge = nsge;
	wr.opcode = IBV_WR_RDMA_WRITE;
	wr.send_flags = flags;
	wr.wr.rdma.remote_addr = addr;
	wr.wr.rdma.rkey = rkey;

	return rdma_seterrno(ibv_post_send(rs->cm_id->qp, &wr, &bad));
}

/*
 * 将 msg 作为 imm_data 发送出去
 * 支持 RoCE 协议时使用 write_with_imm 发送
 * 支持 iWarp 协议时使用 write + send 两步模拟 write_with_imm 发送
 */
static int rs_post_write_msg(struct rsocket *rs,
			 struct ibv_sge *sgl, int nsge,
			 uint32_t msg, int flags,
			 uint64_t addr, uint32_t rkey)
{
	struct ibv_send_wr wr, *bad;
	struct ibv_sge sge;
	int ret;

	wr.next = NULL;
	if (!(rs->opts & RS_OPT_MSG_SEND)) { // RoCE rdma write
		wr.wr_id = rs_send_wr_id(msg); // 
		wr.sg_list = sgl;
		wr.num_sge = nsge;// rs_send_credits() 传入的 nsge 为1
		wr.opcode = IBV_WR_RDMA_WRITE_WITH_IMM;
		wr.send_flags = flags;// rs_send_credits() 传入的 flags 为0
		wr.imm_data = htobe32(msg);// 
		wr.wr.rdma.remote_addr = addr;
		wr.wr.rdma.rkey = rkey;

		return rdma_seterrno(ibv_post_send(rs->cm_id->qp, &wr, &bad));
	} else {// 由于 iWarp 不支持write with imm，因此分两步模拟write with imm：
		ret = rs_post_write(rs, sgl, nsge, msg, flags, addr, rkey); // 1，先rdma write 进行 数据写入；
		if (!ret) {
			wr.wr_id = rs_send_wr_id(rs_msg_set(rs_msg_op(msg), 0)) |
				   RS_WR_ID_FLAG_MSG_SEND;
			sge.addr = (uintptr_t) &msg;
			sge.lkey = 0;
			sge.length = sizeof msg;
			wr.sg_list = &sge;
			wr.num_sge = 1;
			wr.opcode = IBV_WR_SEND;
			wr.send_flags = IBV_SEND_INLINE;

			ret = rdma_seterrno(ibv_post_send(rs->cm_id->qp, &wr, &bad));// 2，再执行rdma send inline 发送rsocket 的 msg
		}
		return ret;
	}
}

static int ds_post_send(struct rsocket *rs, struct ibv_sge *sge,
			uint32_t wr_data)
{
	struct ibv_send_wr wr, *bad;

	wr.wr_id = rs_send_wr_id(wr_data);
	wr.next = NULL;
	wr.sg_list = sge;
	wr.num_sge = 1;
	wr.opcode = IBV_WR_SEND;
	wr.send_flags = (sge->length <= rs->sq_inline) ? IBV_SEND_INLINE : 0;
	wr.wr.ud.ah = rs->conn_dest->ah;
	wr.wr.ud.remote_qpn = rs->conn_dest->qpn;
	wr.wr.ud.remote_qkey = RDMA_UDP_QKEY;

	return rdma_seterrno(ibv_post_send(rs->conn_dest->qp->cm_id->qp, &wr, &bad));
}

/*
 * Update target SGE before sending data.  Otherwise the remote side may
 * update the entry before we do.
 * 在发送数据前更新要发送的目标sge，否则远端可能会在发送端更新前对此sge 进行更新
 * 发送数据是向 tcp->target_sgl[tcp->target_sge].addr 地址发送
 */
static int rs_write_data(struct rsocket *rs,
			 struct ibv_sge *sgl, int nsge,
			 uint32_t length, int flags)
{
	uint64_t addr;
	uint32_t rkey;

	rs->sseq_no++;									// send 序号加1
	rs->sqe_avail--;								// 可用 sqe 减1 
	if (rs->opts & RS_OPT_MSG_SEND)
		rs->sqe_avail--;							// iWarp 由于使用 rdma write + rdma send 两次操作来模拟 RoCE 一次 write_with_imm 操作，因此消耗 sqe_avail 额外减1
	rs->sbuf_bytes_avail -= length;					// send buf 可用字节数减去 要发送的数据长度

	addr = rs->target_sgl[rs->target_sge].addr;		// 保存当前 target_sge 对应的内存地址addr，此 addr 最初为建立连接时 save conn data 保存的对端 rbuf 地址
	rkey = rs->target_sgl[rs->target_sge].key;		// 保存当前 target_sge 对应的内存的 remote key

	rs->target_sgl[rs->target_sge].addr += length;	// 更新 target_sge 对应的对端 rbuf 中可写入的内存地址，向后移动length 个位置，下次写入时从最新地址开始写入
	rs->target_sgl[rs->target_sge].length -= length;// 更新 target_sge 对应的对端 rbuf 中可写入的内存大小，当减小为0 时会更新 target_sge（也即下面的 if 流程）

	if (!rs->target_sgl[rs->target_sge].length) {	// 更新 rs->target_sge ，即后续写入将使用接收端 rbuf 的另外一部分进行写入
		if (++rs->target_sge == RS_SGL_SIZE)		// 若 rs->target_sge 更新后为2，则重置为0
			rs->target_sge = 0;
	}

	return rs_post_write_msg(rs, sgl, nsge, rs_msg_set(RS_OP_DATA, length),
				 flags, addr, rkey);
}

static int rs_write_direct(struct rsocket *rs, struct rs_iomap *iom, uint64_t offset,
			   struct ibv_sge *sgl, int nsge, uint32_t length, int flags)
{
	uint64_t addr;

	rs->sqe_avail--;
	rs->sbuf_bytes_avail -= length;

	addr = iom->sge.addr + offset - iom->offset;
	return rs_post_write(rs, sgl, nsge, rs_msg_set(RS_OP_WRITE, length),
			     flags, addr, iom->sge.key);
}

static int rs_write_iomap(struct rsocket *rs, struct rs_iomap_mr *iomr,
			  struct ibv_sge *sgl, int nsge, int flags)
{
	uint64_t addr;

	rs->sseq_no++;
	rs->sqe_avail--;
	if (rs->opts & RS_OPT_MSG_SEND)
		rs->sqe_avail--;
	rs->sbuf_bytes_avail -= sizeof(struct rs_iomap);

	addr = rs->remote_iomap.addr + iomr->index * sizeof(struct rs_iomap);
	return rs_post_write_msg(rs, sgl, nsge, rs_msg_set(RS_OP_IOMAP_SGL, iomr->index),
				 flags, addr, rs->remote_iomap.key);
}
/*
 * sbuf 中 索引rs->sbuf_size - 索引0 的长度差，作为sbuf 中待发送数据的长度
 *
 */
static uint32_t rs_sbuf_left(struct rsocket *rs)
{
	return (uint32_t) (((uint64_t) (uintptr_t) &rs->sbuf[rs->sbuf_size]) -
			   rs->ssgl[0].addr);
}

static void rs_send_credits(struct rsocket *rs)
{
	struct ibv_sge ibsge;
	struct rs_sge sge, *sge_buf;
	int flags;

	rs->ctrl_seqno++;// control msg 序号+1
	rs->rseq_comp = rs->rseq_no + (rs->rq_size >> 1);				// 更新credits 之后，后续可处理的write with imm 操作次数与初始时一样仍设为 rq_size/2；rseq_no 是已经处理完成的 with imm 操作，在此基础上增加 rq_size/2，未来rseq_no 继续增加rq_size/2 时，会再次进行update credits 操作
																	// rseq_no 表示已处理完的rdma write with imm 操作个数
																	// rseq_comp 表示下次update credits 之前 rseq_no 的上限
	// 根据rs_give_cretids() 判断 rs->rbuf_bytes_avail >= (rs->rbuf_size >> 1)，或 rseq_no >= rseq_comp 时，进行下一次update credits 操作

// 若本次update credits 是由于 rbuf avail 大于了 rbuf_size/2
	if (rs->rbuf_bytes_avail >= (rs->rbuf_size >> 1)) {// 若rbuf 中可用字节数大于rbuf_size，则针对RoCE 协议可执行 rdma write with imm 操作
		if (rs->opts & RS_OPT_MSG_SEND)								// 针对iwarp 所用rdma send操作，由于发送credits 使用 rdma wrie + rdma send 两次操作，因此ctrl_seqno 额外加1
			rs->ctrl_seqno++;
// 参考 https://github.com/linux-rdma/rdma-core/blob/master/librdmacm/docs/rsocket
// 对应上述文档中 host B 有新的 receive buffers 可用的情形：
// 准备 SGE，对应新的可用receive buffers，包含了receive buffers 的addr，可用空间大小，rkey
// 向host A 的target SGL 发送SGE
// host A 将根据 target SGL 中被更新的SGE，获取host B 可用receive buffers 的addr，length，rkey
// host A 后续的发送，将会把数据rdma write 到host B 同步过来的可用receive buffer 中

		if (!(rs->opts & RS_OPT_SWAP_SGL)) {// 若不需要进行网络序和主机序转换
			sge.addr = (uintptr_t) &rs->rbuf[rs->rbuf_free_offset];	// 将rbuf 空闲空间起始地址赋值给sge.addr
			sge.key = rs->rmr->rkey;								// 将rbuf 对应的 mr的rkey 赋值给sge.key，供对端未来执行rdma write 使用
			sge.length = rs->rbuf_size >> 1;						// 由于rbuf 可用receive buffer >= rbuf_size 的一半，将sge 长度设为rbuf_size 的一半
																	// 对端未来针对此receive buffers 的写入数据不能大于此length
		} else {
			sge.addr = bswap_64((uintptr_t) &rs->rbuf[rs->rbuf_free_offset]);
			sge.key = bswap_32(rs->rmr->rkey);
			sge.length = bswap_32(rs->rbuf_size >> 1);
		}

		if (rs->sq_inline < sizeof sge) {							// 如果send queue inline 数量小于sge 变量大小，表示不使用 IBV_SEND_INLINE 发送？
										 							// 使用 rdma write with imm 发送，就需要将要发送的sge 复制到sbuf 中
										 							// 然后调用ibv_post_sned()从sbuf 中发送到target->sgl.addr 中
			sge_buf = rs_get_ctrl_buf(rs);							// 获取下一个control msg 在sbuf 中的地址
			memcpy(sge_buf, &sge, sizeof sge);						// 将sge 的内容复制到sbuf 中
			ibsge.addr = (uintptr_t) sge_buf;						// 将control msg 在sbuf 所占的内存地址赋值给 ibsge.addr
			ibsge.lkey = rs->smr->lkey;								// 将send mr 的local key 赋值给ibsge.lkey，供ibv_post_send() 操作获取到本地读取ctrl msg 并发送的local access 权限
			flags = 0;
		} else { // 若使用rdma send 发送inline 数据，不需要从sbuf 中发送，也不需要local key
			ibsge.addr = (uintptr_t) &sge;
			ibsge.lkey = 0;
			flags = IBV_SEND_INLINE;
		}
		ibsge.length = sizeof(sge);// 发送的sge 长度

// 发送credits；
// rs_msg_set 将 RS_OP_SGL 左移29位，4的二进制为100，左移29位后，msg 的高三位即为100，表示 Credit Update 
// 此时低0～28位的数据表示 received credits granted，即被授权可接收的credits，也就是可用的receive buffer 的信息
// 此处低0～28位数据为 rq_size 384 + rseq_no，因为在rs_create_ep 时，已经提交了 rq_size 个 ibv_post_recv，而每次poll 到recv 完成事件时，都提交了对应的 ibv_post_recv 并将rseq_no 加1，则当前共提交了 rq_size + rseq_no 次 ibv_post_recv()，也即可用的credits 为两者之和
		rs_post_write_msg(rs, &ibsge, 1,
			rs_msg_set(RS_OP_SGL, rs->rseq_no + rs->rq_size), flags,
			rs->remote_sgl.addr + rs->remote_sge * sizeof(struct rs_sge),
			rs->remote_sgl.key);// 执行rdma write
								// 参数1 rsocket 实例，参数2 将credits 数据封装成 msg 后存放的地址，参数3 更新的sge 个数
								// 参数4 credits 封装成的msg，高3位为100 表示为 credit update 操作类型；低29位是要更新的 credits 数值
								// 参数5 rdma write 操作对端内存的地址，由于remote_sgl.addr 记录的是对端接收 credits 消息的内存起始地址，加上 remote_sge * 单个sge 长度表示本次使用的内存实际地址
								// 参数6 对端接收credits 内存对应的 mr rkey

// 执行 update credits ，表示未来接收到数据时将 消耗rbuf_bytes_avail 中 rbuf_size/2 大小的空间；将此部分空间预留出来
// 并将可用内存偏移量更新
// 同时还需要更新对端接收 credits 的sge
		rs->rbuf_bytes_avail -= rs->rbuf_size >> 1;		// rbuf 可用字节减少 rbuf_size/2
		rs->rbuf_free_offset += rs->rbuf_size >> 1;		// rbuf 可用地址后移 rbuf_size/2
		if (rs->rbuf_free_offset >= rs->rbuf_size) 		// 当判断可用内存偏移量超过rbuf size 时，重置偏移量，循环使用 rbuf
			rs->rbuf_free_offset = 0;
		if (++rs->remote_sge == rs->remote_sgl.length)// 每执行一次credits update 后，切换一次sge，将另一部分内存供下次update credits 使用
			rs->remote_sge = 0;// 当判断remote sge达到 2 时，重置remote sge；循环使用两个sge
	} else {
		// 否则，本次update credits 是由于 rseq_no >=rseq_comp ，本轮已经至少接收了 rq_size/2 次rdma write with imm，而非rbuf availbytes >= rbuf_size/2
		// 只需要向对端更新sseq_comp，无须更新sgl[sge].length 及sge
		rs_post_msg(rs, rs_msg_set(RS_OP_SGL, rs->rseq_no + rs->rq_size));
	}
}

/*
 * 根据ctrl_seqno 和 ctrl_max_seqno 比较结果，判断是否可以发送 ctrl 消息
 * ctrl_max_seqno 在每次获得 发送ctrl 消息的 wc 后，加1
 * ctrl_seqno 在每次执行 update credits 发送时加1
 * 在每次执行update credits 之前，需判断 ctrl_avail，保证ctrl_seqno < ctrl_max_seqno
 *
 */
static inline int rs_ctrl_avail(struct rsocket *rs)
{
	return rs->ctrl_seqno != rs->ctrl_max_seqno;
}

/* Protocols that do not support RDMA write with immediate may require 2 msgs */
static inline int rs_2ctrl_avail(struct rsocket *rs)
{
	return (int)((rs->ctrl_seqno + 1) - rs->ctrl_max_seqno) < 0;
}

static int rs_give_credits(struct rsocket *rs)
{
	if (!(rs->opts & RS_OPT_MSG_SEND)) {// roce
		return ((rs->rbuf_bytes_avail >= (rs->rbuf_size >> 1)) ||
			((short) ((short) rs->rseq_no - (short) rs->rseq_comp) >= 0)) &&
		       rs_ctrl_avail(rs) && (rs->state & rs_connected); // rbuf 可用字节数大于等于 rbuf size 的一半							 // 表示recv buf 中可用空间超过了每次传输需要使用的空间，有1个sge 大小的空间可用了
			   													// 或者同时满足一下两个条件
																// recv sequence number 减去 recv sequence comp 的差大于等于0， 	// rseq_no 表示已经接受完成的rmsg 元素总数，当大于等于 rseq_comp 时，说明
			   													// ctrl_seqno 不等于ctrl_max_seqno ，同时rs 已经connected
	} else {// iwarp
		return ((rs->rbuf_bytes_avail >= (rs->rbuf_size >> 1)) ||
			((short) ((short) rs->rseq_no - (short) rs->rseq_comp) >= 0)) &&
		       rs_2ctrl_avail(rs) && (rs->state & rs_connected);
	}
}

/*
 * 判断是否可以提供credits，并在可提供时调用ibv_post_send()发送credits
 */
static void rs_update_credits(struct rsocket *rs)
{
	if (rs_give_credits(rs))// 判断可用recv buffer 是否足够，或者已接受到的seq 序号大于已完成的seq 表明仍有接收但未完成的消息，同时ctrl seqno不能大于上线，且必须是connected 状态
		rs_send_credits(rs);// 准备imm data 并调用ibv_post_send() 执行rdma write
}

/*
 * 循环调用ibv_poll_cq() 直到获取不到cqe
 * 对于获取到的wc 中的cqe，判断完成事件类型（send、recv），判断消息类型（控制消息，数据传输）并分别处理
 * 针对控制消息
 * 	1. credits 接收完成事件，会根据发送来的credit 更新rs->sseq_comp
 * 	2. ctrl 接收完成事件，会根据ctrl 类型更新 rs->state
 * 	3. credits 发送完成事件，rs->ctrl_max_seqno++
 * 	4. ctrl 发送完成事件，rs->ctrl_max_seqno++ 且若为disconnect 需更新 rs->state
 * 针对数据传输
 * 	1. 数据发送，rs->sqe_avail++ 且rs->sbuf_bytes_avail += sizeof msg
 * 	2. 数据接受，将消息的op和data 记录到rs-> rmsg 中
 */
static int rs_poll_cq(struct rsocket *rs)
{
	struct ibv_wc wc;
	uint32_t msg;
	int ret, rcnt = 0;

	while ((ret = ibv_poll_cq(rs->cm_id->recv_cq, 1, &wc)) > 0) {// 如果从recv cq 中获取到了1个 cqe
		if (rs_wr_is_recv(wc.wr_id)) {// 获取到的事件是recv 的完成事件；通过判断接收到的 wr_id 最高位是否为1，因为wr_id 最高位为0时是发送操作，最高位是1时是接收操作
			if (wc.status != IBV_WC_SUCCESS)
				continue;
			rcnt++;// 如果recv work request 正常完成，recv count 加1

			if (wc.wc_flags & IBV_WC_WITH_IMM) {// 如果接收到的是write with imm 操作发送的数据
				msg = be32toh(wc.imm_data);// 将imm data 转为主机序
			} else {// 否则接收到的是send 操作发送的数据
				msg = ((uint32_t *) (rs->rbuf + rs->rbuf_size))
					[rs_wr_data(wc.wr_id)];// 将无符号64位整型强制转换为无符号32位整型，高位数据被舍弃，低32位数据即为发送端发送的数据

			}
			switch (rs_msg_op(msg)) {// 判断 op 类型
			case RS_OP_SGL:// 若接收到的消息是SGL 控制消息，即为rs_send_credits() 发送来的credits 信息（rs_msg_set(RS_OP_SGL, rs->rseq_no + rs->rq_size)）
				rs->sseq_comp = (uint16_t) rs_msg_data(msg);// 根据收到的32位无符号整数msg，将值高3位设为0，然后强制转换为16位无符号整型，存入rs send seq completion 中
				break;
			case RS_OP_IOMAP_SGL:
				/* The iomap was updated, that's nice to know. */
				break;
			case RS_OP_CTRL:// 若接收到的消息是CTRL 控制消息
				if (rs_msg_data(msg) == RS_CTRL_DISCONNECT) {
					rs->state = rs_disconnected;
					return 0;
				} else if (rs_msg_data(msg) == RS_CTRL_SHUTDOWN) {
					if (rs->state & rs_writable) {
						rs->state &= ~rs_readable;
					} else {
						rs->state = rs_disconnected;
						return 0;
					}
				}
				break;
			case RS_OP_WRITE:
				/* We really shouldn't be here. */
				break;
			default:// 若不是以上 op 类型的数据
				// printf tcp_msg_op(msg) 得到结果大多是 无符号整数 0，对应表示TCP_OP_DATA；
				// printf msg 为无符号整数uint32，输出结果为 65535、2048、8192、32768、43072 等值
				// printf("rsocket debug: switch (tcp_msg_op(msg %u ):%u) default ",msg,rs_msg_op(msg));
				rs->rmsg[rs->rmsg_tail].op = rs_msg_op(msg); 							// 将数据高3位 存储到 rmsg 队尾元素的 op 属性中
				rs->rmsg[rs->rmsg_tail].data = rs_msg_data(msg); 						// 将数据低29位 存储到 rmsg 队尾元素的 data 属性中
				if (++rs->rmsg_tail == rs->rq_size + 1)	// rmsg 队尾元素+1，若达到recv queue 大小，则重置为0
					rs->rmsg_tail = 0;
				break;
			}
		} else {// 获取到的wc 是发送操作的完成事件
			switch  (rs_msg_op(rs_wr_data(wc.wr_id))) {
			case RS_OP_SGL: 												// 完成update credits 发送
				rs->ctrl_max_seqno++; 										// 控制信息最大序号加1
				break;
			case RS_OP_CTRL:
				rs->ctrl_max_seqno++; 										// 控制信息最大序号加1
				if (rs_msg_data(rs_wr_data(wc.wr_id)) == RS_CTRL_DISCONNECT)// 若发送的控制信息为断开连接
					rs->state = rs_disconnected;// 修改连接状态
				break;
			case RS_OP_IOMAP_SGL:
				rs->sqe_avail++;
				if (!rs_wr_is_msg_send(wc.wr_id))
					rs->sbuf_bytes_avail += sizeof(struct rs_iomap);
				break;
			default:
				rs->sqe_avail++; //
				rs->sbuf_bytes_avail += rs_msg_data(rs_wr_data(wc.wr_id));
				break;
			}
			if (wc.status != IBV_WC_SUCCESS && (rs->state & rs_connected)) {
				rs->state = rs_error;
				rs->err = EIO;
			}
		}
	}
// 当没有从cq 中获取到cqe 时，
	if (rs->state & rs_connected) {
		while (!ret && rcnt--)// ibv_poll_cq 正常返回0 且接收计数rcnt 大于0时，接收计数减1，并提交一次 ibv_post_recv()
			ret = rs_post_recv(rs);

		if (ret) {
			rs->state = rs_error;
			rs->err = errno;
		}
	}
	return ret;
}

/*
 * 判断rs->cq_armed，若为0 表示已经从cq 中获取到过cqe，直接返回0
 * 否则执行ibv_get_cq_event()，从cm_id的recv cq channel 中获得cqe，并将rs->cq_armed 重置为0
 * 返回 ibv_get_cq_event() 执行结果
 * 
 */
static int rs_get_cq_event(struct rsocket *rs)
{
	struct ibv_cq *cq;
	void *context;
	int ret;

	if (!rs->cq_armed)
		return 0;

	ret = ibv_get_cq_event(rs->cm_id->recv_cq_channel, &cq, &context);
	if (!ret) {// 执行成功，表示cq channel 中存在cqe 事件
		if (++rs->unack_cqe >= rs->sq_size + rs->rq_size) {				// 若unack_cqe 大于等于 send queue 和 recv queue 队列长度之和
			ibv_ack_cq_events(rs->cm_id->recv_cq, rs->unack_cqe);		// 执行ack 确认所有unack event
			rs->unack_cqe = 0;// unack_cqe 清零
		}
		rs->cq_armed = 0;
	} else if (!(errno == EAGAIN || errno == EINTR)) {
		rs->state = rs_error;
	}

	return ret;
}

/*
 * Although we serialize rsend and rrecv calls with respect to themselves,
 * both calls may run simultaneously and need to poll the CQ for completions.
 * We need to serialize access to the CQ, but rsend and rrecv need to
 * allow each other to make forward progress.
 *
 * For example, rsend may need to wait for credits from the remote side,
 * which could be stalled until the remote process calls rrecv.  This should
 * not block rrecv from receiving data from the remote side however.
 *
 * We handle this by using two locks.  The cq_lock protects against polling
 * the CQ and processing completions.  The cq_wait_lock serializes access to
 * waiting on the CQ.
 * 
 * 尽管rsend 和 rrecv 的调用单独看都是串行化的，但两类调用还是会同时执行并需要从CQ 中获取完成事件
 * 我们需要将对CQ 的访问串行，同时 rsend 和rrecv 需要允许对方正常继续执行。
 * 
 * 例如，rsend 可能需要等待远端更新credits，而远端可能会在调用rrecv 之后才会更新credits。
 * 但rsend 的等待，不能阻塞执行rrecv 从而接收远端的数据
 * 
 * 我们通过使用两把锁来处理此情况。 cq_lock 用来保护从CQ 中获取事件并进行处理。
 * cq_wait_lock 用来将对CQ 的访问等待进行串行化。
 */
static int rs_process_cq(struct rsocket *rs, int nonblock, int (*test)(struct rsocket *rs))
{
	int ret;

	fastlock_acquire(&rs->cq_lock);// 首先获取 cq_lock ，从而可以获取到cq 中的完成事件
	do {
		rs_update_credits(rs);							// 尝试向对端更新credits
		ret = rs_poll_cq(rs); 							// 循环从cq 中获取cqe，直到获取不到新的cqe；对获取到的cqe 按照不同wr 进行处理；针对recv wc再次提交新的recv wr；
		if (test(rs)) {									// test()函数为 rssend() => rs_get_comp() => rs_process_cq() 传递来的rs_conn_can_send()，判断 rs_can_send(rs) || !(rs->state & rs_writable) ，有数据可发送，或者rs 不可写时，正常退出
					   									// rrecv() => rs_get_comp() => rs_process_cq() 传递来的 rs_conn_have_rdata()，判断 rs_have_rdata(rs) || !(rs->state & rs_readable)，有已接收的数据需要处理，或者rs 不可读时，正常退出
			ret = 0;								// 若 rs 可以执行send 或 rs 状态为不可写，结束循环
			break;
		} else if (ret) {							// 否则 若rs_poll_cq 返回值不为0，说明执行ibv_poll_cq 或ibv_post_recv 时出现错误或被下一个else if 设置了ret=-1，
			break;										// 结束循环，并在循环后将错误信息返回
		} else if (nonblock) {						// 否则 若传入的nonblock 为真，
			ret = ERR(EWOULDBLOCK);						// 设置errno==11及ret==-1，在下次循环时可能被前一个 else if 判断ret!=0 而退出循环；
		} 

// 下方逻辑对应 rs_get_comp() 中在超过polling_time 时，执行最后一次 阻塞的 rs_process_cq()
		else if (!rs->cq_armed) {					// 否则 test(rs)为否，nonblock 为否，ret == 0，且rs->cq_armed ==0 表示已经从cq 中获取到过cqe
			ibv_req_notify_cq(rs->cm_id->recv_cq, 0);	// 再次请求recv_cq 中完成事件的通知
			rs->cq_armed = 1;
		} else {									// 否则 说明没有从cq 中获取到过cqe
			rs_update_credits(rs);						// 再次尝试向对端更新credits
			fastlock_acquire(&rs->cq_wait_lock);// 获取cq_wait_lock，从而可以使用阻塞的方式从cq 中获得完成事件
			fastlock_release(&rs->cq_lock);// 释放cq_lock，从而其他操作可以从cq 中获取完成事件

			ret = rs_get_cq_event(rs);			// 从rs->cm_id->recv_cq_channel 中获得cqe，并发送ack
			fastlock_release(&rs->cq_wait_lock);// 释放cq_wait_lock，不再使用阻塞的方式等待从cq 获得完成事件
			fastlock_acquire(&rs->cq_lock);// 重新申请cq_lock ，方便循环外统一进行release 操作
		}
	} while (!ret);// ret 为0时，表示没有从cq 中poll 到事件时，持续循环

	rs_update_credits(rs);// 向对端更新rbuf 状态
	fastlock_release(&rs->cq_lock);
	return ret;
}

/*
 * 在polling_time 限定时间内不断循环执行rs_process_cq()
 * rs_process_cq() 中执行 rs_poll_cq() ，并在执行正常结束后不断循环执行；直到 rs_poll_cq() 或ibv_ack_cq_events() 执行出错，或者传入参数为nonblock==1且 rs_poll_cq() 返回0
 * rs_poll_cq() 中循环执行 ibv_poll_cq()，在获取不到cqe 后返回；对于获取到的cqe 根据imm data 32位所传递的op、data 不同类型分别处理
 */
static int rs_get_comp(struct rsocket *rs, int nonblock, int (*test)(struct rsocket *rs))
{
	uint64_t start_time = 0;
	uint32_t poll_time;
	int ret;

	do {
		ret = rs_process_cq(rs, 1, test);// 执行ibv_poll_cq() ，并在返回0时继续循环执行；由于nonblock，因此ibv_poll_cq()==0 且rs_conn_can_send() 为false 时，不会阻塞等待ibv_get_cq_event()，而是直接退出
		if (!ret || nonblock || errno != EWOULDBLOCK)
			return ret;

		if (!start_time)
			start_time = rs_time_us();

		poll_time = (uint32_t) (rs_time_us() - start_time);
	} while (poll_time <= polling_time);// pollint_time 时间段内持续循环执行 rs_process_cq

	ret = rs_process_cq(rs, 0, test);// 超过polling_time 后，再执行一次ibv_poll_cq() ，本次执行完后可能进入阻塞情况下等待ibv_get_cq_event() 返回的情况
	return ret;
}

static int ds_valid_recv(struct ds_qp *qp, struct ibv_wc *wc)
{
	struct ds_header *hdr;

	hdr = (struct ds_header *) (qp->rbuf + rs_wr_data(wc->wr_id));
	return ((wc->byte_len >= sizeof(struct ibv_grh) + DS_IPV4_HDR_LEN) &&
		((hdr->version == 4 && hdr->length == DS_IPV4_HDR_LEN) ||
		 (hdr->version == 6 && hdr->length == DS_IPV6_HDR_LEN)));
}

/*
 * Poll all CQs associated with a datagram rsocket.  We need to drop any
 * received messages that we do not have room to store.  To limit drops,
 * we only poll if we have room to store the receive or we need a send
 * buffer.  To ensure fairness, we poll the CQs round robin, remembering
 * where we left off.
 */
static void ds_poll_cqs(struct rsocket *rs)
{
	struct ds_qp *qp;
	struct ds_smsg *smsg;
	struct ds_rmsg *rmsg;
	struct ibv_wc wc;
	int ret, cnt;

	if (!(qp = rs->qp_list))
		return;

	do {
		cnt = 0;
		do {
			ret = ibv_poll_cq(qp->cm_id->recv_cq, 1, &wc);
			if (ret <= 0) {
				qp = ds_next_qp(qp);
				continue;
			}

			if (rs_wr_is_recv(wc.wr_id)) {
				if (rs->rqe_avail && wc.status == IBV_WC_SUCCESS &&
				    ds_valid_recv(qp, &wc)) {
					rs->rqe_avail--;
					rmsg = &rs->dmsg[rs->rmsg_tail];
					rmsg->qp = qp;
					rmsg->offset = rs_wr_data(wc.wr_id);
					rmsg->length = wc.byte_len - sizeof(struct ibv_grh);
					if (++rs->rmsg_tail == rs->rq_size + 1)
						rs->rmsg_tail = 0;
				} else {
					ds_post_recv(rs, qp, rs_wr_data(wc.wr_id));
				}
			} else {
				smsg = (struct ds_smsg *) (rs->sbuf + rs_wr_data(wc.wr_id));
				smsg->next = rs->smsg_free;
				rs->smsg_free = smsg;
				rs->sqe_avail++;
			}

			qp = ds_next_qp(qp);
			if (!rs->rqe_avail && rs->sqe_avail) {
				rs->qp_list = qp;
				return;
			}
			cnt++;
		} while (qp != rs->qp_list);
	} while (cnt);
}

static void ds_req_notify_cqs(struct rsocket *rs)
{
	struct ds_qp *qp;

	if (!(qp = rs->qp_list))
		return;

	do {
		if (!qp->cq_armed) {
			ibv_req_notify_cq(qp->cm_id->recv_cq, 0);
			qp->cq_armed = 1;
		}
		qp = ds_next_qp(qp);
	} while (qp != rs->qp_list);
}

static int ds_get_cq_event(struct rsocket *rs)
{
	struct epoll_event event;
	struct ds_qp *qp;
	struct ibv_cq *cq;
	void *context;
	int ret;

	if (!rs->cq_armed)
		return 0;

	ret = epoll_wait(rs->epfd, &event, 1, -1);
	if (ret <= 0)
		return ret;

	qp = event.data.ptr;
	ret = ibv_get_cq_event(qp->cm_id->recv_cq_channel, &cq, &context);
	if (!ret) {
		ibv_ack_cq_events(qp->cm_id->recv_cq, 1);
		qp->cq_armed = 0;
		rs->cq_armed = 0;
	}

	return ret;
}

static int ds_process_cqs(struct rsocket *rs, int nonblock, int (*test)(struct rsocket *rs))
{
	int ret = 0;

	fastlock_acquire(&rs->cq_lock);
	do {
		ds_poll_cqs(rs);
		if (test(rs)) {
			ret = 0;
			break;
		} else if (nonblock) {
			ret = ERR(EWOULDBLOCK);
		} else if (!rs->cq_armed) {
			ds_req_notify_cqs(rs);
			rs->cq_armed = 1;
		} else {
			fastlock_acquire(&rs->cq_wait_lock);
			fastlock_release(&rs->cq_lock);

			ret = ds_get_cq_event(rs);
			fastlock_release(&rs->cq_wait_lock);
			fastlock_acquire(&rs->cq_lock);
		}
	} while (!ret);

	fastlock_release(&rs->cq_lock);
	return ret;
}

static int ds_get_comp(struct rsocket *rs, int nonblock, int (*test)(struct rsocket *rs))
{
	uint64_t start_time = 0;
	uint32_t poll_time;
	int ret;

	do {
		ret = ds_process_cqs(rs, 1, test);
		if (!ret || nonblock || errno != EWOULDBLOCK)
			return ret;

		if (!start_time)
			start_time = rs_time_us();

		poll_time = (uint32_t) (rs_time_us() - start_time);
	} while (poll_time <= polling_time);

	ret = ds_process_cqs(rs, 0, test);
	return ret;
}

/*
 * return (rs->fd_flags & O_NONBLOCK) || (flags & MSG_DONTWAIT)
 */
static int rs_nonblocking(struct rsocket *rs, int flags)
{
	return (rs->fd_flags & O_NONBLOCK) || (flags & MSG_DONTWAIT);
}

static int rs_is_cq_armed(struct rsocket *rs)
{
	return rs->cq_armed;
}

// 始终返回true
static int rs_poll_all(struct rsocket *rs)
{
	return 1;
}

/*
 * We use hardware flow control to prevent over running the remote
 * receive queue.  However, data transfers still require space in
 * the remote rmsg queue, or we risk losing notification that data
 * has been transfered.
 *
 * Be careful with race conditions in the check below.  The target SGL
 * may be updated by a remote RDMA write.
 * 判断本地target sql 是否存在可用sqe，sbuf_bytes_avail 是否不小于2k，send 序号是否未达到send comp 序号，target_sgl[target_sqe]是否不为空
 */
static int rs_can_send(struct rsocket *rs)
{
	if (!(rs->opts & RS_OPT_MSG_SEND)) {// RoCE rdma write
		return rs->sqe_avail && (rs->sbuf_bytes_avail >= RS_SNDLOWAT) &&
		       (rs->sseq_no != rs->sseq_comp) &&
		       (rs->target_sgl[rs->target_sge].length != 0);// 存在可用sqe ，并且可用send buffer 不小于2048，并且send sequence number 不等于send sequeue completion，并且target_sgl[target_sge] 长度不为0
	} else {// iWarp rdma send
		return (rs->sqe_avail >= 2) && (rs->sbuf_bytes_avail >= RS_SNDLOWAT) &&
		       (rs->sseq_no != rs->sseq_comp) &&
		       (rs->target_sgl[rs->target_sge].length != 0);
	}
}

static int ds_can_send(struct rsocket *rs)
{
	return rs->sqe_avail;
}

static int ds_all_sends_done(struct rsocket *rs)
{
	return rs->sqe_avail == rs->sq_size;
}
/*
 * 	return rs_can_send(rs) || !(rs->state & rs_writable);
 */
static int rs_conn_can_send(struct rsocket *rs)
{
	return rs_can_send(rs) || !(rs->state & rs_writable);
}

static int rs_conn_can_send_ctrl(struct rsocket *rs)
{
	return rs_ctrl_avail(rs) || !(rs->state & rs_connected);
}

/*
 * (rs->rmsg_head != rs->rmsg_tail)
 */
static int rs_have_rdata(struct rsocket *rs)
{
	return (rs->rmsg_head != rs->rmsg_tail);
}

static int rs_conn_have_rdata(struct rsocket *rs)
{
	return rs_have_rdata(rs) || !(rs->state & rs_readable);
}

static int rs_conn_all_sends_done(struct rsocket *rs)
{
	return ((((int) rs->ctrl_max_seqno) - ((int) rs->ctrl_seqno)) +
		rs->sqe_avail == rs->sq_size) ||
	       !(rs->state & rs_connected);
}

static void ds_set_src(struct sockaddr *addr, socklen_t *addrlen,
		       struct ds_header *hdr)
{
	union socket_addr sa;

	memset(&sa, 0, sizeof sa);
	if (hdr->version == 4) {
		if (*addrlen > sizeof(sa.sin))
			*addrlen = sizeof(sa.sin);

		sa.sin.sin_family = AF_INET;
		sa.sin.sin_port = hdr->port;
		sa.sin.sin_addr.s_addr =  hdr->addr.ipv4;
	} else {
		if (*addrlen > sizeof(sa.sin6))
			*addrlen = sizeof(sa.sin6);

		sa.sin6.sin6_family = AF_INET6;
		sa.sin6.sin6_port = hdr->port;
		sa.sin6.sin6_flowinfo = hdr->addr.ipv6.flowinfo;
		memcpy(&sa.sin6.sin6_addr, &hdr->addr.ipv6.addr, 16);
	}
	memcpy(addr, &sa, *addrlen);
}

static ssize_t ds_recvfrom(struct rsocket *rs, void *buf, size_t len, int flags,
			   struct sockaddr *src_addr, socklen_t *addrlen)
{
	struct ds_rmsg *rmsg;
	struct ds_header *hdr;
	int ret;

	if (!(rs->state & rs_readable))
		return ERR(EINVAL);

	if (!rs_have_rdata(rs)) {
		ret = ds_get_comp(rs, rs_nonblocking(rs, flags),
				  rs_have_rdata);
		if (ret)
			return ret;
	}

	rmsg = &rs->dmsg[rs->rmsg_head];
	hdr = (struct ds_header *) (rmsg->qp->rbuf + rmsg->offset);
	if (len > rmsg->length - hdr->length)
		len = rmsg->length - hdr->length;

	memcpy(buf, (void *) hdr + hdr->length, len);
	if (addrlen)
		ds_set_src(src_addr, addrlen, hdr);

	if (!(flags & MSG_PEEK)) {
		ds_post_recv(rs, rmsg->qp, rmsg->offset);
		if (++rs->rmsg_head == rs->rq_size + 1)
			rs->rmsg_head = 0;
		rs->rqe_avail++;
	}

	return len;
}

static ssize_t rs_peek(struct rsocket *rs, void *buf, size_t len)
{
	size_t left = len;
	uint32_t end_size, rsize;
	int rmsg_head, rbuf_offset;

	rmsg_head = rs->rmsg_head;
	rbuf_offset = rs->rbuf_offset;

	for (; left && (rmsg_head != rs->rmsg_tail); left -= rsize) {
		if (left < rs->rmsg[rmsg_head].data) {
			rsize = left;
		} else {
			rsize = rs->rmsg[rmsg_head].data;
			if (++rmsg_head == rs->rq_size + 1)
				rmsg_head = 0;
		}

		end_size = rs->rbuf_size - rbuf_offset;
		if (rsize > end_size) {
			memcpy(buf, &rs->rbuf[rbuf_offset], end_size);//TODO
			rbuf_offset = 0;
			buf += end_size;
			rsize -= end_size;
			left -= end_size;
		}
		memcpy(buf, &rs->rbuf[rbuf_offset], rsize);//TODO
		rbuf_offset += rsize;
		buf += rsize;
	}

	return len - left;
}

/*
 * Continue to receive any queued data even if the remote side has disconnected.
 */
ssize_t rrecv(int socket, void *buf, size_t len, int flags)
{
	struct rsocket *rs;
	size_t left = len;// left 为调用rrecv 时传入的可读取数据长度，表示调用方本次可接收的数据最大长度
	uint32_t end_size, rsize;
	int ret = 0;

	rs = idm_at(&idm, socket);
	if (!rs)
		return ERR(EBADF);
	if (rs->type == SOCK_DGRAM) { // 处理udp
		fastlock_acquire(&rs->rlock);
		ret = ds_recvfrom(rs, buf, len, flags, NULL, NULL);
		fastlock_release(&rs->rlock);
		return ret;
	}

	if (rs->state & rs_opening) { // 若尚未完成连接
		ret = rs_do_connect(rs); // 建立连接
		if (ret) {
			if (errno == EINPROGRESS)
				errno = EAGAIN;
			return ret;
		}
	}
	fastlock_acquire(&rs->rlock);
	do {
		if (!rs_have_rdata(rs)) { // 判断rmsg 中是否有接收到的imm data，若没有数据，执行 rs_poll_cq() 获取接收完成事件，并将数据存入rmsg
			ret = rs_get_comp(rs, rs_nonblocking(rs, flags),
					  rs_conn_have_rdata);
			if (ret)
				break;
		}

		if (flags & MSG_PEEK) { // rstream.c 传递来的flags 为 MSG_DONTWAIT 值为 0x40 ,MSG_PEEK 值为 0x02
			left = len - rs_peek(rs, buf, left);
			break;
		}

		for (; left && rs_have_rdata(rs); left -= rsize) {// 当可接收的数据长度left 不为0 且rmsg 中仍然有msg 需要处理时，执行循环；使用rsize 记录每次循环读取到的数据长度，因此每次循环时需要更新可接收的数据长度left；
			if (left < rs->rmsg[rs->rmsg_head].data) { // 由于rmsg 队列中元素的data 值存储的是【数据长度】，每次读取只能读取 left 和rmsg[].data 中的较小值；若当前left 值小于rmsg 队列头部元素的data 的值，则将较小的left 赋值给rsize，rsize 用来记录本次读取的数据长度
				rsize = left;
				rs->rmsg[rs->rmsg_head].data -= left; // rmsg[].data 由于大于了可读取的left 的长度，因此仍剩余 rmsg[].data -left 的数据未被读取，将剩余长度记录到rmsg[].data 中，下次继续读取
			} else {// 否则本次可读取的长度 大于 rmsg[].data 中记录的数据长度，因此本地读取数据长度就采用 rmsg[].data 的值，用rsize 记录本地读取的数据长度
				rs->rseq_no++; // recv 序号 加1，表示已处理完的rmsg 元素总个数 加1
				rsize = rs->rmsg[rs->rmsg_head].data;
				if (++rs->rmsg_head == rs->rq_size + 1) // rmsg_head 向后移动，当大小等于rq_size 时，重置为0；
					rs->rmsg_head = 0;
			}

			end_size = rs->rbuf_size - rs->rbuf_offset; // end_size 记录了rbuf_offset 位置之后的数据长度；
			// [-------------------------------------] rbuf
			// |<--------- rbuf_size --------------->|
			//      ⬆
			// rbuf_offset（此处只是为了说明offset 是指示 rbuf 中待复制到 buf 的数据的位置偏移量，注意rbuf_offset 并非指针）
			//      |<--------- end_size ----------->|
			// 
			// TODO: rs->rbuf_offset 什么时候完成了初始化？假设其未进行初始化，假设未赋值的int 变量为0，那么end_size 等于 rbuf_size
			if (rsize > end_size) {		// do wihle 第一次执行时到此处时，rsize 代表本轮循环全部要接收的数据大小，若rsize 大于 rbuf_size，需要首先将rbuf 装满，然后从rbuf 起始地址继续填充剩余数据
				memcpy(buf, &rs->rbuf[rs->rbuf_offset], end_size);// 将rbuf 中当前offset 之后的数据赋值到接送数据的buf 中，数据长度为end_size
				rs->rbuf_offset = 0; // 重置offset 为0
				buf += end_size;	 // 接收数据的buf 已接收到end_size 大小的数据，指针后移动以便继续后续赋值
				rsize -= end_size; 	 // 本次要接收数据长度减去已完成复制的数据长度，rsize 记录的为本次循环还可以接受的数据长度
				left -= end_size;    // 全部可接收数据长度减去已完成复制的数据长度
				rs->rbuf_bytes_avail += end_size; // rbuf 中长度为end_size 的数据被复制到buf，此部分数据占用的空间变为可用状态
			}
			memcpy(buf, &rs->rbuf[rs->rbuf_offset], rsize);// 若上面if 条件不满足，则rsize < end_size ，本次循环直接接收rsize 大小的数据；否则，在接受完end_size 大小的数据之后，继续从rbuf 起始位置接收大小为（本次循环可接受长度-已接受的end_size 长度，即上面if 中rsize更新后的值）的数据到buf 中
			rs->rbuf_offset += rsize; // 移动rbuf 中待复制数据的偏移量
			buf += rsize;// buf 指针向后移动
			rs->rbuf_bytes_avail += rsize; // rbuf 可用字节数增加
		}

	} while (left && (flags & MSG_WAITALL) && (rs->state & rs_readable));// 当 left 不为0 且 flags 为 MSG_WAITALL 且 rs可读时，循环进行数据复制；MSG_WAITALL 只能在阻塞模式时使用，进行循环读；参考 socket recv(sockfd, buff, buff_size, MSG_WAITALL)

	fastlock_release(&rs->rlock);
	return (ret && left == len) ? ret : len - left;
}

ssize_t rrecvfrom(int socket, void *buf, size_t len, int flags,
		  struct sockaddr *src_addr, socklen_t *addrlen)
{
	struct rsocket *rs;
	int ret;

	rs = idm_at(&idm, socket);
	if (!rs)
		return ERR(EBADF);
	if (rs->type == SOCK_DGRAM) {
		fastlock_acquire(&rs->rlock);
		ret = ds_recvfrom(rs, buf, len, flags, src_addr, addrlen);
		fastlock_release(&rs->rlock);
		return ret;
	}

	ret = rrecv(socket, buf, len, flags);
	if (ret > 0 && src_addr)
		rgetpeername(socket, src_addr, addrlen);

	return ret;
}

/*
 * Simple, straightforward implementation for now that only tries to fill
 * in the first vector.
 */
static ssize_t rrecvv(int socket, const struct iovec *iov, int iovcnt, int flags)
{
	return rrecv(socket, iov[0].iov_base, iov[0].iov_len, flags);
}

ssize_t rrecvmsg(int socket, struct msghdr *msg, int flags)
{
	if (msg->msg_control && msg->msg_controllen)
		return ERR(ENOTSUP);

	return rrecvv(socket, msg->msg_iov, (int) msg->msg_iovlen, msg->msg_flags);
}

ssize_t rread(int socket, void *buf, size_t count)
{
	return rrecv(socket, buf, count, 0);
}

ssize_t rreadv(int socket, const struct iovec *iov, int iovcnt)
{
	return rrecvv(socket, iov, iovcnt, 0);
}

static int rs_send_iomaps(struct rsocket *rs, int flags)
{
	struct rs_iomap_mr *iomr;
	struct ibv_sge sge;
	struct rs_iomap iom;
	int ret;

	fastlock_acquire(&rs->map_lock);
	while (!dlist_empty(&rs->iomap_queue)) {
		if (!rs_can_send(rs)) {
			ret = rs_get_comp(rs, rs_nonblocking(rs, flags),
					  rs_conn_can_send);
			if (ret)
				break;
			if (!(rs->state & rs_writable)) {
				ret = ERR(ECONNRESET);
				break;
			}
		}

		iomr = container_of(rs->iomap_queue.next, struct rs_iomap_mr, entry);
		if (!(rs->opts & RS_OPT_SWAP_SGL)) {// 若不需要进行网络序和主机序转换
			iom.offset = iomr->offset;
			iom.sge.addr = (uintptr_t) iomr->mr->addr;
			iom.sge.length = iomr->mr->length;
			iom.sge.key = iomr->mr->rkey;
		} else {
			iom.offset = bswap_64(iomr->offset);
			iom.sge.addr = bswap_64((uintptr_t) iomr->mr->addr);
			iom.sge.length = bswap_32(iomr->mr->length);
			iom.sge.key = bswap_32(iomr->mr->rkey);
		}

		if (rs->sq_inline >= sizeof iom) {
			sge.addr = (uintptr_t) &iom;
			sge.length = sizeof iom;
			sge.lkey = 0;
			ret = rs_write_iomap(rs, iomr, &sge, 1, IBV_SEND_INLINE);
		} else if (rs_sbuf_left(rs) >= sizeof iom) {
			memcpy((void *) (uintptr_t) rs->ssgl[0].addr, &iom, sizeof iom);
			rs->ssgl[0].length = sizeof iom;
			ret = rs_write_iomap(rs, iomr, rs->ssgl, 1, 0);
			if (rs_sbuf_left(rs) > sizeof iom)
				rs->ssgl[0].addr += sizeof iom;
			else
				rs->ssgl[0].addr = (uintptr_t) rs->sbuf;
		} else {
			rs->ssgl[0].length = rs_sbuf_left(rs);
			memcpy((void *) (uintptr_t) rs->ssgl[0].addr, &iom,
				rs->ssgl[0].length);
			rs->ssgl[1].length = sizeof iom - rs->ssgl[0].length;
			memcpy(rs->sbuf, ((void *) &iom) + rs->ssgl[0].length,
			       rs->ssgl[1].length);
			ret = rs_write_iomap(rs, iomr, rs->ssgl, 2, 0);
			rs->ssgl[0].addr = (uintptr_t) rs->sbuf + rs->ssgl[1].length;
		}
		dlist_remove(&iomr->entry);
		dlist_insert_tail(&iomr->entry, &rs->iomap_list);
		if (ret)
			break;
	}

	rs->iomap_pending = !dlist_empty(&rs->iomap_queue);
	fastlock_release(&rs->map_lock);
	return ret;
}

static ssize_t ds_sendv_udp(struct rsocket *rs, const struct iovec *iov,
			    int iovcnt, int flags, uint8_t op)
{
	struct ds_udp_header hdr;
	struct msghdr msg;
	struct iovec miov[8];
	ssize_t ret;

	if (iovcnt > 8)
		return ERR(ENOTSUP);

	hdr.tag = htobe32(DS_UDP_TAG);
	hdr.version = rs->conn_dest->qp->hdr.version;
	hdr.op = op;
	hdr.reserved = 0;
	hdr.qpn = htobe32(rs->conn_dest->qp->cm_id->qp->qp_num & 0xFFFFFF);
	if (rs->conn_dest->qp->hdr.version == 4) {
		hdr.length = DS_UDP_IPV4_HDR_LEN;
		hdr.addr.ipv4 = rs->conn_dest->qp->hdr.addr.ipv4;
	} else {
		hdr.length = DS_UDP_IPV6_HDR_LEN;
		memcpy(hdr.addr.ipv6, &rs->conn_dest->qp->hdr.addr.ipv6, 16);
	}

	miov[0].iov_base = &hdr;
	miov[0].iov_len = hdr.length;
	if (iov && iovcnt)
		memcpy(&miov[1], iov, sizeof(*iov) * iovcnt);

	memset(&msg, 0, sizeof msg);
	msg.msg_name = &rs->conn_dest->addr;
	msg.msg_namelen = ucma_addrlen(&rs->conn_dest->addr.sa);
	msg.msg_iov = miov;
	msg.msg_iovlen = iovcnt + 1;
	ret = sendmsg(rs->udp_sock, &msg, flags);
	return ret > 0 ? ret - hdr.length : ret;
}

static ssize_t ds_send_udp(struct rsocket *rs, const void *buf, size_t len,
			   int flags, uint8_t op)
{
	struct iovec iov;
	if (buf && len) {
		iov.iov_base = (void *) buf;
		iov.iov_len = len;
		return ds_sendv_udp(rs, &iov, 1, flags, op);
	} else {
		return ds_sendv_udp(rs, NULL, 0, flags, op);
	}
}

static ssize_t dsend(struct rsocket *rs, const void *buf, size_t len, int flags)
{
	struct ds_smsg *msg;
	struct ibv_sge sge;
	uint64_t offset;
	int ret = 0;

	if (!rs->conn_dest->ah)
		return ds_send_udp(rs, buf, len, flags, RS_OP_DATA);

	if (!ds_can_send(rs)) {
		ret = ds_get_comp(rs, rs_nonblocking(rs, flags), ds_can_send);
		if (ret)
			return ret;
	}

	msg = rs->smsg_free;
	rs->smsg_free = msg->next;
	rs->sqe_avail--;

	memcpy((void *) msg, &rs->conn_dest->qp->hdr, rs->conn_dest->qp->hdr.length);
	memcpy((void *) msg + rs->conn_dest->qp->hdr.length, buf, len);
	sge.addr = (uintptr_t) msg;
	sge.length = rs->conn_dest->qp->hdr.length + len;
	sge.lkey = rs->conn_dest->qp->smr->lkey;
	offset = (uint8_t *) msg - rs->sbuf;

	ret = ds_post_send(rs, &sge, offset);
	return ret ? ret : len;
}

/*
 * We overlap sending the data, by posting a small work request immediately,
 * then increasing the size of the send on each iteration.
 */
ssize_t rsend(int socket, const void *buf, size_t len, int flags)
{
	struct rsocket *rs;
	struct ibv_sge sge;
	size_t left = len;
	uint32_t xfer_size, olen = RS_OLAP_START_SIZE;// overlap 发送数据的起始大小，随着迭代次数增加，发送数据大小递增
	int ret = 0;

	rs = idm_at(&idm, socket);// 获取当前socket fd 对应的rsocket 实例
	if (!rs)
		return ERR(EBADF);
	if (rs->type == SOCK_DGRAM) {// udp
		fastlock_acquire(&rs->slock);
		ret = dsend(rs, buf, len, flags);
		fastlock_release(&rs->slock);
		return ret;
	}

	if (rs->state & rs_opening) {
		ret = rs_do_connect(rs);
		if (ret) {
			if (errno == EINPROGRESS)
				errno = EAGAIN;
			return ret;
		}
	}

	fastlock_acquire(&rs->slock);
	if (rs->iomap_pending) {
		ret = rs_send_iomaps(rs, flags);
		if (ret)
			goto out;
	}
	// rs->state 为connected 状态，可以进行数据发送
	// 使用left 记录待发送的数据长度，left 后续会更新为实际可发送的数据长度
	for (; left; left -= xfer_size, buf += xfer_size) {// 每循环一次后，left 减小xfer_size，buf 作为要发送数据的指针，向后移动xfer_size 个位置
		if (!rs_can_send(rs)) {// 若不满足发送条件
			ret = rs_get_comp(rs, rs_nonblocking(rs, flags),
					  rs_conn_can_send);// 获取recv cq channel 中的完成事件并进行处理
					  					// 获取过程中会update credits
										// rs_conn_can_send 判断是否满足发送条件，若满足则返回0；
										// 否则返回相关信息（ ibv_get_cq_event \ ibv_post_recv \ ibv_poll_cq 等的错误信息、EAGAIN等）
			if (ret)
				break;
			if (!(rs->state & rs_writable)) {// 若rs 不可写
				ret = ERR(ECONNRESET);// 将errno 设为 ECONNRESET 连接已被重置
				break;
			}
		}
// left 为待发送的数据长度
// 将olen 和 left 两者较小的值赋值给 xfer_size
		if (olen < left) {
			xfer_size = olen;
			if (olen < RS_MAX_TRANSFER)
				olen <<= 1;// olen 的值增加1倍 olen= olen*2
		} else {
			xfer_size = left;
		}
// 避免xfer_size 超过send buffer 可用字节 ，避免超过 target_sgl[] 长度
// 将xfer_size、rs->sbuf_bytes_avail、rs->target_sgl[rs->target_sge].length 三者中较小的值赋值给xfer_size
		if (xfer_size > rs->sbuf_bytes_avail)// 如果超过本机sbuf 空闲可使用的长度
			xfer_size = rs->sbuf_bytes_avail;
		if (xfer_size > rs->target_sgl[rs->target_sge].length)// 如果超过对端rbuf 可接收的长度
			xfer_size = rs->target_sgl[rs->target_sge].length;

		if (xfer_size <= rs->sq_inline) {// 当xfer_size 不大于 rs->sq_inline 时，使用rdma send inline 执行发送；否则使用rdma write with imm 发送
			sge.addr = (uintptr_t) buf;// buf 指向尚未发送的数据的起始地址
			sge.length = xfer_size;
			sge.lkey = 0;
			ret = rs_write_data(rs, &sge, 1, xfer_size, IBV_SEND_INLINE);
		} else if (xfer_size <= rs_sbuf_left(rs)) {// xfer_size 不大于sbuf 中的剩余空间大小
			memcpy((void *) (uintptr_t) rs->ssgl[0].addr, buf, xfer_size);// 将buf 中长度为xfer_size 的数据，复制到 ssgl[0].addr
			rs->ssgl[0].length = xfer_size;
			ret = rs_write_data(rs, rs->ssgl, 1, xfer_size, 0);// 执行发送，写入对端的rbuf 中，且不一定是写入到rmr 的起始地址；可能是写入到rmr 的中间某位置
			if (xfer_size < rs_sbuf_left(rs))// 如果 xfer_size 小于发送之前sbuf 中待发送的数据长度
				rs->ssgl[0].addr += xfer_size;// 向后移动ssgl[0].addr 指向本次发送完的下一个地址
			else
				rs->ssgl[0].addr = (uintptr_t) rs->sbuf;// 否则xfer_size 等于本次发送前sbuf 的待发送数据长度，本次发送完成后，ssgl[0].addr 重新回到sbuf 的起始位置
		} else {// 若 xfer_size > sq_inline 且xfer_size > sbuf中剩余空间大小
			rs->ssgl[0].length = rs_sbuf_left(rs);// ssgl[0].length 设为sbuf 中剩余空间大小
			memcpy((void *) (uintptr_t) rs->ssgl[0].addr, buf,
				rs->ssgl[0].length);// 将buf 中的待发送数据复制到 ssgl[0].addr 指向的地址处
			rs->ssgl[1].length = xfer_size - rs->ssgl[0].length;// ssgl[1].length 等于本次应发送的数据长度减去本次实际发送的数据长度
			memcpy(rs->sbuf, buf + rs->ssgl[0].length, rs->ssgl[1].length);// 将本次发送完之后buf 中尚未发送的数据，复制到sbuf 起始地址【由于xfer_size 小于sbuf 可用字节长度，因此将ssgl[1]循环指向sbuf 起始位置不会导致将ssgl[0]指向的数据覆盖的问题】
			ret = rs_write_data(rs, rs->ssgl, 2, xfer_size, 0);// 将ssgl[0]和ssgl[1] 对应的共xfer_size 大小的数据一次性发送出去
			rs->ssgl[0].addr = (uintptr_t) rs->sbuf + rs->ssgl[1].length;// 将ssgl[0].addr 更新为sbuf 起始地址向后便宜 ssgl[1].length 处的地址
		}
		if (ret)
			break;
	}
out:
	fastlock_release(&rs->slock);

	return (ret && left == len) ? ret : len - left;
}

ssize_t rsendto(int socket, const void *buf, size_t len, int flags,
		const struct sockaddr *dest_addr, socklen_t addrlen)
{
	struct rsocket *rs;
	int ret;

	rs = idm_at(&idm, socket);
	if (!rs)
		return ERR(EBADF);
	if (rs->type == SOCK_STREAM) {
		if (dest_addr || addrlen)
			return ERR(EISCONN);

		return rsend(socket, buf, len, flags);
	}

	if (rs->state == rs_init) {
		ret = ds_init_ep(rs);
		if (ret)
			return ret;
	}

	fastlock_acquire(&rs->slock);
	if (!rs->conn_dest || ds_compare_addr(dest_addr, &rs->conn_dest->addr)) {
		ret = ds_get_dest(rs, dest_addr, addrlen, &rs->conn_dest);
		if (ret)
			goto out;
	}

	ret = dsend(rs, buf, len, flags);
out:
	fastlock_release(&rs->slock);
	return ret;
}

static void rs_copy_iov(void *dst, const struct iovec **iov, size_t *offset, size_t len)
{
	size_t size;

	while (len) {
		size = (*iov)->iov_len - *offset;
		if (size > len) {
			memcpy (dst, (*iov)->iov_base + *offset, len);
			*offset += len;
			break;
		}

		memcpy(dst, (*iov)->iov_base + *offset, size);
		len -= size;
		dst += size;
		(*iov)++;
		*offset = 0;
	}
}

static ssize_t rsendv(int socket, const struct iovec *iov, int iovcnt, int flags)
{
	struct rsocket *rs;
	const struct iovec *cur_iov;
	size_t left, len, offset = 0;
	uint32_t xfer_size, olen = RS_OLAP_START_SIZE;
	int i, ret = 0;

	rs = idm_at(&idm, socket);
	if (!rs)
		return ERR(EBADF);
	if (rs->state & rs_opening) {
		ret = rs_do_connect(rs);
		if (ret) {
			if (errno == EINPROGRESS)
				errno = EAGAIN;
			return ret;
		}
	}

	cur_iov = iov;
	len = iov[0].iov_len;
	for (i = 1; i < iovcnt; i++)
		len += iov[i].iov_len;
	left = len;

	fastlock_acquire(&rs->slock);
	if (rs->iomap_pending) {
		ret = rs_send_iomaps(rs, flags);
		if (ret)
			goto out;
	}
	for (; left; left -= xfer_size) {
		if (!rs_can_send(rs)) {
			ret = rs_get_comp(rs, rs_nonblocking(rs, flags),
					  rs_conn_can_send);
			if (ret)
				break;
			if (!(rs->state & rs_writable)) {
				ret = ERR(ECONNRESET);
				break;
			}
		}

		if (olen < left) {
			xfer_size = olen;
			if (olen < RS_MAX_TRANSFER)
				olen <<= 1;
		} else {
			xfer_size = left;
		}

		if (xfer_size > rs->sbuf_bytes_avail)
			xfer_size = rs->sbuf_bytes_avail;
		if (xfer_size > rs->target_sgl[rs->target_sge].length)
			xfer_size = rs->target_sgl[rs->target_sge].length;

		if (xfer_size <= rs_sbuf_left(rs)) {
			rs_copy_iov((void *) (uintptr_t) rs->ssgl[0].addr,
				    &cur_iov, &offset, xfer_size);
			rs->ssgl[0].length = xfer_size;
			ret = rs_write_data(rs, rs->ssgl, 1, xfer_size,
					    xfer_size <= rs->sq_inline ? IBV_SEND_INLINE : 0);
			if (xfer_size < rs_sbuf_left(rs))
				rs->ssgl[0].addr += xfer_size;
			else
				rs->ssgl[0].addr = (uintptr_t) rs->sbuf;
		} else {
			rs->ssgl[0].length = rs_sbuf_left(rs);
			rs_copy_iov((void *) (uintptr_t) rs->ssgl[0].addr, &cur_iov,
				    &offset, rs->ssgl[0].length);
			rs->ssgl[1].length = xfer_size - rs->ssgl[0].length;
			rs_copy_iov(rs->sbuf, &cur_iov, &offset, rs->ssgl[1].length);
			ret = rs_write_data(rs, rs->ssgl, 2, xfer_size,
					    xfer_size <= rs->sq_inline ? IBV_SEND_INLINE : 0);
			rs->ssgl[0].addr = (uintptr_t) rs->sbuf + rs->ssgl[1].length;
		}
		if (ret)
			break;
	}
out:
	fastlock_release(&rs->slock);

	return (ret && left == len) ? ret : len - left;
}

ssize_t rsendmsg(int socket, const struct msghdr *msg, int flags)
{
	if (msg->msg_control && msg->msg_controllen)
		return ERR(ENOTSUP);

	return rsendv(socket, msg->msg_iov, (int) msg->msg_iovlen, flags);
}

ssize_t rwrite(int socket, const void *buf, size_t count)
{
	return rsend(socket, buf, count, 0);
}

ssize_t rwritev(int socket, const struct iovec *iov, int iovcnt)
{
	return rsendv(socket, iov, iovcnt, 0);
}

/* When mapping rpoll to poll, the events reported on the RDMA
 * fd are independent from the events rpoll may be looking for.
 * To avoid threads hanging in poll, whenever any event occurs,
 * we need to wakeup all threads in poll, so that they can check
 * if there has been a change on the rsockets they are monitoring.
 * To support this, we 'gate' threads entering and leaving rpoll.
 */
static int rs_pollinit(void)
{
	int ret = 0;

	pthread_mutex_lock(&mut);
	if (pollsignal >= 0)
		goto unlock;

	pollsignal = eventfd(0, EFD_NONBLOCK | EFD_SEMAPHORE);// 创建一个eventfd对象
	// eventfd通过一个进程间共享的64位计数器完成进程间通信，这个计数器由在linux内核空间维护
	// 用户可以通过调用write方法向内核空间写入一个64位的值，也可以调用read方法读取这个值。
	if (pollsignal < 0)
		ret = -errno;

unlock:
	pthread_mutex_unlock(&mut);
	return ret;
}

/* 进入rs poll ，直到 suspendpoll 为true时，将当前线程yield 并返回 -EBUSY
 * When an event occurs, we must wait until the state of all rsockets
 * has settled.  Then we need to re-check the rsocket state prior to
 * blocking on poll().
 * 
 * 当发生一个事件时，必须等待直到所有rsocket 的状态都稳定。然后在poll() 中阻塞之前，需要重新检查rsocket 的状态
 */
static int rs_poll_enter(void)
{
	pthread_mutex_lock(&mut);
	if (suspendpoll) {// 挂起poll
		pthread_mutex_unlock(&mut);
		sched_yield();// 会导致当前线程放弃CPU，进程管理系统会把该线程放到其对应优先级的CPU静态进程队列的尾端，然后一个新的线程会占用CPU。
		return -EBUSY;
	}
// suspendpoll 尚未更新为 1
	pollcnt++;// 全局变量计数+1
	pthread_mutex_unlock(&mut);
	return 0;
}

static void rs_poll_exit(void)
{
	uint64_t c;
	int save_errno;
	ssize_t ret;

	pthread_mutex_lock(&mut);
	if (!--pollcnt) {// pollcnt 当前为1
		/* Keep errno value from poll() call.  We try to clear
		 * a single signal.  But there's no guarantee that we'll
		 * find one.  Additional signals indicate that a change
		 * occurred on an rsocket, which requires all threads to
		 * re-check before blocking on poll.
		 * 
		 * 保存调用poll() 之后的errno 值。
		 * 我们尝试清理一个 single signal，但没办法保证一定可以找得到
		 * 附加的 signal 指示了一个rsocket 上发生的变化，需要所有线程调用poll() 并阻塞之前再次进行check
		 * 
		 */
		save_errno = errno;
		ret = read(pollsignal, &c, sizeof(c));// 读取pollsignal，再次唤醒所有rsocket 检查是否有对应事件； eventfd_read()设置了EFD_SEMAPHORE后，每次读取到的值都是1，且read后计数器也递减1。
		if (ret != sizeof(c))
			errno = save_errno;
		suspendpoll = 0;// 将suspendpoll 重置为 0
	}
	pthread_mutex_unlock(&mut);
}

/* When an event occurs, it's possible for a single thread blocked in
 * poll to return from the kernel, read the event, and update the state
 * of an rsocket.  However, that can leave threads blocked in the kernel
 * on poll (trying to read the CQ fd), which have had their rsocket
 * state set.  To avoid those threads remaining blocked in the kernel,
 * we must wake them up and ensure that they all return to user space,
 * in order to re-check the state of their rsockets.
 *
 * Because poll is racy wrt updating the rsocket states, we need to
 * signal state checks whenever a thread updates the state of a
 * monitored rsocket, independent of whether that thread actually
 * reads an event from an fd.  In other words, we must wake up all
 * polling threads whenever poll() indicates that there is a new
 * completion to process, and when rpoll() will return a successful
 * value after having blocked.
 */
static void rs_poll_stop(void)
{
	uint64_t c;
	int save_errno;
	ssize_t ret;

	/* See comment in rs_poll_exit */
	save_errno = errno;

	pthread_mutex_lock(&mut);
	if (!--pollcnt) {
		ret = read(pollsignal, &c, sizeof(c));
		suspendpoll = 0;
	} else if (!suspendpoll) {
		suspendpoll = 1;
		c = 1;
		ret = write(pollsignal, &c, sizeof(c));
	} else {
		ret = sizeof(c);
	}
	pthread_mutex_unlock(&mut);

	if (ret != sizeof(c))
		errno = save_errno;
}

static int rs_poll_signal(void)
{
	uint64_t c;
	ssize_t ret;

	pthread_mutex_lock(&mut);
	if (pollcnt && !suspendpoll) {
		suspendpoll = 1;
		c = 1;
		ret = write(pollsignal, &c, sizeof(c));
		if (ret == sizeof(c))
			ret = 0;
	} else {
		ret = 0;
	}
	pthread_mutex_unlock(&mut);
	return ret;
}

/* We always add the pollsignal read fd to the poll fd set, so
 * that we can signal any blocked threads.
 *
 * poll() 单个 process 就可以同时处理多个网络连接的IO
 * 为了让rpoll 实现类似于poll()的功能
 * 使用rfds 作为多个被I/O 阻塞的fd 所对应的pollfd 数组的指针
 * 同时为了可以在合适的时候主动唤醒被阻塞的线程，将pollsignal fd 加入到rfds 中
 * 当需要唤醒被阻塞的线程时，主动对pollsignal 进行read 或write 操作
 */
static struct pollfd *rs_fds_alloc(nfds_t nfds)
{// __thread 变量每一个线程有一份独立实体，各个线程的值互不干扰。可以用来修饰那些带有全局性且值可能变，但是又不值得用全局变量保护的变量
 // 线程内的全局变量
	static __thread struct pollfd *rfds;
	static __thread nfds_t rnfds;

	if (nfds + 1 > rnfds) {
		if (rfds)
			free(rfds);
		else if (rs_pollinit())
			return NULL;

		rfds = malloc(sizeof(*rfds) * nfds + 1);// 动态分配 rfds 内存空间
		rnfds = rfds ? nfds + 1 : 0;// rfds 内存分配成功，rnfds 值设为nfds+1，+1 是因为要给pollsignal 预留
	}

	if (rfds) {// rfds 已获得分配的内存空间
		rfds[nfds].fd = pollsignal; // 将rfds 最后一个元素的fd 设为 pollsignal
		rfds[nfds].events = POLLIN; // 将 pollsignal 关注的事件设为POLLIN
	}
	return rfds;
}

/* 尝试从rsocket 上poll 一些事件
 * 若成功poll 到事件，返回事件掩码
 * 若没有poll 到事件，返回0
 * 当连接为TCP 且已经连接或完成连接时，通过poll cq 并判断have_rdata 和 can_send 来手动设置 pollin 或 pollout
 * 当连接为TCP 但仍处理listening 时，对 accept_queue 存储的双工socket 对之一socket 0进行一次 poll() ，返回poll 结果
 * 参数 events 表示关注的事件类型
 */
static int rs_poll_rs(struct rsocket *rs, int events,
		      int nonblock, int (*test)(struct rsocket *rs))
{
	struct pollfd fds;
	short revents; // 进行poll 的fd 上实际获取到的事件类型
	int ret;

check_cq:
	if ((rs->type == SOCK_STREAM) && ((rs->state & rs_connected) ||
	     (rs->state == rs_disconnected) || (rs->state & rs_error))) {// 如果为 tcp 连接，并且 rs-> satte 状态为条件中三者之一
		rs_process_cq(rs, nonblock, test);// 由rs_poll_check() 或 rs_poll_event() 调用时， 尝试向对端更新credits，然后从CQ 中获取 1 次所有完成事件，再次尝试更新credits
										  // 由 rs_poll_arm() 调用时，更新credits，poll 所有cq，设置armed =1 ，再次更新credits，再次poll cq，返回0

		revents = 0;
		if ((events & POLLIN) && rs_conn_have_rdata(rs))// 判断传入的events 代表的事件类型，若为pollin 类型表示有数据可读，若同时确定存在数据可读
			revents |= POLLIN;	// revents 与 pollin 进行“或”操作，记录下pollin 类型
		if ((events & POLLOUT) && rs_can_send(rs))// 若判断传入的events 代表的事件类型为pollout，表示数据可写，若同时判断满足发送条件
			revents |= POLLOUT;	// revents 记录pollout 状态
		if (!(rs->state & rs_connected)) { // 若连接状态不是connected，使用revents 记录响应poll 类型
			if (rs->state == rs_disconnected)
				revents |= POLLHUP;// POLLHUP：对方描述符挂起
			else
				revents |= POLLERR;// 发生错误
		}

		return revents;
	} else if (rs->type == SOCK_DGRAM) {// udp 相关处理
		ds_process_cqs(rs, nonblock, test);

		revents = 0;
		if ((events & POLLIN) && rs_have_rdata(rs))
			revents |= POLLIN;
		if ((events & POLLOUT) && ds_can_send(rs))
			revents |= POLLOUT;

		return revents;
	}

	if (rs->state == rs_listening) { // tcp，但状态不是connected，disconnected或者 error，而是正在监听
		fds.fd = rs->accept_queue[0];// 将创建的socket 0 赋值给 fds.fd，接下来会对其进行poll 获取事件
		fds.events = events;// 将调用rs_poll_rs() 时传入的events 作为关注的事件类型赋值给fds.events
		fds.revents = 0;
		poll(&fds, 1, 0);// 获取 socket 0 上的事件
		return fds.revents;// 返回fds.fd 上获取到的事件类型
	}

	if (rs->state & rs_opening) {// tcp通信，但状态尚处在opening
		ret = rs_do_connect(rs);
		if (ret && (errno == EINPROGRESS)) {
			errno = 0;
		} else {
			goto check_cq;
		}
	}

	if (rs->state == rs_connect_error) {
		revents = 0;
		if (events & POLLOUT)
			revents |= POLLOUT;
		if (events & POLLIN)
			revents |= POLLIN;
		revents |= POLLERR;
		return revents;
	}

	return 0;
}

/* rpoll 中首先执行一次poll check，尝试获取所有rs 上的事件
 * 若能获取到则返回存在事件的fd 个数
 * 否则返回0
 */
static int rs_poll_check(struct pollfd *fds, nfds_t nfds)
{
	struct rsocket *rs;
	int i, cnt = 0;

	for (i = 0; i < nfds; i++) {
		rs = idm_lookup(&idm, fds[i].fd);// 获取 fds 中所有元素fd 对应的rsocket 实例
		if (rs)
			fds[i].revents = rs_poll_rs(rs, fds[i].events, 1, rs_poll_all);// 当存在fd 对应的 rsocket 时，使用rs_poll_rs 尝试获取事件
		else
			poll(&fds[i], 1, 0);// 当fd 不存在对应rsocket 实例时，直接调用poll() 从fd 上获取事件

		if (fds[i].revents)// 如果能够获取到事件，则事件类型记录在 revents 
			cnt++;
	}
	return cnt;
}

/*
 * 根据 rs 及rs->state 将需要继续关注的fd 加入 rfds，并将关注的事件类型设为POLLIN
 * 正常执行返回0；
 * 若获取到fds 中fd 上的事件，返回1
 */
static int rs_poll_arm(struct pollfd *rfds, struct pollfd *fds, nfds_t nfds)
{
	struct rsocket *rs;
	int i;
	for (i = 0; i < nfds; i++) {
		rs = idm_lookup(&idm, fds[i].fd);
		if (rs) {
			fds[i].revents = rs_poll_rs(rs, fds[i].events, 0, rs_is_cq_armed);// 判断当前是否能够从fds 的所有fd 上获取到事件
			if (fds[i].revents)// 若获取到某个fd 上的事件(其他fd 不被rearm 如何保证其他fd 不会饥饿)
				return 1;	   // 无须arm 直接返回
			// {
			// 	s++;
			// 	continue;
			// }	

// 未从当前fd 中获取到事件，根据rs 状态判断将哪个fd 放入rfds 中进行事件监听
			if (rs->type == SOCK_STREAM) { // 当连接为tcp 时
				if (rs->state >= rs_connected)// 当rs 连接状态为已连接，或者其他连接完成后的状态时
					rfds[i].fd = rs->cm_id->recv_cq_channel->fd;// 此时需要监听recv cq channel 上的事件，将 recv_cq_channel-> fd 作为需要监听事件的fd，加入到 rfds 中，监听cq 事件
				else
					rfds[i].fd = rs->cm_id->channel->fd;// 否则rs 尚未完成连接的建立，将cm_id-> channel-> fd 作为需要继续监听的fd，加入到rfds 中，监听cm 事件
			} else {
				rfds[i].fd = rs->epfd;// udp
			}
			rfds[i].events = POLLIN;// 将fd 关注的事件类型设为 POLLIN，因为rdma 只产生 POLLIN 事件
		} else {// 若rsocket 实例不存在
			rfds[i].fd = fds[i].fd;// 直接监听 fds[].fd
			rfds[i].events = fds[i].events;
		}
		rfds[i].revents = 0;
	}
	// return s;
	return 0;
}

// 针对rfds 中所有 fds，获取 1 次当前CQ 中所有事件
// 并再次poll rs ，返回poll 到事件的fd 个数
static int rs_poll_events(struct pollfd *rfds, struct pollfd *fds, nfds_t nfds)
{
	struct rsocket *rs;
	int i, cnt = 0;

	for (i = 0; i < nfds; i++) {
		rs = idm_lookup(&idm, fds[i].fd);
		if (rs) {
			if (rfds[i].revents) {// 若rsocket 存在事件产生
				fastlock_acquire(&rs->cq_wait_lock);
				if (rs->type == SOCK_STREAM)
					rs_get_cq_event(rs);// 获取 cq 事件
				else
					ds_get_cq_event(rs);
				fastlock_release(&rs->cq_wait_lock);
			}
			fds[i].revents = rs_poll_rs(rs, fds[i].events, 1, rs_poll_all);// 处理完cq event 现有事件后，再次执行poll rs
		} else {
			fds[i].revents = rfds[i].revents;
		}
		if (fds[i].revents)// 如果再次获取到事件，计数器+1
			cnt++;
	}
	return cnt;// 返回处理完当前事件后，再次获取到事件的fd 个数
}

/*
 * We need to poll *all* fd's that the user specifies at least once.
 * Note that we may receive events on an rsocket that may not be reported
 * to the user (e.g. connection events or credit updates).  Process those
 * events, then return to polling until we find ones of interest.
 * 需要将所有用户指定的 fd 至少poll 一次
 * 需要注意，可能会在rsocket 接收到不会报告给用户的事件（例如 连接事件或更新credits 事件）
 * 处理那些事件，并在获取到下一个感兴趣的事件之前持续polling
 */
int rpoll(struct pollfd *fds, nfds_t nfds, int timeout)
{
	struct pollfd *rfds;
	uint64_t start_time = 0;
	uint32_t poll_time;
	int pollsleep, ret;

	do {
		ret = rs_poll_check(fds, nfds);	// 首先检查一次所有fds数组中fd 上当前能够获取到的事件，保证至少对fd poll 一次
		if (ret || !timeout)// 若成功获取到了事件，会得到产生了事件的 fd 的个数；否则当timeout 为0时，直接返回
			return ret;		// ret 可能为产生了事件的fd 个数；也可能由于超时没有获取到事件而为0

		if (!start_time)
			start_time = rs_time_us();

		poll_time = (uint32_t) (rs_time_us() - start_time);
	} while (poll_time <= polling_time);

// poll_time 超时且没有获取到事件
	rfds = rs_fds_alloc(nfds);// 创建rfds 记录pollfd 数组
	if (!rfds)// rfds 新建失败
		return ERR(ENOMEM);

	do {
		ret = rs_poll_arm(rfds, fds, nfds);// 将rsocket 的cm fd 或 recv cq channel fd 加入到rfds 数组
		if (ret)// 若已经可以从rfds 中poll 到某个fd 上发生的事件
			break; // 退出do-while 循环，并返回1
// rfds 中已加入需要监听事件的fd，且截至目前没有poll 到任何事件
		if (rs_poll_enter())// 将pollcnt +1，直到 suspendpoll 标志为 1 时，将当前线程yield，并返回-EBUSY
			continue;
// suspendpoll 标志为1
		if (timeout >= 0) {
			timeout -= (int) ((rs_time_us() - start_time) / 1000);
			if (timeout <= 0)
				return 0;// 判断若timeout 超时，返回0
			pollsleep = min(timeout, wake_up_interval);
		} else {
			pollsleep = wake_up_interval;	// 若timeout == -1，定期唤醒poll
		}

		ret = poll(rfds, nfds + 1, pollsleep);// 使用系统调用poll() 获取rfds 中产生事件的fd 的个数
		if (ret < 0) {// ret == -1，poll 出错
			rs_poll_exit();// 出错后执行rs poll 退出，退出前通过signalpoll 再次唤醒所有rsocket 检查是否有事件
			break; // 退出do-while 循环
		}
// 若系统调用poll 正常返回
		ret = rs_poll_events(rfds, fds, nfds);
		rs_poll_stop();
	} while (!ret);

	return ret;
}

static struct pollfd *
rs_select_to_poll(int *nfds, fd_set *readfds, fd_set *writefds, fd_set *exceptfds)
{
	struct pollfd *fds;
	int fd, i = 0;

	fds = calloc(*nfds, sizeof(*fds));
	if (!fds)
		return NULL;

	for (fd = 0; fd < *nfds; fd++) {
		if (readfds && FD_ISSET(fd, readfds)) {
			fds[i].fd = fd;
			fds[i].events = POLLIN;
		}

		if (writefds && FD_ISSET(fd, writefds)) {
			fds[i].fd = fd;
			fds[i].events |= POLLOUT;
		}

		if (exceptfds && FD_ISSET(fd, exceptfds))
			fds[i].fd = fd;

		if (fds[i].fd)
			i++;
	}

	*nfds = i;
	return fds;
}

static int
rs_poll_to_select(int nfds, struct pollfd *fds, fd_set *readfds,
		  fd_set *writefds, fd_set *exceptfds)
{
	int i, cnt = 0;

	for (i = 0; i < nfds; i++) {
		if (readfds && (fds[i].revents & (POLLIN | POLLHUP))) {
			FD_SET(fds[i].fd, readfds);
			cnt++;
		}

		if (writefds && (fds[i].revents & POLLOUT)) {
			FD_SET(fds[i].fd, writefds);
			cnt++;
		}

		if (exceptfds && (fds[i].revents & ~(POLLIN | POLLOUT))) {
			FD_SET(fds[i].fd, exceptfds);
			cnt++;
		}
	}
	return cnt;
}

static int rs_convert_timeout(struct timeval *timeout)
{
	return !timeout ? -1 :
		timeout->tv_sec * 1000 + timeout->tv_usec / 1000;
}

int rselect(int nfds, fd_set *readfds, fd_set *writefds,
	    fd_set *exceptfds, struct timeval *timeout)
{
	struct pollfd *fds;
	int ret;

	fds = rs_select_to_poll(&nfds, readfds, writefds, exceptfds);
	if (!fds)
		return ERR(ENOMEM);

	ret = rpoll(fds, nfds, rs_convert_timeout(timeout));

	if (readfds)
		FD_ZERO(readfds);
	if (writefds)
		FD_ZERO(writefds);
	if (exceptfds)
		FD_ZERO(exceptfds);

	if (ret > 0)
		ret = rs_poll_to_select(nfds, fds, readfds, writefds, exceptfds);

	free(fds);
	return ret;
}

/*
 * For graceful disconnect, notify the remote side that we're
 * disconnecting and wait until all outstanding sends complete, provided
 * that the remote side has not sent a disconnect message.
 */
int rshutdown(int socket, int how)
{
	struct rsocket *rs;
	int ctrl, ret = 0;

	rs = idm_lookup(&idm, socket);
	if (!rs)
		return ERR(EBADF);
	if (rs->opts & RS_OPT_KEEPALIVE)
		rs_notify_svc(&tcp_svc, rs, RS_SVC_REM_KEEPALIVE);

	if (rs->fd_flags & O_NONBLOCK)
		rs_set_nonblocking(rs, 0);

	if (rs->state & rs_connected) {
		if (how == SHUT_RDWR) {
			ctrl = RS_CTRL_DISCONNECT;
			rs->state &= ~(rs_readable | rs_writable);
		} else if (how == SHUT_WR) {
			rs->state &= ~rs_writable;
			ctrl = (rs->state & rs_readable) ?
				RS_CTRL_SHUTDOWN : RS_CTRL_DISCONNECT;
		} else {
			rs->state &= ~rs_readable;
			if (rs->state & rs_writable)
				goto out;
			ctrl = RS_CTRL_DISCONNECT;
		}
		if (!rs_ctrl_avail(rs)) {
			ret = rs_process_cq(rs, 0, rs_conn_can_send_ctrl);
			if (ret)
				goto out;
		}

		if ((rs->state & rs_connected) && rs_ctrl_avail(rs)) {
			rs->ctrl_seqno++;
			ret = rs_post_msg(rs, rs_msg_set(RS_OP_CTRL, ctrl));
		}
	}

	if (rs->state & rs_connected)
		rs_process_cq(rs, 0, rs_conn_all_sends_done);

out:
	if ((rs->fd_flags & O_NONBLOCK) && (rs->state & rs_connected))
		rs_set_nonblocking(rs, rs->fd_flags);

	if (rs->state & rs_disconnected) {
		/* Generate event by flushing receives to unblock rpoll */
		ibv_req_notify_cq(rs->cm_id->recv_cq, 0);
		ucma_shutdown(rs->cm_id);
	}

	return ret;
}

static void ds_shutdown(struct rsocket *rs)
{
	if (rs->opts & RS_OPT_UDP_SVC)
		rs_notify_svc(&udp_svc, rs, RS_SVC_REM_DGRAM);

	if (rs->fd_flags & O_NONBLOCK)
		rs_set_nonblocking(rs, 0);

	rs->state &= ~(rs_readable | rs_writable);
	ds_process_cqs(rs, 0, ds_all_sends_done);

	if (rs->fd_flags & O_NONBLOCK)
		rs_set_nonblocking(rs, rs->fd_flags);
}

int rclose(int socket)
{
	struct rsocket *rs;

	rs = idm_lookup(&idm, socket);
	if (!rs)
		return EBADF;
	if (rs->type == SOCK_STREAM) {
		if (rs->state & rs_connected)
			rshutdown(socket, SHUT_RDWR);
		if (rs->opts & RS_OPT_KEEPALIVE)
			rs_notify_svc(&tcp_svc, rs, RS_SVC_REM_KEEPALIVE);
		if (rs->opts & RS_OPT_CM_SVC && rs->state == rs_listening)
			rs_notify_svc(&listen_svc, rs, RS_SVC_REM_CM);
		if (rs->opts & RS_OPT_CM_SVC){
			rs_notify_svc(&accept_svc, rs, RS_SVC_REM_CM);
			rs_notify_svc(&connect_svc, rs, RS_SVC_REM_CM);
		}
	} else {
		ds_shutdown(rs);
	}

	rs_free(rs);
	return 0;
}

static void rs_copy_addr(struct sockaddr *dst, struct sockaddr *src, socklen_t *len)
{
	socklen_t size;

	if (src->sa_family == AF_INET) {
		size = min_t(socklen_t, *len, sizeof(struct sockaddr_in));
		*len = sizeof(struct sockaddr_in);
	} else {
		size = min_t(socklen_t, *len, sizeof(struct sockaddr_in6));
		*len = sizeof(struct sockaddr_in6);
	}
	memcpy(dst, src, size);
}

int rgetpeername(int socket, struct sockaddr *addr, socklen_t *addrlen)
{
	struct rsocket *rs;

	rs = idm_lookup(&idm, socket);
	if (!rs)
		return ERR(EBADF);
	if (rs->type == SOCK_STREAM) {
		rs_copy_addr(addr, rdma_get_peer_addr(rs->cm_id), addrlen);
		return 0;
	} else {
		return getpeername(rs->udp_sock, addr, addrlen);
	}
}

int rgetsockname(int socket, struct sockaddr *addr, socklen_t *addrlen)
{
	struct rsocket *rs;

	rs = idm_lookup(&idm, socket);
	if (!rs)
		return ERR(EBADF);
	if (rs->type == SOCK_STREAM) {
		rs_copy_addr(addr, rdma_get_local_addr(rs->cm_id), addrlen);
		return 0;
	} else {
		return getsockname(rs->udp_sock, addr, addrlen);
	}
}

static int rs_set_keepalive(struct rsocket *rs, int on)
{
	FILE *f;
	int ret;

	if ((on && (rs->opts & RS_OPT_KEEPALIVE)) ||
	    (!on && !(rs->opts & RS_OPT_KEEPALIVE)))
		return 0;

	if (on) {
		if (!rs->keepalive_time) {
			if ((f = fopen("/proc/sys/net/ipv4/tcp_keepalive_time", "r"))) {
				if (fscanf(f, "%u", &rs->keepalive_time) != 1)
					rs->keepalive_time = 7200;
				fclose(f);
			} else {
				rs->keepalive_time = 7200;
			}
		}
		ret = rs_notify_svc(&tcp_svc, rs, RS_SVC_ADD_KEEPALIVE);
	} else {
		ret = rs_notify_svc(&tcp_svc, rs, RS_SVC_REM_KEEPALIVE);
	}

	return ret;
}

int rsetsockopt(int socket, int level, int optname,
		const void *optval, socklen_t optlen)
{
	struct rsocket *rs;
	int ret, opt_on = 0;
	uint64_t *opts = NULL;

	ret = ERR(ENOTSUP);
	rs = idm_lookup(&idm, socket);
	if (!rs)
		return ERR(EBADF);
	if (rs->type == SOCK_DGRAM && level != SOL_RDMA) {
		ret = setsockopt(rs->udp_sock, level, optname, optval, optlen);
		if (ret)
			return ret;
	}

	switch (level) {
	case SOL_SOCKET:
		opts = &rs->so_opts;
		switch (optname) {
		case SO_REUSEADDR:
			if (rs->type == SOCK_STREAM) {
				ret = rdma_set_option(rs->cm_id, RDMA_OPTION_ID,
						      RDMA_OPTION_ID_REUSEADDR,
						      (void *) optval, optlen);
				if (ret && ((errno == ENOSYS) || ((rs->state != rs_init) &&
				    rs->cm_id->context &&
				    (rs->cm_id->verbs->device->transport_type == IBV_TRANSPORT_IB))))
					ret = 0;
			}
			opt_on = *(int *) optval;
			break;
		case SO_RCVBUF:
			if ((rs->type == SOCK_STREAM && !rs->rbuf) ||
			    (rs->type == SOCK_DGRAM && !rs->qp_list))
				rs->rbuf_size = (*(uint32_t *) optval) << 1;
			ret = 0;
			break;
		case SO_SNDBUF:
			if (!rs->sbuf)
				rs->sbuf_size = (*(uint32_t *) optval) << 1;
			if (rs->sbuf_size < RS_SNDLOWAT)
				rs->sbuf_size = RS_SNDLOWAT << 1;
			ret = 0;
			break;
		case SO_LINGER:
			/* Invert value so default so_opt = 0 is on */
			opt_on =  !((struct linger *) optval)->l_onoff;
			ret = 0;
			break;
		case SO_KEEPALIVE:
			ret = rs_set_keepalive(rs, *(int *) optval);
			opt_on = rs->opts & RS_OPT_KEEPALIVE;
			break;
		case SO_OOBINLINE:
			opt_on = *(int *) optval;
			ret = 0;
			break;
		default:
			break;
		}
		break;
	case IPPROTO_TCP:
		opts = &rs->tcp_opts;
		switch (optname) {
		case TCP_KEEPCNT:
		case TCP_KEEPINTVL:
			ret = 0;   /* N/A - we're using a reliable connection */
			break;
		case TCP_KEEPIDLE:
			if (*(int *) optval <= 0) {
				ret = ERR(EINVAL);
				break;
			}
			rs->keepalive_time = *(int *) optval;
			ret = (rs->opts & RS_OPT_KEEPALIVE) ?
			      rs_notify_svc(&tcp_svc, rs, RS_SVC_MOD_KEEPALIVE) : 0;
			break;
		case TCP_NODELAY:
			opt_on = *(int *) optval;
			ret = 0;
			break;
		case TCP_MAXSEG:
			ret = 0;
			break;
		default:
			break;
		}
		break;
	case IPPROTO_IPV6:
		opts = &rs->ipv6_opts;
		switch (optname) {
		case IPV6_V6ONLY:
			if (rs->type == SOCK_STREAM) {
				ret = rdma_set_option(rs->cm_id, RDMA_OPTION_ID,
						      RDMA_OPTION_ID_AFONLY,
						      (void *) optval, optlen);
			}
			opt_on = *(int *) optval;
			break;
		default:
			break;
		}
		break;
	case SOL_RDMA:
		if (rs->state >= rs_opening) {
			ret = ERR(EINVAL);
			break;
		}

		switch (optname) {
		case RDMA_SQSIZE:
			rs->sq_size = min_t(uint32_t, (*(uint32_t *)optval),
					    RS_QP_MAX_SIZE);
			ret = 0;
			break;
		case RDMA_RQSIZE:
			rs->rq_size = min_t(uint32_t, (*(uint32_t *)optval),
					    RS_QP_MAX_SIZE);
			ret = 0;
			break;
		case RDMA_INLINE:
			rs->sq_inline = min_t(uint32_t, *(uint32_t *)optval,
					      RS_QP_MAX_SIZE);
			ret = 0;
			break;
		case RDMA_IOMAPSIZE:
			rs->target_iomap_size = (uint16_t) rs_scale_to_value(
				(uint8_t) rs_value_to_scale(*(int *) optval, 8), 8);
			ret = 0;
			break;
		case RDMA_ROUTE:
			if ((rs->optval = malloc(optlen))) {
				memcpy(rs->optval, optval, optlen);
				rs->optlen = optlen;
				ret = 0;
			} else {
				ret = ERR(ENOMEM);
			}
			break;
		default:
			break;
		}
		break;
	default:
		break;
	}

	if (!ret && opts) {
		if (opt_on)
			*opts |= (1 << optname);
		else
			*opts &= ~(1 << optname);
	}

	return ret;
}

static void rs_convert_sa_path(struct ibv_sa_path_rec *sa_path,
			       struct ibv_path_data *path_data)
{
	uint32_t fl_hop;

	memset(path_data, 0, sizeof(*path_data));
	path_data->path.dgid = sa_path->dgid;
	path_data->path.sgid = sa_path->sgid;
	path_data->path.dlid = sa_path->dlid;
	path_data->path.slid = sa_path->slid;
	fl_hop = be32toh(sa_path->flow_label) << 8;
	path_data->path.flowlabel_hoplimit = htobe32(fl_hop | sa_path->hop_limit);
	path_data->path.tclass = sa_path->traffic_class;
	path_data->path.reversible_numpath = sa_path->reversible << 7 | 1;
	path_data->path.pkey = sa_path->pkey;
	path_data->path.qosclass_sl = htobe16(sa_path->sl);
	path_data->path.mtu = sa_path->mtu | 2 << 6;	/* exactly */
	path_data->path.rate = sa_path->rate | 2 << 6;
	path_data->path.packetlifetime = sa_path->packet_life_time | 2 << 6;
	path_data->flags= sa_path->preference;
}

int rgetsockopt(int socket, int level, int optname,
		void *optval, socklen_t *optlen)
{
	struct rsocket *rs;
	void *opt;
	struct ibv_sa_path_rec *path_rec;
	struct ibv_path_data path_data;
	socklen_t len;
	int ret = 0;
	int num_paths;

	rs = idm_lookup(&idm, socket);
	if (!rs)
		return ERR(EBADF);
	switch (level) {
	case SOL_SOCKET:
		switch (optname) {
		case SO_REUSEADDR:
		case SO_KEEPALIVE:
		case SO_OOBINLINE:
			*((int *) optval) = !!(rs->so_opts & (1 << optname));
			*optlen = sizeof(int);
			break;
		case SO_RCVBUF:
			*((int *) optval) = rs->rbuf_size;
			*optlen = sizeof(int);
			break;
		case SO_SNDBUF:
			*((int *) optval) = rs->sbuf_size;
			*optlen = sizeof(int);
			break;
		case SO_LINGER:
			/* Value is inverted so default so_opt = 0 is on */
			((struct linger *) optval)->l_onoff =
					!(rs->so_opts & (1 << optname));
			((struct linger *) optval)->l_linger = 0;
			*optlen = sizeof(struct linger);
			break;
		case SO_ERROR:
			*((int *) optval) = rs->err;
			*optlen = sizeof(int);
			rs->err = 0;
			break;
		default:
			ret = ENOTSUP;
			break;
		}
		break;
	case IPPROTO_TCP:
		switch (optname) {
		case TCP_KEEPCNT:
		case TCP_KEEPINTVL:
			*((int *) optval) = 1;   /* N/A */
			break;
		case TCP_KEEPIDLE:
			*((int *) optval) = (int) rs->keepalive_time;
			*optlen = sizeof(int);
			break;
		case TCP_NODELAY:
			*((int *) optval) = !!(rs->tcp_opts & (1 << optname));
			*optlen = sizeof(int);
			break;
		case TCP_MAXSEG:
			*((int *) optval) = (rs->cm_id && rs->cm_id->route.num_paths) ?
					    1 << (7 + rs->cm_id->route.path_rec->mtu) :
					    2048;
			*optlen = sizeof(int);
			break;
		default:
			ret = ENOTSUP;
			break;
		}
		break;
	case IPPROTO_IPV6:
		switch (optname) {
		case IPV6_V6ONLY:
			*((int *) optval) = !!(rs->ipv6_opts & (1 << optname));
			*optlen = sizeof(int);
			break;
		default:
			ret = ENOTSUP;
			break;
		}
		break;
	case SOL_RDMA:
		switch (optname) {
		case RDMA_SQSIZE:
			*((int *) optval) = rs->sq_size;
			*optlen = sizeof(int);
			break;
		case RDMA_RQSIZE:
			*((int *) optval) = rs->rq_size;
			*optlen = sizeof(int);
			break;
		case RDMA_INLINE:
			*((int *) optval) = rs->sq_inline;
			*optlen = sizeof(int);
			break;
		case RDMA_IOMAPSIZE:
			*((int *) optval) = rs->target_iomap_size;
			*optlen = sizeof(int);
			break;
		case RDMA_ROUTE:
			if (rs->optval) {
				if (*optlen < rs->optlen) {
					ret = EINVAL;
				} else {
					memcpy(rs->optval, optval, rs->optlen);
					*optlen = rs->optlen;
				}
			} else {
				if (*optlen < sizeof(path_data)) {
					ret = EINVAL;
				} else {
					len = 0;
					opt = optval;
					path_rec = rs->cm_id->route.path_rec;
					num_paths = 0;
					while (len + sizeof(path_data) <= *optlen &&
					       num_paths < rs->cm_id->route.num_paths) {
						rs_convert_sa_path(path_rec, &path_data);
						memcpy(opt, &path_data, sizeof(path_data));
						len += sizeof(path_data);
						opt += sizeof(path_data);
						path_rec++;
						num_paths++;
					}
					*optlen = len;
					ret = 0;
				}
			}
			break;
		default:
			ret = ENOTSUP;
			break;
		}
		break;
	default:
		ret = ENOTSUP;
		break;
	}

	return rdma_seterrno(ret);
}

int rfcntl(int socket, int cmd, ... /* arg */ )
{
	struct rsocket *rs;
	va_list args;
	int param;
	int ret = 0;

	rs = idm_lookup(&idm, socket);
	if (!rs)
		return ERR(EBADF);
	va_start(args, cmd);
	switch (cmd) {
	case F_GETFL:
		ret = rs->fd_flags;
		break;
	case F_SETFL:
		param = va_arg(args, int);
		if ((rs->fd_flags & O_NONBLOCK) != (param & O_NONBLOCK))
			ret = rs_set_nonblocking(rs, param & O_NONBLOCK);

		if (!ret)
			rs->fd_flags = param;
		break;
	default:
		ret = ERR(ENOTSUP);
		break;
	}
	va_end(args);
	return ret;
}

static struct rs_iomap_mr *rs_get_iomap_mr(struct rsocket *rs)
{
	int i;

	if (!rs->remote_iomappings) {
		rs->remote_iomappings = calloc(rs->remote_iomap.length,
					       sizeof(*rs->remote_iomappings));
		if (!rs->remote_iomappings)
			return NULL;

		for (i = 0; i < rs->remote_iomap.length; i++)
			rs->remote_iomappings[i].index = i;
	}

	for (i = 0; i < rs->remote_iomap.length; i++) {
		if (!rs->remote_iomappings[i].mr)
			return &rs->remote_iomappings[i];
	}
	return NULL;
}

/*
 * If an offset is given, we map to it.  If offset is -1, then we map the
 * offset to the address of buf.  We do not check for conflicts, which must
 * be fixed at some point.
 */
off_t riomap(int socket, void *buf, size_t len, int prot, int flags, off_t offset)
{
	struct rsocket *rs;
	struct rs_iomap_mr *iomr;
	int access = IBV_ACCESS_LOCAL_WRITE;

	rs = idm_at(&idm, socket);
	if (!rs)
		return ERR(EBADF);
	if (!rs->cm_id->pd || (prot & ~(PROT_WRITE | PROT_NONE)))
		return ERR(EINVAL);

	fastlock_acquire(&rs->map_lock);
	if (prot & PROT_WRITE) {
		iomr = rs_get_iomap_mr(rs);
		access |= IBV_ACCESS_REMOTE_WRITE;
	} else {
		iomr = calloc(1, sizeof(*iomr));
		iomr->index = -1;
	}
	if (!iomr) {
		offset = ERR(ENOMEM);
		goto out;
	}

	iomr->mr = ibv_reg_mr(rs->cm_id->pd, buf, len, access);
	if (!iomr->mr) {
		if (iomr->index < 0)
			free(iomr);
		offset = -1;
		goto out;
	}

	if (offset == -1)
		offset = (uintptr_t) buf;
	iomr->offset = offset;
	atomic_store(&iomr->refcnt, 1);

	if (iomr->index >= 0) {
		dlist_insert_tail(&iomr->entry, &rs->iomap_queue);
		rs->iomap_pending = 1;
	} else {
		dlist_insert_tail(&iomr->entry, &rs->iomap_list);
	}
out:
	fastlock_release(&rs->map_lock);
	return offset;
}

int riounmap(int socket, void *buf, size_t len)
{
	struct rsocket *rs;
	struct rs_iomap_mr *iomr;
	dlist_entry *entry;
	int ret = 0;

	rs = idm_at(&idm, socket);
	if (!rs)
		return ERR(EBADF);
	fastlock_acquire(&rs->map_lock);

	for (entry = rs->iomap_list.next; entry != &rs->iomap_list;
	     entry = entry->next) {
		iomr = container_of(entry, struct rs_iomap_mr, entry);
		if (iomr->mr->addr == buf && iomr->mr->length == len) {
			rs_release_iomap_mr(iomr);
			goto out;
		}
	}

	for (entry = rs->iomap_queue.next; entry != &rs->iomap_queue;
	     entry = entry->next) {
		iomr = container_of(entry, struct rs_iomap_mr, entry);
		if (iomr->mr->addr == buf && iomr->mr->length == len) {
			rs_release_iomap_mr(iomr);
			goto out;
		}
	}
	ret = ERR(EINVAL);
out:
	fastlock_release(&rs->map_lock);
	return ret;
}

static struct rs_iomap *rs_find_iomap(struct rsocket *rs, off_t offset)
{
	int i;

	for (i = 0; i < rs->target_iomap_size; i++) {
		if (offset >= rs->target_iomap[i].offset &&
		    offset < rs->target_iomap[i].offset + rs->target_iomap[i].sge.length)
			return &rs->target_iomap[i];
	}
	return NULL;
}

size_t riowrite(int socket, const void *buf, size_t count, off_t offset, int flags)
{
	struct rsocket *rs;
	struct rs_iomap *iom = NULL;
	struct ibv_sge sge;
	size_t left = count;
	uint32_t xfer_size, olen = RS_OLAP_START_SIZE;
	int ret = 0;

	rs = idm_at(&idm, socket);
	if (!rs)
		return ERR(EBADF);
	fastlock_acquire(&rs->slock);
	if (rs->iomap_pending) {
		ret = rs_send_iomaps(rs, flags);
		if (ret)
			goto out;
	}
	for (; left; left -= xfer_size, buf += xfer_size, offset += xfer_size) {
		if (!iom || offset > iom->offset + iom->sge.length) {
			iom = rs_find_iomap(rs, offset);
			if (!iom)
				break;
		}

		if (!rs_can_send(rs)) {
			ret = rs_get_comp(rs, rs_nonblocking(rs, flags),
					  rs_conn_can_send);
			if (ret)
				break;
			if (!(rs->state & rs_writable)) {
				ret = ERR(ECONNRESET);
				break;
			}
		}

		if (olen < left) {
			xfer_size = olen;
			if (olen < RS_MAX_TRANSFER)
				olen <<= 1;
		} else {
			xfer_size = left;
		}

		if (xfer_size > rs->sbuf_bytes_avail)
			xfer_size = rs->sbuf_bytes_avail;
		if (xfer_size > iom->offset + iom->sge.length - offset)
			xfer_size = iom->offset + iom->sge.length - offset;

		if (xfer_size <= rs->sq_inline) {
			sge.addr = (uintptr_t) buf;
			sge.length = xfer_size;
			sge.lkey = 0;
			ret = rs_write_direct(rs, iom, offset, &sge, 1,
					      xfer_size, IBV_SEND_INLINE);
		} else if (xfer_size <= rs_sbuf_left(rs)) {
			memcpy((void *) (uintptr_t) rs->ssgl[0].addr, buf, xfer_size);
			rs->ssgl[0].length = xfer_size;
			ret = rs_write_direct(rs, iom, offset, rs->ssgl, 1, xfer_size, 0);
			if (xfer_size < rs_sbuf_left(rs))
				rs->ssgl[0].addr += xfer_size;
			else
				rs->ssgl[0].addr = (uintptr_t) rs->sbuf;
		} else {
			rs->ssgl[0].length = rs_sbuf_left(rs);
			memcpy((void *) (uintptr_t) rs->ssgl[0].addr, buf,
				rs->ssgl[0].length);
			rs->ssgl[1].length = xfer_size - rs->ssgl[0].length;
			memcpy(rs->sbuf, buf + rs->ssgl[0].length, rs->ssgl[1].length);
			ret = rs_write_direct(rs, iom, offset, rs->ssgl, 2, xfer_size, 0);
			rs->ssgl[0].addr = (uintptr_t) rs->sbuf + rs->ssgl[1].length;
		}
		if (ret)
			break;
	}
out:
	fastlock_release(&rs->slock);

	return (ret && left == count) ? ret : count - left;
}

/****************************************************************************
 * Service Processing Threads 服务处理线程
 ****************************************************************************/
/* 向svc 中添加rsocket 实例
 * 使得svc 可以服务多个rsocket
 */
static int rs_svc_grow_sets(struct rs_svc *svc, int grow_size)
{
	struct rsocket **rss;
	void *set, *contexts;
// svc 中两个属性：context_size 和 run 
	set = calloc(svc->size + grow_size, sizeof(*rss) + svc->context_size);// 分配多个 rs对象 和 context 的内存空间，现有两种对象各有size 个，新增 grow_size 个；
	if (!set)
		return ENOMEM;

	svc->size += grow_size;
	rss = set;// 新分配的内存空间赋值给rss 作为存放的起始地址
	contexts = set + sizeof(*rss) * svc->size;// 通过偏移量确定contexts 起始地址（猜测一个rsocket 占用的空间为 [rsocket 指针数组|context数组]
	if (svc->cnt) {
		memcpy(rss, svc->rss, sizeof(*rss) * (svc->cnt + 1));// 将当前svc 记录的rsocket 地址的指针复制到新的内存空间
		memcpy(contexts, svc->contexts, svc->context_size * (svc->cnt + 1));// 将当前svc 记录的rsocket 对应的context 复制到新的内存地址空间
	}

	free(svc->rss);
	svc->rss = rss;
	svc->contexts = contexts;
	return 0;
}

/* svc 添加所服务的rsocket 对象
 * 将 rs 添加到 svc->rss 数组末尾
 * 同时，svc-> cnt 记录 svc->rss 中已存在的rs 数量
 * Index 0 is reserved for the service's communication socket.
 * 为服务通信的socket 保留0 号位置
 * 
 */
static int rs_svc_add_rs(struct rs_svc *svc, struct rsocket *rs)
{
	int ret;
printf("rsocket debug: svc add rs %d\n",rs->index);
	if (svc->cnt >= svc->size - 1) {// 0号位置为服务之间通信的socket 保留，因此所服务的rsocket 数量达到 size-1 时就需要增加svc 存储数据的内存
		ret = rs_svc_grow_sets(svc, 4);// 增加内存空间
		if (ret)
			return ret;
	}

	svc->rss[++svc->cnt] = rs;// 将新加入的rsocket 指针放入最后一个位置
	return 0;
}

static int rs_svc_index(struct rs_svc *svc, struct rsocket *rs)
{
	int i;

	for (i = 1; i <= svc->cnt; i++) {// 0号位置保留
		if (svc->rss[i] == rs)
			return i;
	}
	return -1;
}
// 将rs 从svc 需要服务的对象中删除
static int rs_svc_rm_rs(struct rs_svc *svc, struct rsocket *rs)
{
printf("rsocket debug: svc rm rs->index %d svc_index %d\n",rs->index,rs_svc_index(svc, rs));

	int i;

	if ((i = rs_svc_index(svc, rs)) >= 0) {
		svc->rss[i] = svc->rss[svc->cnt];
		memcpy(svc->contexts + i * svc->context_size,
		       svc->contexts + svc->cnt * svc->context_size,
		       svc->context_size);
		svc->cnt--;
		return 0;
	}
	
	return EBADF;
}

static void udp_svc_process_sock(struct rs_svc *svc)
{
	struct rs_svc_msg msg;

	read_all(svc->sock[1], &msg, sizeof msg);
	switch (msg.cmd) {
	case RS_SVC_ADD_DGRAM:
		msg.status = rs_svc_add_rs(svc, msg.rs);
		if (!msg.status) {
			msg.rs->opts |= RS_OPT_UDP_SVC;
			udp_svc_fds = svc->contexts;
			udp_svc_fds[svc->cnt].fd = msg.rs->udp_sock;
			udp_svc_fds[svc->cnt].events = POLLIN;
			udp_svc_fds[svc->cnt].revents = 0;
		}
		break;
	case RS_SVC_REM_DGRAM:
		msg.status = rs_svc_rm_rs(svc, msg.rs);
		if (!msg.status)
			msg.rs->opts &= ~RS_OPT_UDP_SVC;
		break;
	case RS_SVC_NOOP:
		msg.status = 0;
		break;
	default:
		break;
	}

	write_all(svc->sock[1], &msg, sizeof msg);
}

static uint8_t udp_svc_sgid_index(struct ds_dest *dest, union ibv_gid *sgid)
{
	union ibv_gid gid;
	int i;

	for (i = 0; i < 16; i++) {
		ibv_query_gid(dest->qp->cm_id->verbs, dest->qp->cm_id->port_num,
			      i, &gid);
		if (!memcmp(sgid, &gid, sizeof gid))
			return i;
	}
	return 0;
}

static uint8_t udp_svc_path_bits(struct ds_dest *dest)
{
	struct ibv_port_attr attr;

	if (!ibv_query_port(dest->qp->cm_id->verbs, dest->qp->cm_id->port_num, &attr))
		return (uint8_t) ((1 << attr.lmc) - 1);
	return 0x7f;
}

static void udp_svc_create_ah(struct rsocket *rs, struct ds_dest *dest, uint32_t qpn)
{
	union socket_addr saddr;
	struct rdma_cm_id *id;
	struct ibv_ah_attr attr;
	int ret;

	if (dest->ah) {
		fastlock_acquire(&rs->slock);
		ibv_destroy_ah(dest->ah);
		dest->ah = NULL;
		fastlock_release(&rs->slock);
	}

	ret = rdma_create_id(NULL, &id, NULL, dest->qp->cm_id->ps);
	if  (ret)
		return;

	memcpy(&saddr, rdma_get_local_addr(dest->qp->cm_id),
	       ucma_addrlen(rdma_get_local_addr(dest->qp->cm_id)));
	if (saddr.sa.sa_family == AF_INET)
		saddr.sin.sin_port = 0;
	else
		saddr.sin6.sin6_port = 0;
	ret = rdma_resolve_addr(id, &saddr.sa, &dest->addr.sa, 2000);
	if (ret)
		goto out;

	ret = rdma_resolve_route(id, 2000);
	if (ret)
		goto out;

	memset(&attr, 0, sizeof attr);
	if (id->route.path_rec->hop_limit > 1) {
		attr.is_global = 1;
		attr.grh.dgid = id->route.path_rec->dgid;
		attr.grh.flow_label = be32toh(id->route.path_rec->flow_label);
		attr.grh.sgid_index = udp_svc_sgid_index(dest, &id->route.path_rec->sgid);
		attr.grh.hop_limit = id->route.path_rec->hop_limit;
		attr.grh.traffic_class = id->route.path_rec->traffic_class;
	}
	attr.dlid = be16toh(id->route.path_rec->dlid);
	attr.sl = id->route.path_rec->sl;
	attr.src_path_bits = be16toh(id->route.path_rec->slid) & udp_svc_path_bits(dest);
	attr.static_rate = id->route.path_rec->rate;
	attr.port_num  = id->port_num;

	fastlock_acquire(&rs->slock);
	dest->qpn = qpn;
	dest->ah = ibv_create_ah(dest->qp->cm_id->pd, &attr);
	fastlock_release(&rs->slock);
out:
	rdma_destroy_id(id);
}

static int udp_svc_valid_udp_hdr(struct ds_udp_header *udp_hdr,
				 union socket_addr *addr)
{
	return (udp_hdr->tag == htobe32(DS_UDP_TAG)) &&
		((udp_hdr->version == 4 && addr->sa.sa_family == AF_INET &&
		  udp_hdr->length == DS_UDP_IPV4_HDR_LEN) ||
		 (udp_hdr->version == 6 && addr->sa.sa_family == AF_INET6 &&
		  udp_hdr->length == DS_UDP_IPV6_HDR_LEN));
}

static void udp_svc_forward(struct rsocket *rs, void *buf, size_t len,
			    union socket_addr *src)
{
	struct ds_header hdr;
	struct ds_smsg *msg;
	struct ibv_sge sge;
	uint64_t offset;

	if (!ds_can_send(rs)) {
		if (ds_get_comp(rs, 0, ds_can_send))
			return;
	}

	msg = rs->smsg_free;
	rs->smsg_free = msg->next;
	rs->sqe_avail--;

	ds_format_hdr(&hdr, src);
	memcpy((void *) msg, &hdr, hdr.length);
	memcpy((void *) msg + hdr.length, buf, len);
	sge.addr = (uintptr_t) msg;
	sge.length = hdr.length + len;
	sge.lkey = rs->conn_dest->qp->smr->lkey;
	offset = (uint8_t *) msg - rs->sbuf;

	ds_post_send(rs, &sge, offset);
}

static void udp_svc_process_rs(struct rsocket *rs)
{
	static uint8_t buf[RS_SNDLOWAT];
	struct ds_dest *dest, *cur_dest;
	struct ds_udp_header *udp_hdr;
	union socket_addr addr;
	socklen_t addrlen = sizeof addr;
	int len, ret;
	uint32_t qpn;

	ret = recvfrom(rs->udp_sock, buf, sizeof buf, 0, &addr.sa, &addrlen);
	if (ret < DS_UDP_IPV4_HDR_LEN)
		return;

	udp_hdr = (struct ds_udp_header *) buf;
	if (!udp_svc_valid_udp_hdr(udp_hdr, &addr))
		return;

	len = ret - udp_hdr->length;
	qpn = be32toh(udp_hdr->qpn) & 0xFFFFFF;

	udp_hdr->tag = (__force __be32)be32toh(udp_hdr->tag);
	udp_hdr->qpn = (__force __be32)qpn;

	ret = ds_get_dest(rs, &addr.sa, addrlen, &dest);
	if (ret)
		return;

	if (udp_hdr->op == RS_OP_DATA) {
		fastlock_acquire(&rs->slock);
		cur_dest = rs->conn_dest;
		rs->conn_dest = dest;
		ds_send_udp(rs, NULL, 0, 0, RS_OP_CTRL);
		rs->conn_dest = cur_dest;
		fastlock_release(&rs->slock);
	}

	if (!dest->ah || (dest->qpn != qpn))
		udp_svc_create_ah(rs, dest, qpn);

	/* to do: handle when dest local ip address doesn't match udp ip */
	if (udp_hdr->op == RS_OP_DATA) {
		fastlock_acquire(&rs->slock);
		cur_dest = rs->conn_dest;
		rs->conn_dest = &dest->qp->dest;
		udp_svc_forward(rs, buf + udp_hdr->length, len, &addr);
		rs->conn_dest = cur_dest;
		fastlock_release(&rs->slock);
	}
}

static void *udp_svc_run(void *arg)
{
	struct rs_svc *svc = arg;
	struct rs_svc_msg msg;
	int i, ret;

	ret = rs_svc_grow_sets(svc, 4);
	if (ret) {
		msg.status = ret;
		write_all(svc->sock[1], &msg, sizeof msg);
		return (void *) (uintptr_t) ret;
	}

	udp_svc_fds = svc->contexts;
	udp_svc_fds[0].fd = svc->sock[1];
	udp_svc_fds[0].events = POLLIN;
	do {
		for (i = 0; i <= svc->cnt; i++)
			udp_svc_fds[i].revents = 0;

		poll(udp_svc_fds, svc->cnt + 1, -1);
		if (udp_svc_fds[0].revents)
			udp_svc_process_sock(svc);

		for (i = 1; i <= svc->cnt; i++) {
			if (udp_svc_fds[i].revents)
				udp_svc_process_rs(svc->rss[i]);
		}
	} while (svc->cnt >= 1);

	return NULL;
}

static uint64_t rs_get_time(void)
{
	return rs_time_us() / 1000000;
}

static void tcp_svc_process_sock(struct rs_svc *svc)
{
	struct rs_svc_msg msg;
	int i;

	read_all(svc->sock[1], &msg, sizeof msg);
	switch (msg.cmd) {
	case RS_SVC_ADD_KEEPALIVE:
		msg.status = rs_svc_add_rs(svc, msg.rs);
		if (!msg.status) {
			msg.rs->opts |= RS_OPT_KEEPALIVE;
			tcp_svc_timeouts = svc->contexts;
			tcp_svc_timeouts[svc->cnt] = rs_get_time() +
						     msg.rs->keepalive_time;
		}
		break;
	case RS_SVC_REM_KEEPALIVE:
		msg.status = rs_svc_rm_rs(svc, msg.rs);
		if (!msg.status)
			msg.rs->opts &= ~RS_OPT_KEEPALIVE;
		break;
	case RS_SVC_MOD_KEEPALIVE:
		i = rs_svc_index(svc, msg.rs);
		if (i >= 0) {
			tcp_svc_timeouts[i] = rs_get_time() + msg.rs->keepalive_time;
			msg.status = 0;
		} else {
			msg.status = EBADF;
		}
		break;
	case RS_SVC_NOOP:
		msg.status = 0;
		break;
	default:
		break;
	}
	write_all(svc->sock[1], &msg, sizeof msg);
}

/*
 * Send a 0 byte RDMA write with immediate as keep-alive message.
 * This avoids the need for the receive side to do any acknowledgment.
 */
static void tcp_svc_send_keepalive(struct rsocket *rs)
{
	fastlock_acquire(&rs->cq_lock);
	if (rs_ctrl_avail(rs) && (rs->state & rs_connected)) {
		rs->ctrl_seqno++;
		rs_post_write(rs, NULL, 0, rs_msg_set(RS_OP_CTRL, RS_CTRL_KEEPALIVE),
			      0, (uintptr_t) NULL, (uintptr_t) NULL);
	}
	fastlock_release(&rs->cq_lock);
}	

static void *tcp_svc_run(void *arg)
{
	struct rs_svc *svc = arg;
	struct rs_svc_msg msg;
	struct pollfd fds;
	uint64_t now, next_timeout;
	int i, ret, timeout;

	ret = rs_svc_grow_sets(svc, 16);
	if (ret) {
		msg.status = ret;
		write_all(svc->sock[1], &msg, sizeof msg);
		return (void *) (uintptr_t) ret;
	}

	tcp_svc_timeouts = svc->contexts;
	fds.fd = svc->sock[1];
	fds.events = POLLIN;
	timeout = -1;
	do {
		poll(&fds, 1, timeout * 1000);
		if (fds.revents)
			tcp_svc_process_sock(svc);

		now = rs_get_time();
		next_timeout = ~0;
		for (i = 1; i <= svc->cnt; i++) {
			if (tcp_svc_timeouts[i] <= now) {
				tcp_svc_send_keepalive(svc->rss[i]);
				tcp_svc_timeouts[i] =
					now + svc->rss[i]->keepalive_time;
			}
			if (tcp_svc_timeouts[i] < next_timeout)
				next_timeout = tcp_svc_timeouts[i];
		}
		timeout = (int) (next_timeout - now);
	} while (svc->cnt >= 1);

	return NULL;
}

static void rs_handle_cm_event(struct rsocket *rs)
{
	int ret;

	if (rs->state & rs_opening) {
		rs_do_connect(rs);
	} else {
		ret = ucma_complete(rs->cm_id);
		if (!ret && rs->cm_id->event && (rs->state & rs_connected) &&
		    (rs->cm_id->event->event == RDMA_CM_EVENT_DISCONNECTED))
			rs->state = rs_disconnected;
	}

	if (!(rs->state & rs_opening))
		rs_poll_signal();
}
// 子线程处理父线程传递来的消息
static void cm_svc_process_sock(struct rs_svc *svc)
{
	struct rs_svc_msg msg;
	struct pollfd *fds;

	read_all(svc->sock[1], &msg, sizeof(msg));// 从线程通信sock 中读取消息
	switch (msg.cmd) {// 判断消息类型
	case RS_SVC_ADD_CM:// add cm 表示向svc 中添加所服务的rsocket 对象
		msg.status = rs_svc_add_rs(svc, msg.rs);
		if (!msg.status) {// 添加成功，需要通知父线程对rs 执行删除svc 操作
			msg.rs->opts |= RS_OPT_CM_SVC;// 向父线程发送的消息 rs操作类型设为操作CM_SVC，父线程收到消息后会执行rm_cm_svc 操作
			fds = svc->contexts;
			fds[svc->cnt].fd = msg.rs->cm_id->channel->fd;// fds 最后一个fd 设为msg 对应rsocket 的channel fd
			fds[svc->cnt].events = POLLIN;
			fds[svc->cnt].revents = 0;
		}
		break;
	case RS_SVC_REM_CM:// 将rsocket 从svc 服务对象中删除
		msg.status = rs_svc_rm_rs(svc, msg.rs);
		if (!msg.status)
			msg.rs->opts &= ~RS_OPT_CM_SVC;// 删除成功，将rsocket opt 的opt cm svc 清除，避免后续误删除
		break;
	case RS_SVC_NOOP:// 不执行任何操作
		msg.status = 0;
		break;
	default:
		break;
	}
	write_all(svc->sock[1], &msg, sizeof(msg));// 向父线程发送消息
}

// rs_notify_svc 创建的服务子线程从此处开始执行
static void *cm_svc_run(void *arg)
{
	struct rs_svc *svc = arg;
	struct pollfd *fds;
	struct rs_svc_msg msg;
	int i, ret;

	ret = rs_svc_grow_sets(svc, 4);// svc 服务的rsocket 增加4个（为什么是4个？）
	if (ret) {
		msg.status = ret;// 增加空间失败，将失败信息传递给父线程
		write_all(svc->sock[1], &msg, sizeof(msg));
		return (void *) (uintptr_t) ret;// 子线程退出
	}

	fds = svc->contexts;// 获取父线程传递过来的svc 中记录的fds（何时将fd 添加到contexts 的？）// listen_svc 的context_size 使用的是sizeof(pollfd)， 
	fds[0].fd = svc->sock[1];// svc 的0号位置，保存线程通信的socketpair[1]
	fds[0].events = POLLIN;// 关注线程通信的socketpair[1] 上的可读事件
	for (int k=0;k<=svc->cnt;k++){
		// printf("rsocket debug: svc->contexts[%d] %d\n",k,((struct pollfd*)&fds[k])->fd);
	}
	do {
		for (i = 0; i <= svc->cnt; i++)
			fds[i].revents = 0;// 清空所有监听fd 已获取到的事件

		poll(fds, svc->cnt + 1, -1);// svc->cnt 记录了svc 共服务于多少个rsocket，加上0号位置的线程通信socket，因此需要cnt+1；第三个参数timeout 为-1 表示永远等待直到有事件产生
		if (fds[0].revents)// 若获取到线程通信sock 上有事件产生，表示父线程传递了消息给子线程，此时父线程传递给子线程的msg 里存了要加入 svc 的rs
			cm_svc_process_sock(svc);

		for (i = 1; i <= svc->cnt; i++) {// 遍历fds 中所有fd
			if (!fds[i].revents)
				continue;
			printf("rsocket debug: fd[%d] revents %d\n",((struct pollfd*)&fds[i])->fd,fds[i].revents);

			if (svc == &listen_svc)// 若针对某个fd，产生了事件，判断svc 是否为listen_svc，若是则执行accept
				rs_accept(svc->rss[i]);
			else
				rs_handle_cm_event(svc->rss[i]);// 若不是listen_svc，认为是connect_svc，
		}
	} while (svc->cnt >= 1);// svc 所服务的rsocket 不为空时，循环执行

	return NULL;
}
