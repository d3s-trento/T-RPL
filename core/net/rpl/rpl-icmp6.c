/*
 * Copyright (c) 2010, Swedish Institute of Computer Science.
 * All rights reserved.
 *
 * Redistribution and use in source and binary forms, with or without
 * modification, are permitted provided that the following conditions
 * are met:
 * 1. Redistributions of source code must retain the above copyright
 *    notice, this list of conditions and the following disclaimer.
 * 2. Redistributions in binary form must reproduce the above copyright
 *    notice, this list of conditions and the following disclaimer in the
 *    documentation and/or other materials provided with the distribution.
 * 3. Neither the name of the Institute nor the names of its contributors
 *    may be used to endorse or promote products derived from this software
 *    without specific prior written permission.
 *
 * THIS SOFTWARE IS PROVIDED BY THE INSTITUTE AND CONTRIBUTORS ``AS IS'' AND
 * ANY EXPRESS OR IMPLIED WARRANTIES, INCLUDING, BUT NOT LIMITED TO, THE
 * IMPLIED WARRANTIES OF MERCHANTABILITY AND FITNESS FOR A PARTICULAR PURPOSE
 * ARE DISCLAIMED.  IN NO EVENT SHALL THE INSTITUTE OR CONTRIBUTORS BE LIABLE
 * FOR ANY DIRECT, INDIRECT, INCIDENTAL, SPECIAL, EXEMPLARY, OR CONSEQUENTIAL
 * DAMAGES (INCLUDING, BUT NOT LIMITED TO, PROCUREMENT OF SUBSTITUTE GOODS
 * OR SERVICES; LOSS OF USE, DATA, OR PROFITS; OR BUSINESS INTERRUPTION)
 * HOWEVER CAUSED AND ON ANY THEORY OF LIABILITY, WHETHER IN CONTRACT, STRICT
 * LIABILITY, OR TORT (INCLUDING NEGLIGENCE OR OTHERWISE) ARISING IN ANY WAY
 * OUT OF THE USE OF THIS SOFTWARE, EVEN IF ADVISED OF THE POSSIBILITY OF
 * SUCH DAMAGE.
 *
 * This file is part of the Contiki operating system.
 *
 */

/**
 * \file
 *         ICMP6 I/O for RPL control messages.
 *
 * \author Joakim Eriksson <joakime@sics.se>, Nicolas Tsiftes <nvt@sics.se>
 * Contributors: Niclas Finne <nfi@sics.se>, Joel Hoglund <joel@sics.se>,
 *               Mathieu Pouillot <m.pouillot@watteco.com>
 *               George Oikonomou <oikonomou@users.sourceforge.net> (multicast)
 */

/**
 * \addtogroup uip6
 * @{
 */

#include "net/ip/tcpip.h"
#include "net/ip/uip.h"
#include "net/ipv6/uip-ds6.h"
#include "net/ipv6/uip-nd6.h"
#include "net/ipv6/uip-icmp6.h"
#include "net/rpl/rpl-private.h"
#include "net/packetbuf.h"
#include "net/ipv6/multicast/uip-mcast6.h"
#include "net/nbr-table.h"

#include <limits.h>
#include <string.h>

#define DEBUG DEBUG_NONE

#include "net/ip/uip-debug.h"

/*---------------------------------------------------------------------------*/
#define RPL_DIO_GROUNDED                 0x80
#define RPL_DIO_MOP_SHIFT                3
#define RPL_DIO_MOP_MASK                 0x3c
#define RPL_DIO_PREFERENCE_MASK          0x07

#define UIP_IP_BUF       ((struct uip_ip_hdr *)&uip_buf[UIP_LLH_LEN])
#define UIP_ICMP_BUF     ((struct uip_icmp_hdr *)&uip_buf[uip_l2_l3_hdr_len])
#define UIP_ICMP_PAYLOAD ((unsigned char *)&uip_buf[uip_l2_l3_icmp_hdr_len])

const uip_ipaddr_t uip_all_zeroes_addr = { { 0x0, /* rest is 0 */ } };
/*---------------------------------------------------------------------------*/
static void dis_input(void);
static void dio_input(void);
static void dao_input(void);
static void dao_ack_input(void);
static void dao_forward(const uip_ipaddr_t *dest, int type, int code, int payload_len, uip_ds6_route_t *rep);
static void broadcast_ack_input(void);

/* some debug callbacks useful when debugging RPL networks */
#ifdef RPL_DEBUG_DIO_INPUT
void RPL_DEBUG_DIO_INPUT(uip_ipaddr_t *, rpl_dio_t *);
#endif

#ifdef RPL_DEBUG_DAO_OUTPUT
void RPL_DEBUG_DAO_OUTPUT(rpl_parent_t *);
#endif

static uint8_t dao_sequence = RPL_LOLLIPOP_INIT;
static uint8_t myaddr_dao_sequence;
static uint8_t myaddr_parent_state = ROUTE_ENTRY_DAO_NOT_SENT;
static rpl_parent_t* myaddr_dao_parent = NULL; //oana: the dao parent of the current node
 
extern rpl_of_t RPL_OF;

#if RPL_CONF_MULTICAST
static uip_mcast6_route_t *mcast_group;
#endif
/*---------------------------------------------------------------------------*/
/* Initialise RPL ICMPv6 message handlers */
UIP_ICMP6_HANDLER(dis_handler, ICMP6_RPL, RPL_CODE_DIS, dis_input);
UIP_ICMP6_HANDLER(dio_handler, ICMP6_RPL, RPL_CODE_DIO, dio_input);
UIP_ICMP6_HANDLER(dao_handler, ICMP6_RPL, RPL_CODE_DAO, dao_input);
UIP_ICMP6_HANDLER(dao_ack_handler, ICMP6_RPL, RPL_CODE_DAO_ACK, dao_ack_input);
UIP_ICMP6_HANDLER(broadcast_ack_handler, ICMP6_RPL, RPL_CODE_BROADCAST_ACK, broadcast_ack_input);
/*---------------------------------------------------------------------------*/
static int
get_global_addr(uip_ipaddr_t *addr)
{
  int i;
  int state;

  for(i = 0; i < UIP_DS6_ADDR_NB; i++) {
    state = uip_ds6_if.addr_list[i].state;
    if(uip_ds6_if.addr_list[i].isused &&
       (state == ADDR_TENTATIVE || state == ADDR_PREFERRED)) {
      if(!uip_is_addr_link_local(&uip_ds6_if.addr_list[i].ipaddr)) {
        memcpy(addr, &uip_ds6_if.addr_list[i].ipaddr, sizeof(uip_ipaddr_t));
        return 1;
      }
    }
  }
  return 0;
}
/*---------------------------------------------------------------------------*/
static uint32_t
get32(uint8_t *buffer, int pos)
{
  return (uint32_t)buffer[pos] << 24 | (uint32_t)buffer[pos + 1] << 16 |
         (uint32_t)buffer[pos + 2] << 8 | buffer[pos + 3];
}
/*---------------------------------------------------------------------------*/
static void
set32(uint8_t *buffer, int pos, uint32_t value)
{
  buffer[pos++] = value >> 24;
  buffer[pos++] = (value >> 16) & 0xff;
  buffer[pos++] = (value >> 8) & 0xff;
  buffer[pos++] = value & 0xff;
}
/*---------------------------------------------------------------------------*/
static uint16_t
get16(uint8_t *buffer, int pos)
{
  return (uint16_t)buffer[pos] << 8 | buffer[pos + 1];
}
/*---------------------------------------------------------------------------*/
static void
set16(uint8_t *buffer, int pos, uint16_t value)
{
  buffer[pos++] = value >> 8;
  buffer[pos++] = value & 0xff;
}
/*---------------------------------------------------------------------------*/
static void
dis_input(void)
{
  rpl_instance_t *instance;
  rpl_instance_t *end;

  /* DAG Information Solicitation */
  PRINTF("RPL: Received a DIS from ");
  PRINT6ADDR(&UIP_IP_BUF->srcipaddr);
  PRINTF("\n");

  for(instance = &instance_table[0], end = instance + RPL_MAX_INSTANCES;
      instance < end; ++instance) {
    if(instance->used == 1) {
#if RPL_LEAF_ONLY
      if(!uip_is_addr_mcast(&UIP_IP_BUF->destipaddr)) {
	PRINTF("RPL: LEAF ONLY Multicast DIS will NOT reset DIO timer\n");
#else /* !RPL_LEAF_ONLY */
      if(uip_is_addr_mcast(&UIP_IP_BUF->destipaddr)) {
        PRINTF("RPL: Multicast DIS => reset DIO timer\n");
        rpl_reset_dio_timer(instance);
      } else {
#endif /* !RPL_LEAF_ONLY */
        PRINTF("RPL: Unicast DIS, reply to sender\n");
        dio_output(instance, &UIP_IP_BUF->srcipaddr);
      }
    }
  }
  uip_len = 0;
}
/*---------------------------------------------------------------------------*/
void
dis_output(uip_ipaddr_t *addr)
{
  unsigned char *buffer;
  uip_ipaddr_t tmpaddr;

  /*
   * DAG Information Solicitation  - 2 bytes reserved
   *      0                   1                   2
   *      0 1 2 3 4 5 6 7 8 9 0 1 2 3 4 5 6 7 8 9 0 1 2 3
   *     +-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+
   *     |     Flags     |   Reserved    |   Option(s)...
   *     +-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+
   */

  buffer = UIP_ICMP_PAYLOAD;
  buffer[0] = buffer[1] = 0;

  if(addr == NULL) {
    uip_create_linklocal_rplnodes_mcast(&tmpaddr);
    addr = &tmpaddr;
  }

  PRINTF("RPL: Sending a DIS to ");
  PRINT6ADDR(addr);
  PRINTF("\n");

  uip_icmp6_send(addr, ICMP6_RPL, RPL_CODE_DIS, 2);
}
/*---------------------------------------------------------------------------*/
static void
dio_input(void)
{
  unsigned char *buffer;
  uint8_t buffer_length;
  rpl_dio_t dio;
  uint8_t subopt_type;
  int i;
  int len;
  uip_ipaddr_t from;
  uip_ds6_nbr_t *nbr;

  memset(&dio, 0, sizeof(dio));

  /* Set default values in case the DIO configuration option is missing. */
  dio.dag_intdoubl = RPL_DIO_INTERVAL_DOUBLINGS;
  dio.dag_intmin = RPL_DIO_INTERVAL_MIN;
  dio.dag_redund = RPL_DIO_REDUNDANCY;
  dio.dag_min_hoprankinc = RPL_MIN_HOPRANKINC;
  dio.dag_max_rankinc = RPL_MAX_RANKINC;
  dio.ocp = RPL_OF.ocp;
  dio.default_lifetime = RPL_DEFAULT_LIFETIME;
  dio.lifetime_unit = RPL_DEFAULT_LIFETIME_UNIT;

  uip_ipaddr_copy(&from, &UIP_IP_BUF->srcipaddr);

  /* DAG Information Object */
  PRINTF("RPL: Received a DIO from ");
  PRINT6ADDR(&from);
  PRINTF("\n");

  if((nbr = uip_ds6_nbr_lookup(&from)) == NULL) {
    if((nbr = uip_ds6_nbr_add(&from, (uip_lladdr_t *)
                              packetbuf_addr(PACKETBUF_ADDR_SENDER),
                              0, NBR_REACHABLE)) != NULL) {
      /* set reachable timer */
      stimer_set(&nbr->reachable, UIP_ND6_REACHABLE_TIME / 1000);
      PRINTF("RPL: Neighbor added to neighbor cache ");
      PRINT6ADDR(&from);
      PRINTF(", ");
      PRINTLLADDR((uip_lladdr_t *)packetbuf_addr(PACKETBUF_ADDR_SENDER));
      PRINTF("\n");
    } else {
      printf("RPL: Out of memory, dropping DIO from ");
      uip_debug_ipaddr_print(&from);
      //PRINTF(", ");
      //PRINTLLADDR((uip_lladdr_t *)packetbuf_addr(PACKETBUF_ADDR_SENDER));
      printf("\n");
      goto discard;
    }
  } else {
    PRINTF("RPL: Neighbor already in neighbor cache\n");
  }

  buffer_length = uip_len - uip_l3_icmp_hdr_len;

  /* Process the DIO base option. */
  i = 0;
  buffer = UIP_ICMP_PAYLOAD;

  dio.instance_id = buffer[i++];
  dio.version = buffer[i++];
  dio.rank = get16(buffer, i);
  i += 2;

  PRINTF("RPL: Incoming DIO (id, ver, rank) = (%u,%u,%u)\n",
         (unsigned)dio.instance_id,
         (unsigned)dio.version,
         (unsigned)dio.rank);

  dio.grounded = buffer[i] & RPL_DIO_GROUNDED;
  dio.mop = (buffer[i]& RPL_DIO_MOP_MASK) >> RPL_DIO_MOP_SHIFT;
  dio.preference = buffer[i++] & RPL_DIO_PREFERENCE_MASK;

  dio.dtsn = buffer[i++];
  /* two reserved bytes */
  i += 2;

  memcpy(&dio.dag_id, buffer + i, sizeof(dio.dag_id));
  i += sizeof(dio.dag_id);

  PRINTF("RPL: Incoming DIO (dag_id, pref) = (");
  PRINT6ADDR(&dio.dag_id);
  PRINTF(", %u)\n", dio.preference);

  /* Check if there are any DIO suboptions. */
  for(; i < buffer_length; i += len) {
    subopt_type = buffer[i];
    if(subopt_type == RPL_OPTION_PAD1) {
      len = 1;
    } else {
      /* Suboption with a two-byte header + payload */
      len = 2 + buffer[i + 1];
    }

    if(len + i > buffer_length) {
      PRINTF("RPL: Invalid DIO packet\n");
      RPL_STAT(rpl_stats.malformed_msgs++);
      goto discard;
    }

    PRINTF("RPL: DIO option %u, length: %u\n", subopt_type, len - 2);

    switch(subopt_type) {
    case RPL_OPTION_DAG_METRIC_CONTAINER:
      if(len < 6) {
        PRINTF("RPL: Invalid DAG MC, len = %d\n", len);
	RPL_STAT(rpl_stats.malformed_msgs++);
        goto discard;
      }
      dio.mc.type = buffer[i + 2];
      dio.mc.flags = buffer[i + 3] << 1;
      dio.mc.flags |= buffer[i + 4] >> 7;
      dio.mc.aggr = (buffer[i + 4] >> 4) & 0x3;
      dio.mc.prec = buffer[i + 4] & 0xf;
      dio.mc.length = buffer[i + 5];

      if(dio.mc.type == RPL_DAG_MC_NONE) {
        /* No metric container: do nothing */
      } else if(dio.mc.type == RPL_DAG_MC_ETX) {
        dio.mc.obj.etx = get16(buffer, i + 6);

        PRINTF("RPL: DAG MC: type %u, flags %u, aggr %u, prec %u, length %u, ETX %u\n",
	       (unsigned)dio.mc.type,
	       (unsigned)dio.mc.flags,
	       (unsigned)dio.mc.aggr,
	       (unsigned)dio.mc.prec,
	       (unsigned)dio.mc.length,
	       (unsigned)dio.mc.obj.etx);
      } else if(dio.mc.type == RPL_DAG_MC_ENERGY) {
        dio.mc.obj.energy.flags = buffer[i + 6];
        dio.mc.obj.energy.energy_est = buffer[i + 7];
      } else {
       PRINTF("RPL: Unhandled DAG MC type: %u\n", (unsigned)dio.mc.type);
       goto discard;
      }
      break;
    case RPL_OPTION_ROUTE_INFO:
      if(len < 9) {
        PRINTF("RPL: Invalid destination prefix option, len = %d\n", len);
	RPL_STAT(rpl_stats.malformed_msgs++);
        goto discard;
      }

      /* The flags field includes the preference value. */
      dio.destination_prefix.length = buffer[i + 2];
      dio.destination_prefix.flags = buffer[i + 3];
      dio.destination_prefix.lifetime = get32(buffer, i + 4);

      if(((dio.destination_prefix.length + 7) / 8) + 8 <= len &&
         dio.destination_prefix.length <= 128) {
        PRINTF("RPL: Copying destination prefix\n");
        memcpy(&dio.destination_prefix.prefix, &buffer[i + 8],
               (dio.destination_prefix.length + 7) / 8);
      } else {
        PRINTF("RPL: Invalid route info option, len = %d\n", len);
	RPL_STAT(rpl_stats.malformed_msgs++);
	goto discard;
      }

      break;
    case RPL_OPTION_DAG_CONF:
      if(len != 16) {
        PRINTF("RPL: Invalid DAG configuration option, len = %d\n", len);
	RPL_STAT(rpl_stats.malformed_msgs++);
        goto discard;
      }

      /* Path control field not yet implemented - at i + 2 */
      dio.dag_intdoubl = buffer[i + 3];
      dio.dag_intmin = buffer[i + 4];
      dio.dag_redund = buffer[i + 5];
      dio.dag_max_rankinc = get16(buffer, i + 6);
      dio.dag_min_hoprankinc = get16(buffer, i + 8);
      dio.ocp = get16(buffer, i + 10);
      /* buffer + 12 is reserved */
      dio.default_lifetime = buffer[i + 13];
      dio.lifetime_unit = get16(buffer, i + 14);
      PRINTF("RPL: DAG conf:dbl=%d, min=%d red=%d maxinc=%d mininc=%d ocp=%d d_l=%u l_u=%u\n",
             dio.dag_intdoubl, dio.dag_intmin, dio.dag_redund,
             dio.dag_max_rankinc, dio.dag_min_hoprankinc, dio.ocp,
             dio.default_lifetime, dio.lifetime_unit);
      break;
    case RPL_OPTION_PREFIX_INFO:
      if(len != 32) {
        PRINTF("RPL: Invalid DAG prefix info, len != 32\n");
	RPL_STAT(rpl_stats.malformed_msgs++);
        goto discard;
      }
      dio.prefix_info.length = buffer[i + 2];
      dio.prefix_info.flags = buffer[i + 3];
      /* valid lifetime is ingnored for now - at i + 4 */
      /* preferred lifetime stored in lifetime */
      dio.prefix_info.lifetime = get32(buffer, i + 8);
      /* 32-bit reserved at i + 12 */
      PRINTF("RPL: Copying prefix information\n");
      memcpy(&dio.prefix_info.prefix, &buffer[i + 16], 16);
      break;
    default:
      PRINTF("RPL: Unsupported suboption type in DIO: %u\n",
	(unsigned)subopt_type);
    }
  }

#ifdef RPL_DEBUG_DIO_INPUT
  RPL_DEBUG_DIO_INPUT(&from, &dio);
#endif

  rpl_process_dio(&from, &dio);

discard:
  uip_len = 0;
}
/*---------------------------------------------------------------------------*/
void
dio_output(rpl_instance_t *instance, uip_ipaddr_t *uc_addr)
{
  unsigned char *buffer;
  int pos;
  rpl_dag_t *dag = instance->current_dag;
#if !RPL_LEAF_ONLY
  uip_ipaddr_t addr;
#endif /* !RPL_LEAF_ONLY */

#if RPL_LEAF_ONLY
  /* In leaf mode, we only send DIO messages as unicasts in response to
     unicast DIS messages. */
  if(uc_addr == NULL) {
    PRINTF("RPL: LEAF ONLY have multicast addr: skip dio_output\n");
    return;
  }
#endif /* RPL_LEAF_ONLY */

  /* DAG Information Object */
  pos = 0;

  buffer = UIP_ICMP_PAYLOAD;
  buffer[pos++] = instance->instance_id;
  buffer[pos++] = dag->version;

#if RPL_LEAF_ONLY
  PRINTF("RPL: LEAF ONLY DIO rank set to INFINITE_RANK\n");
  set16(buffer, pos, INFINITE_RANK);
#else /* RPL_LEAF_ONLY */
  set16(buffer, pos, dag->rank);
#endif /* RPL_LEAF_ONLY */
  pos += 2;

  buffer[pos] = 0;
  if(dag->grounded) {
    buffer[pos] |= RPL_DIO_GROUNDED;
  }

  buffer[pos] |= instance->mop << RPL_DIO_MOP_SHIFT;
  buffer[pos] |= dag->preference & RPL_DIO_PREFERENCE_MASK;
  pos++;

  buffer[pos++] = instance->dtsn_out;

  /* always request new DAO to refresh route */
  RPL_LOLLIPOP_INCREMENT(instance->dtsn_out);

  /* reserved 2 bytes */
  buffer[pos++] = 0; /* flags */
  buffer[pos++] = 0; /* reserved */

  memcpy(buffer + pos, &dag->dag_id, sizeof(dag->dag_id));
  pos += 16;

#if !RPL_LEAF_ONLY
  if(instance->mc.type != RPL_DAG_MC_NONE) {
    instance->of->update_metric_container(instance);

    buffer[pos++] = RPL_OPTION_DAG_METRIC_CONTAINER;
    buffer[pos++] = 6;
    buffer[pos++] = instance->mc.type;
    buffer[pos++] = instance->mc.flags >> 1;
    buffer[pos] = (instance->mc.flags & 1) << 7;
    buffer[pos++] |= (instance->mc.aggr << 4) | instance->mc.prec;
    if(instance->mc.type == RPL_DAG_MC_ETX) {
      buffer[pos++] = 2;
      set16(buffer, pos, instance->mc.obj.etx);
      pos += 2;
    } else if(instance->mc.type == RPL_DAG_MC_ENERGY) {
      buffer[pos++] = 2;
      buffer[pos++] = instance->mc.obj.energy.flags;
      buffer[pos++] = instance->mc.obj.energy.energy_est;
    } else {
      PRINTF("RPL: Unable to send DIO because of unhandled DAG MC type %u\n",
	(unsigned)instance->mc.type);
      return;
    }
  }
#endif /* !RPL_LEAF_ONLY */

  /* Always add a DAG configuration option. */
  buffer[pos++] = RPL_OPTION_DAG_CONF;
  buffer[pos++] = 14;
  buffer[pos++] = 0; /* No Auth, PCS = 0 */
  buffer[pos++] = instance->dio_intdoubl;
  buffer[pos++] = instance->dio_intmin;
  buffer[pos++] = instance->dio_redundancy;
  set16(buffer, pos, instance->max_rankinc);
  pos += 2;
  set16(buffer, pos, instance->min_hoprankinc);
  pos += 2;
  /* OCP is in the DAG_CONF option */
  set16(buffer, pos, instance->of->ocp);
  pos += 2;
  buffer[pos++] = 0; /* reserved */
  buffer[pos++] = instance->default_lifetime;
  set16(buffer, pos, instance->lifetime_unit);
  pos += 2;

  /* Check if we have a prefix to send also. */
  if(dag->prefix_info.length > 0) {
    buffer[pos++] = RPL_OPTION_PREFIX_INFO;
    buffer[pos++] = 30; /* always 30 bytes + 2 long */
    buffer[pos++] = dag->prefix_info.length;
    buffer[pos++] = dag->prefix_info.flags;
    set32(buffer, pos, dag->prefix_info.lifetime);
    pos += 4;
    set32(buffer, pos, dag->prefix_info.lifetime);
    pos += 4;
    memset(&buffer[pos], 0, 4);
    pos += 4;
    memcpy(&buffer[pos], &dag->prefix_info.prefix, 16);
    pos += 16;
    PRINTF("RPL: Sending prefix info in DIO for ");
    PRINT6ADDR(&dag->prefix_info.prefix);
    PRINTF("\n");
  } else {
    PRINTF("RPL: No prefix to announce (len %d)\n",
           dag->prefix_info.length);
  }

#if RPL_LEAF_ONLY
#if (DEBUG) & DEBUG_PRINT
  if(uc_addr == NULL) {
    PRINTF("RPL: LEAF ONLY sending unicast-DIO from multicast-DIO\n");
  }
#endif /* DEBUG_PRINT */
  PRINTF("RPL: Sending unicast-DIO with rank %u to ",
      (unsigned)dag->rank);
  PRINT6ADDR(uc_addr);
  PRINTF("\n");
  uip_icmp6_send(uc_addr, ICMP6_RPL, RPL_CODE_DIO, pos);
#else /* RPL_LEAF_ONLY */
  /* Unicast requests get unicast replies! */
  if(uc_addr == NULL) {
    PRINTF("RPL: Sending a multicast-DIO with rank %u\n",
        (unsigned)instance->current_dag->rank);
    uip_create_linklocal_rplnodes_mcast(&addr);
    uip_icmp6_send(&addr, ICMP6_RPL, RPL_CODE_DIO, pos);
  } else {
    PRINTF("RPL: Sending unicast-DIO with rank %u to ",
        (unsigned)instance->current_dag->rank);
    PRINT6ADDR(uc_addr);
    PRINTF("\n");
    uip_icmp6_send(uc_addr, ICMP6_RPL, RPL_CODE_DIO, pos);
  }
#endif /* RPL_LEAF_ONLY */
}
/*---------------------------------------------------------------------------*/
static void
dao_input(void)
{
  uip_ipaddr_t dao_sender_addr;
  uip_lladdr_t dao_sender_lladdr;
  rpl_dag_t *dag;
  rpl_instance_t *instance;
  unsigned char *buffer;
  uint16_t sequence;
  uint8_t instance_id;
  uint8_t lifetime;
  uint8_t prefixlen;
  uint8_t flags;
  uint8_t subopt_type;
  /*
  uint8_t pathcontrol;
  uint8_t pathsequence;
  */
  uip_ipaddr_t prefix;
  uip_ds6_route_t *rep = NULL;
  uint8_t buffer_length;
  int pos;
  int len;
  int i;
  int learned_from;
  int dao_ack_status;
  rpl_parent_t *parent;
  uip_ds6_nbr_t *nbr;

  uip_ipaddr_t used_dao_parent;
  int used_parent_state;
  int restore_dao_parent;

  prefixlen = 0;
  parent = NULL;

  uip_ipaddr_copy(&dao_sender_addr, &UIP_IP_BUF->srcipaddr);

  dao_sender_lladdr = *(uip_lladdr_t *)packetbuf_addr(PACKETBUF_ADDR_SENDER);
  /* Destination Advertisement Object */
  PRINTF("RPL: Received a DAO from ");
  PRINT6ADDR(&dao_sender_addr);
  PRINTF("\n");

  buffer = UIP_ICMP_PAYLOAD;
  buffer_length = uip_len - uip_l3_icmp_hdr_len;

  pos = 0;
  instance_id = buffer[pos++];

  instance = rpl_get_instance(instance_id);
  if(instance == NULL) {
    PRINTF("RPL: Ignoring a DAO for an unknown RPL instance(%u)\n",
           instance_id);
    goto discard;
  }

  lifetime = instance->default_lifetime;

  flags = buffer[pos++];
  /* reserved */
  pos++;
  sequence = buffer[pos++];

  dag = instance->current_dag;
  /* Is the DAG ID present? */
  if(flags & RPL_DAO_D_FLAG) {
    if(memcmp(&dag->dag_id, &buffer[pos], sizeof(dag->dag_id))) {
      PRINTF("RPL: Ignoring a DAO for a DAG different from ours\n");
      goto discard;
    }
    pos += 16;
  }

  learned_from = uip_is_addr_mcast(&dao_sender_addr) ?
                 RPL_ROUTE_FROM_MULTICAST_DAO : RPL_ROUTE_FROM_UNICAST_DAO;

  PRINTF("RPL: DAO from %s\n",
         learned_from == RPL_ROUTE_FROM_UNICAST_DAO? "unicast": "multicast");
  if(learned_from == RPL_ROUTE_FROM_UNICAST_DAO) {
    /* Check whether this is a DAO forwarding loop. */
    parent = rpl_find_parent(dag, &dao_sender_addr);
    /* check if this is a new DAO registration with an "illegal" rank */
    /* if we already route to this node it is likely */
    if(parent != NULL &&
       DAG_RANK(parent->rank, instance) < DAG_RANK(dag->rank, instance)) {
      PRINTF("RPL: Loop detected when receiving a unicast DAO from a node with a lower rank! (%u < %u)\n",
          DAG_RANK(parent->rank, instance), DAG_RANK(dag->rank, instance));
      parent->rank = INFINITE_RANK;
      parent->flags |= RPL_PARENT_FLAG_UPDATED;
      goto discard;
    }

    /* If we get the DAO from our DAO parent, we also have a loop. */
    if(parent != NULL && parent == dag->preferred_parent) {
      PRINTF("RPL: Loop detected when receiving a unicast DAO from our parent\n");
      parent->rank = INFINITE_RANK;
      parent->flags |= RPL_PARENT_FLAG_UPDATED;
      goto discard;
    }
  }

  /* Check if there are any RPL options present. */
  for(i = pos; i < buffer_length; i += len) {
    subopt_type = buffer[i];
    if(subopt_type == RPL_OPTION_PAD1) {
      len = 1;
    } else {
      /* The option consists of a two-byte header and a payload. */
      len = 2 + buffer[i + 1];
    }

    switch(subopt_type) {
    case RPL_OPTION_TARGET:
      /* Handle the target option. */
      prefixlen = buffer[i + 3];
      memset(&prefix, 0, sizeof(prefix));
      memcpy(&prefix, buffer + i + 4, (prefixlen + 7) / CHAR_BIT);
      break;
    case RPL_OPTION_TRANSIT:
      /* The path sequence and control are ignored. */
      /*      pathcontrol = buffer[i + 3];
              pathsequence = buffer[i + 4];*/
      lifetime = buffer[i + 5];
      /* The parent address is also ignored. */
      break;
    }
  }

  printf("RPL: DAO sequence: %u lifetime: %u, prefix length: %u prefix: ",
          sequence, (unsigned)lifetime, (unsigned)prefixlen);
  uip_debug_ipaddr_print(&prefix);
  printf("\n");

#if RPL_CONF_MULTICAST
  if(uip_is_addr_mcast_global(&prefix)) {
    PRINTF("RPL: mcast DAO");
    if (uip_mcast6_route_lookup(&prefix)) { /* TODO: could be better to check for ACK status as well */
      PRINTF(" (route already exists)\n");
      goto discard;
    } else {
      mcast_group = uip_mcast6_route_add(&prefix);
      if(mcast_group) {
        PRINTF(" (route added)");
        mcast_group->dag = dag;
        mcast_group->lifetime = RPL_LIFETIME(instance, lifetime);
      }
      PRINTF("\n");
      goto fwd_dao;
    }
  }
#endif

  rep = uip_ds6_route_lookup(&prefix);
  
  /*PRINTF("RPL: after route lookup. I have the following targets: \n");
  uip_ds6_route_t *rr;
  for(rr = uip_ds6_route_head();  rr != NULL; rr = uip_ds6_route_next(rr)) {
      PRINT6ADDR(&rr->ipaddr);
      PRINTF(", next hop is: ");
      PRINT6ADDR(uip_ds6_route_nexthop(rr));
      PRINTF(", preferred parent is: ");
      PRINT6ADDR(&rep->state.parent_ipaddr);
      PRINTF("\n");
  }
  PRINTF("\n");*/

  if(lifetime == RPL_ZERO_LIFETIME) {
    PRINTF("RPL: No-Path DAO received\n");
    /* No-Path DAO received; invoke the route purging routine. */
    if(rep != NULL &&
       rep->state.nopath_received == 0 &&
       rep->length == prefixlen &&
       uip_ds6_route_nexthop(rep) != NULL &&
       uip_ipaddr_cmp(uip_ds6_route_nexthop(rep), &dao_sender_addr)) {
      PRINTF("RPL: Setting expiration timer for prefix ");
      PRINT6ADDR(&prefix);
      PRINTF("\n");
      rep->state.nopath_received = 1;
      rep->state.lifetime = DAO_EXPIRATION_TIMEOUT;

      
      /* We forward the incoming no-path DAO to our parent, if we have one. */
      //oana: differentiate here which dao parent for which target   
      if(dag->preferred_parent != NULL && !uip_ipaddr_cmp(&rep->state.parent_ipaddr, &uip_all_zeroes_addr)) {
        /*PRINTF("RPL: Forwarding no-path DAO to parent ");
        PRINT6ADDR(&rep->state.parent_ipaddr);
        PRINTF("\n");*/
        //uip_icmp6_send(&rep->state.parent_ipaddr,ICMP6_RPL, RPL_CODE_DAO, buffer_length);
        dao_forward(&rep->state.parent_ipaddr, ICMP6_RPL, RPL_CODE_DAO, buffer_length, rep);
        //rep->state.parent_ipaddr = uip_all_zeroes_addr;
      }
      if(flags & RPL_DAO_K_FLAG) {
        dao_ack_output(instance, &dao_sender_addr, sequence, RPL_DAO_ACK_ACCEPT);
      }
    }
    goto discard;
  }

  PRINTF("RPL: adding DAO route\n");

  if (rep) {
  	// removing the stale route (if any)
	// but keeping the ip of the dao parent to restore it later
	used_dao_parent = rep->state.parent_ipaddr;
	used_parent_state = rep->state.parent_state;
	uip_ds6_route_rm(rep); 
	restore_dao_parent = 1;
	rep = NULL;
  }
  else {
	restore_dao_parent = 0;
  }

  dao_ack_status = RPL_DAO_ACK_ACCEPT;

  if((nbr = uip_ds6_nbr_lookup(&dao_sender_addr)) == NULL) {
    if((nbr = uip_ds6_nbr_add(&dao_sender_addr, &dao_sender_lladdr,
                              0, NBR_REACHABLE)) != NULL) {
      nbr_table_stats_t *stats;
      stats = nbr_table_get_stats();
      if (stats->locked < stats->max-4) {
        ///* lock next hop in nbr table */
        //nbr_table_lock(rpl_parents, &dao_sender_addr);
        /* set reachable timer */
        stimer_set(&nbr->reachable, UIP_ND6_REACHABLE_TIME / 1000);
        PRINTF("RPL: Neighbor added to neighbor cache (locked:%u used:%u max:%u) ",stats->locked, stats->used, stats->max);
        PRINT6ADDR(&dao_sender_addr);
        PRINTF(", ");
        PRINTLLADDR(&dao_sender_lladdr);
        PRINTF("\n");
      } else {
        printf("RPL: Almost Out of Memory, dropping DAO (sending NACK) from ");
		uip_debug_ipaddr_print(&dao_sender_addr);
		printf("\n");
        //PRINTF(", ");
        //PRINTLLADDR((uip_lladdr_t *)packetbuf_addr(PACKETBUF_ADDR_SENDER));
        /* send explicit NACK */
        dao_ack_status = RPL_DAO_ACK_REJECT;
        //uip_ds6_nbr_rm(nbr); //no need to remove; adding to nbr table, but not to routing table. Not locking, so it will eventually go away.
	    goto send_ack;
      }
    } else {
      printf("RPL: Out of Memory, dropping DAO from ");
      uip_debug_ipaddr_print(&dao_sender_addr);
      //PRINTF(", ");
      //PRINTLLADDR((uip_lladdr_t *)packetbuf_addr(PACKETBUF_ADDR_SENDER));
      printf("\n");
	  // no memory to send any DAO ACKs, should never happen
      goto discard;
    }
  } else {
    printf("RPL: Neighbor already in neighbor cache\n");
    nbr_table_stats_t *stats;
    stats = nbr_table_get_stats();
    if (stats->locked >= stats->max-4 && ! rpl_parent_is_locked(parent)) {
      printf("RPL: limiting fan-out to %u (locked:%u), dropping DAO\n", stats->max-4, stats->locked);
      /* send explicit NACK */
      dao_ack_status = RPL_DAO_ACK_REJECT;
      goto send_ack;
    }
  }

  rpl_lock_parent(parent); // locking the next hop router (called parent here, but neighbor would be a better term)

  rep = rpl_add_route(dag, &prefix, prefixlen, &dao_sender_addr);
  if(rep == NULL) {
    RPL_STAT(rpl_stats.mem_overflows++);
	printf("RPL: Could not add a route after receiving a DAO (sending NACK) from ");
	uip_debug_ipaddr_print(&dao_sender_addr);
	//PRINTF(", ");
	//PRINTLLADDR((uip_lladdr_t *)packetbuf_addr(PACKETBUF_ADDR_SENDER));
	printf("\n");
	/* send explicit NACK */
	dao_ack_status = RPL_DAO_ACK_ROUTE_REJECT;
	goto send_ack;
  }
  else{ // added a routing entry
	rep->state.lifetime = RPL_LIFETIME(instance, lifetime);
	rep->state.learned_from = learned_from;
	rep->state.nopath_received = 0;
	rep->state.parent_state = ROUTE_ENTRY_DAO_NOT_SENT;
		
	if (restore_dao_parent) { // added an entry for a destination known before
      rep->state.parent_ipaddr = used_dao_parent;
	  rep->state.parent_state = used_parent_state;
	}
	else { // added an entry for a new destination
	  uip_ipaddr_t* last_dao_parent_ipaddr = rpl_get_parent_ipaddr(dag->last_preferred_dao_parent); 
	  if(dag->preferred_parent != NULL && last_dao_parent_ipaddr != NULL){
		rep->state.parent_ipaddr = *(uip_ipaddr_t*)last_dao_parent_ipaddr;
		PRINTF("RPL: Adding new route and setting DAO parent to ");
		PRINT6ADDR(&rep->state.parent_ipaddr);
		PRINTF("\n");
	    PRINTF("RPL: preferred parent: %p", dag->preferred_parent);
	    PRINTF("\n");
	  }
	  else{
        rep->state.parent_ipaddr = uip_all_zeroes_addr;
		printf("pref and/or last dao parent is null: %p %p\n", dag->preferred_parent, last_dao_parent_ipaddr);
      }
	} 
  }	

#if RPL_CONF_MULTICAST
fwd_dao:
#endif
  //PRINTF("RPL: Just before Forwarding DAO to parent\n ");
  if(dag->preferred_parent != NULL){
	uip_ipaddr_t* to = NULL;
	if(rep == NULL) {/* rep could be NULL in case of multicast */
		to = rpl_get_parent_ipaddr(dag->preferred_parent);
   	    printf("RPL: Forwarding DAO to preferred parent (rep null): ");
	}
	else if (!uip_ipaddr_cmp(&rep->state.parent_ipaddr, &uip_all_zeroes_addr)) {
		to = &rep->state.parent_ipaddr;
   	    printf("RPL: Forwarding DAO to previously used parent: ");
	}
	else {
		to = rpl_get_parent_ipaddr(dag->preferred_parent); // Tim: or last_preferred_dao_parent?
   	    printf("RPL: Forwarding DAO to preferred parent (no prev parent): ");
		rep->state.parent_ipaddr = *to;
	}
	uip_debug_ipaddr_print(to);
   	printf("\n");
	if (to)
   	  dao_forward(to, ICMP6_RPL, RPL_CODE_DAO, buffer_length, rep);
  }
  else {
    printf("Not fwd DAO, pref parent is null\n");
  }

send_ack:
  if(flags & RPL_DAO_K_FLAG) {
    /* IP stack needs sender to be among neighbors in order to send ICMP reply */
    // Tim: it should never happen that we are here but there's no neighbor table entry
    //      threfore commenting the following
    /*if(uip_ds6_nbr_lookup(&dao_sender_addr) == NULL) {
    uip_ds6_nbr_add(&dao_sender_addr, &dao_sender_lladdr, 0, NBR_REACHABLE);
    }*/
    if (dag->rank == ROOT_RANK(instance)) { // with root-bcast root always accepts
      dao_ack_output(instance, &dao_sender_addr, sequence, RPL_DAO_ACK_ACCEPT);
    }
    else {
      /*if(dag->preferred_parent != NULL)*/{
        dao_ack_output(instance, &dao_sender_addr, sequence, dao_ack_status);
      }
    }
  }
discard:
  uip_len = 0;
}
/*---------------------------------------------------------------------------*/
void
send_dao_all_targets(rpl_instance_t *instance, rpl_parent_t *p){
  /*rpl_dag_t *dag;
  dag = p->dag;
  if(dag == NULL) {
    PRINTF("RPL dao_output error dag NULL\n");
    return;
  }
 
  PRINTF("RPL: send_dao_all_targets: \n");
  uip_ds6_route_t *rr;
  for(rr = uip_ds6_route_head();  rr != NULL; rr = uip_ds6_route_next(rr)) {
         rr->state.parent_ipaddr = *(rpl_get_parent_ipaddr(dag->last_preferred_dao_parent));   
      dao_output_target(p, &rr->ipaddr, instance->default_lifetime);
      PRINT6ADDR(&rr->ipaddr);
      PRINTF(", ");
  }
  PRINTF("\n");*/
  
  printf("RPL: nullify the pseudo dao parent: \n");
  uip_ds6_route_t *rr;
  for(rr = uip_ds6_route_head();  rr != NULL; rr = uip_ds6_route_next(rr)) {
       rr->state.parent_state = ROUTE_ENTRY_DAO_NOT_SENT;
       rr->state.parent_ipaddr = uip_all_zeroes_addr;
       myaddr_dao_parent = NULL;        
  } 
}
/*---------------------------------------------------------------------------*/
void
dao_output(rpl_parent_t *parent, uint8_t lifetime)
{
  rpl_dag_t *dag;
  dag = parent->dag;
  if(dag == NULL) {
    PRINTF("RPL dao_output error dag NULL\n");
    return;
  }
	
  /* Destination Advertisement Object */
  uip_ipaddr_t prefix;

  if(get_global_addr(&prefix) == 0) {
    PRINTF("RPL: No global address set for this node - suppressing DAO\n");
    return;
  }

  //in case of No-Path  
  if(lifetime == RPL_ZERO_LIFETIME){
       //dao_output_myself(parent, &prefix, lifetime);
       myaddr_dao_parent = dag->preferred_parent;
       dag->last_preferred_dao_parent = dag->preferred_parent;
       printf("RPL: Preferred parent changed to ");
       uip_debug_ipaddr_print(rpl_get_parent_ipaddr(myaddr_dao_parent));
       //printf(" from ");
    //uip_debug_ipaddr_print(rpl_get_parent_ipaddr(parent));
       printf("\n");
       
       //send No-Path for all the targets
       /*uip_ds6_route_t *rr;
       for(rr = uip_ds6_route_head();  rr != NULL; rr = uip_ds6_route_next(rr)) {
      PRINT6ADDR(&rr->ipaddr);
      PRINTF(", ");
       }
       PRINTF("\n");*/
       
       return;
  }
  
  /* Sending a DAO with own prefix as target */ 
  if(myaddr_dao_parent != NULL){
       printf("RPL: DAO sent to ");
       uip_debug_ipaddr_print(rpl_get_parent_ipaddr(myaddr_dao_parent));
       printf("\n");
       dao_output_myself(myaddr_dao_parent, &prefix, lifetime);
  }
  else{
       dao_output_myself(dag->last_preferred_dao_parent, &prefix, lifetime);
       myaddr_dao_parent = dag->last_preferred_dao_parent;
       printf("RPL: DAO sent to ");
       uip_debug_ipaddr_print(rpl_get_parent_ipaddr(myaddr_dao_parent));
       printf("\n");
  }
 

  
  myaddr_dao_sequence = dao_sequence;
  myaddr_parent_state = ROUTE_ENTRY_DAO_SENT;
}
/*---------------------------------------------------------------------------*/
//for a node, its DAO parent is kept in myaddr_dao_parent, while for a target, its DAO parent is kept in the routing table
void
dao_output_myself(rpl_parent_t *parent, uip_ipaddr_t *prefix, uint8_t lifetime)
{
  rpl_dag_t *dag;
  rpl_instance_t *instance;
  unsigned char *buffer;
  uint8_t prefixlen;
  int pos;

  /* Destination Advertisement Object */

  /* If we are in feather mode, we should not send any DAOs */
  if(rpl_get_mode() == RPL_MODE_FEATHER) {
    return;
  }

  if(parent == NULL) {
    PRINTF("RPL dao_output_myself error parent NULL\n");
    return;
  }

  dag = parent->dag;
  if(dag == NULL) {
    PRINTF("RPL dao_output_myself error dag NULL\n");
    return;
  }

  instance = dag->instance;

  if(instance == NULL) {
    PRINTF("RPL dao_output_myself error instance NULL\n");
    return;
  }
  if(prefix == NULL) {
    PRINTF("RPL dao_output_myself error prefix NULL\n");
    return;
  }
#ifdef RPL_DEBUG_DAO_OUTPUT
  RPL_DEBUG_DAO_OUTPUT(parent);
#endif

  buffer = UIP_ICMP_PAYLOAD;

  RPL_LOLLIPOP_INCREMENT(dao_sequence);
  pos = 0;

  buffer[pos++] = instance->instance_id;
  buffer[pos] = 0;
#if RPL_DAO_SPECIFY_DAG
  buffer[pos] |= RPL_DAO_D_FLAG;
#endif /* RPL_DAO_SPECIFY_DAG */
#if RPL_CONF_DAO_ACK
  buffer[pos] |= RPL_DAO_K_FLAG;
#endif /* RPL_CONF_DAO_ACK */
  ++pos;
  buffer[pos++] = 0; /* reserved */
  buffer[pos++] = dao_sequence;
#if RPL_DAO_SPECIFY_DAG
  memcpy(buffer + pos, &dag->dag_id, sizeof(dag->dag_id));
  pos+=sizeof(dag->dag_id);
#endif /* RPL_DAO_SPECIFY_DAG */

  /* create target subopt */
  prefixlen = sizeof(*prefix) * CHAR_BIT;
  buffer[pos++] = RPL_OPTION_TARGET;
  buffer[pos++] = 2 + ((prefixlen + 7) / CHAR_BIT);
  buffer[pos++] = 0; /* reserved */
  buffer[pos++] = prefixlen;
  memcpy(buffer + pos, prefix, (prefixlen + 7) / CHAR_BIT);
  pos += ((prefixlen + 7) / CHAR_BIT);

  /* Create a transit information sub-option. */
  buffer[pos++] = RPL_OPTION_TRANSIT;
  buffer[pos++] = 4;
  buffer[pos++] = 0; /* flags - ignored */
  buffer[pos++] = 0; /* path control - ignored */
  buffer[pos++] = 0; /* path seq - ignored */
  buffer[pos++] = lifetime;

  printf("RPL: Sending DAO with sequence number %u and lifetime %u prefix ",
    dao_sequence, lifetime);
  uip_debug_ipaddr_print(prefix);
  printf(" to ");
  uip_debug_ipaddr_print(rpl_get_parent_ipaddr(parent));
  printf("\n");

  if(rpl_get_parent_ipaddr(parent) != NULL) {
    uip_icmp6_send(rpl_get_parent_ipaddr(parent), ICMP6_RPL, RPL_CODE_DAO, pos);
  }
}

void
dao_output_target(rpl_parent_t *parent, uip_ipaddr_t *prefix, uint8_t lifetime)
{
  rpl_dag_t *dag;
  rpl_instance_t *instance;
  unsigned char *buffer;
  uint8_t prefixlen;
  int pos;

  /* Destination Advertisement Object */

  /* If we are in feather mode, we should not send any DAOs */
  if(rpl_get_mode() == RPL_MODE_FEATHER) {
    return;
  }

  if(parent == NULL) {
    PRINTF("RPL dao_output_target error parent NULL\n");
    return;
  }

  dag = parent->dag;
  if(dag == NULL) {
    PRINTF("RPL dao_output_target error dag NULL\n");
    return;
  }

  instance = dag->instance;

  if(instance == NULL) {
    PRINTF("RPL dao_output_target error instance NULL\n");
    return;
  }
  if(prefix == NULL) {
    PRINTF("RPL dao_output_target error prefix NULL\n");
    return;
  }
  
  //oana: get the right parent
  uip_ds6_route_t *rep = uip_ds6_route_lookup(prefix);
  if (!rep ) {
       PRINTF("RPL dao_output_target error route finder from prefix returned NULL\n");
       return;
  }

//#ifdef RPL_DEBUG_DAO_OUTPUT
//  RPL_DEBUG_DAO_OUTPUT(parent); //oana: not the right parent anymore
//#endif

  
  buffer = UIP_ICMP_PAYLOAD;

  RPL_LOLLIPOP_INCREMENT(dao_sequence);
  pos = 0;

  buffer[pos++] = instance->instance_id;
  buffer[pos] = 0;
#if RPL_DAO_SPECIFY_DAG
  buffer[pos] |= RPL_DAO_D_FLAG;
#endif /* RPL_DAO_SPECIFY_DAG */
#if RPL_CONF_DAO_ACK
  buffer[pos] |= RPL_DAO_K_FLAG;
#endif /* RPL_CONF_DAO_ACK */
  ++pos;
  buffer[pos++] = 0; /* reserved */
  buffer[pos++] = dao_sequence;
#if RPL_DAO_SPECIFY_DAG
  memcpy(buffer + pos, &dag->dag_id, sizeof(dag->dag_id));
  pos+=sizeof(dag->dag_id);
#endif /* RPL_DAO_SPECIFY_DAG */

  /* create target subopt */
  prefixlen = sizeof(*prefix) * CHAR_BIT;
  buffer[pos++] = RPL_OPTION_TARGET;
  buffer[pos++] = 2 + ((prefixlen + 7) / CHAR_BIT);
  buffer[pos++] = 0; /* reserved */
  buffer[pos++] = prefixlen;
  memcpy(buffer + pos, prefix, (prefixlen + 7) / CHAR_BIT);
  pos += ((prefixlen + 7) / CHAR_BIT);

  /* Create a transit information sub-option. */
  buffer[pos++] = RPL_OPTION_TRANSIT;
  buffer[pos++] = 4;
  buffer[pos++] = 0; /* flags - ignored */
  buffer[pos++] = 0; /* path control - ignored */
  buffer[pos++] = 0; /* path seq - ignored */
  buffer[pos++] = lifetime;
  //TODO oana: if lifetime = RPL_ZERO_LIFETIME, then NoPath to the pref parent from rpl.c
  if(lifetime == RPL_ZERO_LIFETIME) 
       printf("RPL: lifetime = RPL_ZERO_LIFETIME should do smth\n");

  if(uip_ipaddr_cmp(&rep->state.parent_ipaddr, &uip_all_zeroes_addr)){
       PRINTF("RPL[dao_output_target]:Route did not have any parent; just added last_preferred_dao_parent; ");
       rep->state.parent_ipaddr = *(rpl_get_parent_ipaddr(dag->last_preferred_dao_parent));
       PRINT6ADDR(&rep->state.parent_ipaddr);
    PRINTF("\n");  
  }    

  printf("RPL[dao_output_target]: Sending DAO with sequence number %u and lifetime %u prefix ",
    dao_sequence, lifetime);
  uip_debug_ipaddr_print(prefix);
  printf(" to ");
  uip_debug_ipaddr_print(&rep->state.parent_ipaddr);
  printf("\n");

  rep->state.dao_sequence = dao_sequence;
  rep->state.parent_state = ROUTE_ENTRY_DAO_SENT;

  uip_icmp6_send(&rep->state.parent_ipaddr, ICMP6_RPL, RPL_CODE_DAO, pos);
}
/*---------------------------------------------------------------------------*/
/*
 * Forward a DAO packet, changing the sequence number to the local one.
 * rep: the routing entry for the DAO target, if known
*/
static void
dao_forward(const uip_ipaddr_t *dest, int type, int code, int payload_len, uip_ds6_route_t *rep)
{
  if (payload_len < 4) {
    return;
  }

  RPL_LOLLIPOP_INCREMENT(dao_sequence);
  UIP_ICMP_PAYLOAD[3] = dao_sequence;

  if (rep) {
    rep->state.dao_sequence = dao_sequence;
    rep->state.parent_state = ROUTE_ENTRY_DAO_SENT;
    //rep->state.parent_ipaddr = dest; this is done when the forward function is called	
  }
  uip_icmp6_send(dest, type, code, payload_len);
}
/*---------------------------------------------------------------------------*/
static uip_ds6_route_t *
route_lookup_by_dao_seq(uint8_t seq)
{
  /* TODO: add wraparound protection? */
  uip_ds6_route_t *r;
  for(r = uip_ds6_route_head(); r != NULL; r = uip_ds6_route_next(r)) {
    if (r->state.dao_sequence == seq) {
      return r;
    }
  }

  return NULL;
}
/*---------------------------------------------------------------------------*/
static void
dao_ack_input(void)
{
  unsigned char *buffer;
  //uint8_t buffer_length;
  uint8_t instance_id;
  uint8_t sequence;
  uint8_t status;
  rpl_instance_t *instance;
  uip_ds6_route_t *rep;
  rpl_dag_t* dag;

  buffer = UIP_ICMP_PAYLOAD;
  //buffer_length = uip_len - uip_l3_icmp_hdr_len;

  instance_id = buffer[0];
  sequence = buffer[2];
  status = buffer[3];

  printf("RPL: Received a DAO ACK with sequence number %u and status %u from ",
    sequence, status);
  uip_debug_ipaddr_print(&UIP_IP_BUF->srcipaddr);
  printf("\n");

  instance = rpl_get_instance(instance_id);
  if(instance == NULL) {
      PRINTF("RPL: Ignoring a DAO-ACK for an unknown RPL instance(%u)\n",
             instance_id);
	goto discard;
  }

  rep = route_lookup_by_dao_seq(sequence);
  if(! rep && sequence != myaddr_dao_sequence) {
      PRINTF("RPL: Ignoring a DAO-ACK with wrong sequence number(%u). Multicast?\n",
             sequence);
	goto discard;
  }

  if(status == RPL_DAO_ACK_REJECT || status == RPL_DAO_ACK_ROOT_REJECT || status == RPL_DAO_ACK_ROUTE_REJECT) {
    //mark route as mcaster
    if(rep){
      rep->state.parent_state = ROUTE_ENTRY_DAO_NACKED;
    }else{
      myaddr_parent_state = ROUTE_ENTRY_DAO_NACKED;
    }

    //join mcaster group, if not already joined
    uip_ipaddr_t addr;
    uip_ds6_maddr_t * rv;

    /*     
    * IPHC will use stateless multicast compression for this destination
    * (M=1, DAC=0), with 32 inline bits (1E 89 AB CD)
    */
	#define MCASTER_GROUP 0xDDDD
    uip_ip6addr(&addr, 0xFF1E,0,0,0,0,0,0x89,MCASTER_GROUP);
    rv = uip_ds6_maddr_add(&addr);

    if(rv){
      printf("RPL: DAO-NACK, joined multicast group ");
      PRINT6ADDR(&uip_ds6_maddr_lookup(&addr)->ipaddr);
      printf("\n");
    }
    
    //oana: if the sender of the DAO-NACk was not the root: try to change the parent
 	if(status == RPL_DAO_ACK_REJECT || status == RPL_DAO_ACK_ROUTE_REJECT){
 	  	dag = instance->current_dag;
  		if(dag == NULL){
  			//PRINTF("RPL [dao_ack_input]: No existing dag.\n");
  			return;
  		}
    	
 	  	//oana: search for new DAO preferred parent and resend DAO
  		rpl_parent_t *p;  	
    	
    	if(!uip_ipaddr_cmp(&UIP_IP_BUF->srcipaddr, rpl_get_parent_ipaddr(dag->last_preferred_dao_parent))){
    		//added this case for when the parent to which I initially sent the DAO is not the last_pref_parent anymore 
			//it can happen when the pref parent changed between when I sent the DAO and when I received the NACK
    		p = dag->last_preferred_dao_parent;
		}
   		else{
   			p = new_dao_parent(dag);	
			if(p != NULL){
   				p->already_tried = 1;
   				dag->last_preferred_dao_parent = p;
   				rpl_lock_parent(p);
			}
   			else{
				//no other parents available => local repair?
				PRINTF("DAO_ACK_INPUT: SHOULD DO local repair now?\n");
				//rpl_local_repair(instance);
				return;
			}
   		}
   		
   		//add this parent for the specific target and resend DAO
 		if(rep){
 			rep->state.parent_ipaddr = *(rpl_get_parent_ipaddr(p));
 			rep->state.parent_state = ROUTE_ENTRY_DAO_NACKED;
 			PRINTF("DAO_ACK_INPUT: checking another parent: ");
 	   		PRINT6ADDR(&rep->state.parent_ipaddr);
    		//PRINTF("with rank %u\n", (unsigned)p->rank);
      		PRINTF("for target\n");
 			dao_output_target(p, &rep->ipaddr, instance->default_lifetime); //resend dao
   	 	} 
  		else{	
  			if(sequence == myaddr_dao_sequence){
  				myaddr_dao_parent = p;
  				myaddr_parent_state = ROUTE_ENTRY_DAO_NACKED;
				PRINTF("DAO_ACK_INPUT: checking another parent: ");
      			PRINT6ADDR(rpl_get_parent_ipaddr(p));
      			PRINTF("for myself\n");
  				dao_output(p, instance->default_lifetime); //resend dao
  			}
		}
 	}//end if (sender not the root)
 }
 else{ //if DAO-ACK
    uip_ipaddr_t addr;
    uip_ds6_maddr_t *maddr;

    if(rep){
       rep->state.parent_state = ROUTE_ENTRY_DAO_ACKED;
    }else{
       if(sequence == myaddr_dao_sequence)
          myaddr_parent_state = ROUTE_ENTRY_DAO_ACKED;
    }

    // check if we can leave the mcast group
    uip_ip6addr(&addr, 0xFF1E,0,0,0,0,0,0x89,MCASTER_GROUP);
    if((maddr = uip_ds6_maddr_lookup(&addr))){
      uip_ds6_route_t *r;
      uint8_t allacked = 1;
      r = uip_ds6_route_head();

      while(r != NULL){
        if(r->state.parent_state != ROUTE_ENTRY_DAO_ACKED){
          allacked = 0;
          break;
        }
        r = uip_ds6_route_next(r);
      }
      if(allacked && myaddr_parent_state == ROUTE_ENTRY_DAO_ACKED){
        printf("RPL: DAO-ACK, could leave multicast group\n");
        uip_ds6_maddr_rm(maddr);
      }
    }
  }
discard:
  uip_len = 0;
}
/*---------------------------------------------------------------------------*/
void
dao_ack_output(rpl_instance_t *instance, uip_ipaddr_t *dest, uint8_t sequence, uint8_t status)
{
  unsigned char *buffer;

  PRINTF("RPL: Sending a DAO ACK with sequence number %u status %u to ", sequence, status);
  //uip_debug_ipaddr_print(dest);
  PRINTF("\n");

  buffer = UIP_ICMP_PAYLOAD;

  buffer[0] = instance->instance_id;
  buffer[1] = 0;
  buffer[2] = sequence;
  buffer[3] = status;

  uip_icmp6_send(dest, ICMP6_RPL, RPL_CODE_DAO_ACK, 4);
}
/*---------------------------------------------------------------------------*/
void
rpl_icmp6_register_handlers()
{
  uip_icmp6_register_input_handler(&dis_handler);
  uip_icmp6_register_input_handler(&dio_handler);
  uip_icmp6_register_input_handler(&dao_handler);
  uip_icmp6_register_input_handler(&dao_ack_handler);
  uip_icmp6_register_input_handler(&broadcast_ack_handler);
}
/*---------------------------------------------------------------------------*/

void root_bcast_ack();

static void
broadcast_ack_input(void)
{
  unsigned char *buffer;
  uint8_t buffer_length;
  uint8_t instance_id;
  uint8_t sequence;
  uint8_t status;

  buffer = UIP_ICMP_PAYLOAD;
  buffer_length = uip_len - uip_l3_icmp_hdr_len;

  instance_id = buffer[0];
  sequence = buffer[2];
  status = buffer[3];

  printf("RPL: Received a BCAST ACK with sequence number %d and status %d from ",
    sequence, status);
  //PRINT6ADDR(&UIP_IP_BUF->srcipaddr);
  uip_debug_ipaddr_print(&UIP_IP_BUF->srcipaddr);
  printf("\n");
  root_bcast_ack();
  uip_len = 0;
}
/*---------------------------------------------------------------------------*/
void
broadcast_ack_output(uip_ipaddr_t *dest, uint8_t sequence)
{
  unsigned char *buffer;

  printf("RPL: Sending a Broadcast ACK with sequence number %d to ", sequence);
  uip_debug_ipaddr_print(dest);
  printf("\n");

  buffer = UIP_ICMP_PAYLOAD;

  buffer[0] = 0;//instance->instance_id;
  buffer[1] = 0;
  buffer[2] = sequence;
  buffer[3] = 0;

  uip_icmp6_send(dest, ICMP6_RPL, RPL_CODE_BROADCAST_ACK, 4);
}
/*---------------------------------------------------------------------------*/
/** @}*/
