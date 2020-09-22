/**
 * bp_common_mem_if.vh
 *
 * This file defines the interface between the UCE/CCE and memory.
 *
 */

`ifndef BP_COMMON_MEM_IF_VH
`define BP_COMMON_MEM_IF_VH

`include "bsg_defines.v"
`include "bp_common_lce_cce_if.vh"

/*
 *
 * CCE-Memory Interface
 *
 */

/*
 * bp_mem_msg_e specifies the memory command from the UCE/CCE
 *
 * There are three types of commands:
 * 1. Access to memory that should be cached in L2/LLC (rd/wr)
 * 2. Access to memory that should remain uncached by L2/LLC (uc_rd/uc_wr)
 * 3. Prefetch access to memory that should be cached in L2/LLC (pre)
 *
 * Cacheability of the data at the L1/LCE level is determined by the uncached bit within
 * the payload of the message, and is managed by the LCE/CCE. This information is not
 * exposed to memory/L2/LLC, allowing for accesses that may be wholly uncached, locally
 * uncached but globally cached, or locally cached but globally uncached in the system.
 *
 */
typedef enum logic [3:0]
{
  e_mem_msg_rd        = 4'b0000  // Cache block fetch / load / Get (cached in L2/LLC)
  ,e_mem_msg_wr       = 4'b0001  // Cache block write / writeback / store / Put (cached in L2/LLC)
  ,e_mem_msg_uc_rd    = 4'b0010  // Uncached load (uncached in L2/LLC)
  ,e_mem_msg_uc_wr    = 4'b0011  // Uncached store (uncached in L2/LLC)
  ,e_mem_msg_pre      = 4'b0100  // Pre-fetch block request from CCE, fill into L2/LLC if able
  // Atomic support
  ,e_mem_msg_lr       = 4'b0101
  ,e_mem_msg_sc       = 4'b0110
  ,e_mem_msg_amo_swap = 4'b0111
  ,e_mem_msg_amo_add  = 4'b1000
  ,e_mem_msg_amo_xor  = 4'b1001
  ,e_mem_msg_amo_and  = 4'b1010
  ,e_mem_msg_amo_or   = 4'b1011
  ,e_mem_msg_amo_min  = 4'b1100
  ,e_mem_msg_amo_max  = 4'b1101
  ,e_mem_msg_amo_minu = 4'b1110
  ,e_mem_msg_amo_maxu = 4'b1111
} bp_mem_msg_e;

/*
 *
 * CCE to Mem Command
 *
 */

/*
 * bp_cce_mem_msg_payload_s defines a payload that is sent to the memory system by the CCE as part
 * of bp_cce_mem_msg_s and returned by the mem to the CCE in bp_mem_cce_data_resp_s. This data
 * is not required by the memory system to complete the request, and should not be modified by
 * most memory side devices by default.
 *
 * lce_id is the LCE that sent the initial request to the CCE
 * way_id is the way within the cache miss address target set to fill the data in to
 * state is the fill coherence state (may be changed if request was speculative)
 * prefetch is set if the request was a prefetch from LCE (as opposed to CCE)
 * uncached is set if the request was an uncached request from LCE
 * speculative is set if the request was issued speculatively by the CCE
 */

`define declare_bp_mem_msg_payload_s(lce_id_width_mp, lce_assoc_mp, name_mp) \
  typedef struct packed                                       \
  {                                                           \
    bp_coh_states_e                              state;       \
    logic [`BSG_SAFE_CLOG2(lce_assoc_mp)-1:0]    way_id;      \
    logic [lce_id_width_mp-1:0]                  lce_id;      \
    logic                                        prefetch;    \
    logic                                        uncached;    \
    logic                                        speculative; \
  } bp_``name_mp``_msg_payload_s;


/*
 * bp_mem_msg_s is the message struct for messages between the UCE/CCE and memory
 *
 * msg_type gives the command or response type (interpretation depends on direction of message)
 * addr is the physical address for the command/response, and must be aligned according to size
 * size is the size in bytes of the access, with data in the low-order size bits of the data field
 * payload is an opaque field sent to mem and returned to the CCE unmodified
 */
`define declare_bp_mem_msg_s(addr_width_mp, data_width_mp, name_mp)  \
  typedef struct packed                                         \
  {                                                             \
    bp_``name_mp``_msg_payload_s                 payload;       \
    bp_mem_msg_size_e                            size;          \
    logic [addr_width_mp-1:0]                    addr;          \
    bp_mem_msg_e                                 msg_type;      \
  } bp_``name_mp``_msg_header_s;                                \
                                                                \
  typedef struct packed                                         \
  {                                                             \
    logic [data_width_mp-1:0]                    data;          \
    bp_``name_mp``_msg_header_s                  header;        \
  } bp_``name_mp``_msg_s;

/*
 * Width Macros
 */

// CCE-MEM Interface
`define bp_mem_msg_payload_width(lce_id_width_mp, lce_assoc_mp) \
  (3+lce_id_width_mp+`BSG_SAFE_CLOG2(lce_assoc_mp)+$bits(bp_coh_states_e))

`define bp_mem_msg_header_width(addr_width_mp, lce_id_width_mp, lce_assoc_mp) \
  ($bits(bp_mem_msg_e)+addr_width_mp \
   +`bp_mem_msg_payload_width(lce_id_width_mp, lce_assoc_mp)\
   +$bits(bp_mem_msg_size_e))

`define bp_mem_msg_width(addr_width_mp, data_width_mp, lce_id_width_mp, lce_assoc_mp) \
  (`bp_mem_msg_header_width(addr_width_mp,lce_id_width_mp,lce_assoc_mp)+data_width_mp)

/*
 *
 * Memory End Interface Macro
 *
 * This macro defines all of the memory end interface struct and port widths at once as localparams
 *
 */

`define declare_bp_mem_if(paddr_width_mp, data_width_mp, lce_id_width_mp, lce_assoc_mp, name_mp) \
  `declare_bp_mem_msg_payload_s(lce_id_width_mp, lce_assoc_mp, name_mp);                         \
  `declare_bp_mem_msg_s(paddr_width_mp, data_width_mp, name_mp);

`define declare_bp_mem_if_widths(paddr_width_mp, data_width_mp, lce_id_width_mp, lce_assoc_mp, name_mp) \
  , localparam ``name_mp``_msg_payload_width_lp = `bp_mem_msg_payload_width(lce_id_width_mp, lce_assoc_mp) \
  , localparam ``name_mp``_msg_header_width_lp  = `bp_mem_msg_header_width(paddr_width_mp, lce_id_width_mp, lce_assoc_mp) \
  , localparam ``name_mp``_msg_width_lp         = `bp_mem_msg_width(paddr_width_mp, data_width_mp, lce_id_width_mp, lce_assoc_mp)


`endif
