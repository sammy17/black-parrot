/*
 * bp_me_cce_to_cache_new.v
 *
 */
 
module bp_me_cce_to_cache_new
 import bp_cce_pkg::*;
 import bp_common_pkg::*;
 import bp_common_aviary_pkg::*;
 import bp_me_pkg::*;
 import bsg_cache_pkg::*;
 #(parameter bp_params_e bp_params_p = e_bp_default_cfg
   `declare_bp_proc_params(bp_params_p)
   `declare_bp_mem_if_widths(paddr_width_p, cce_block_width_p, lce_id_width_p, lce_assoc_p, cce_mem)

   , parameter cache_data_width_p = dword_width_p

   , localparam block_size_in_words_lp=cce_block_width_p/dword_width_p
   , localparam lg_sets_lp=`BSG_SAFE_CLOG2(l2_sets_p)
   , localparam lg_ways_lp=`BSG_SAFE_CLOG2(l2_assoc_p)
   , localparam word_offset_width_lp=`BSG_SAFE_CLOG2(block_size_in_words_lp)
   , localparam data_mask_width_lp=(dword_width_p>>3)
   , localparam byte_offset_width_lp=`BSG_SAFE_CLOG2(dword_width_p>>3)
   , localparam block_offset_width_lp=(word_offset_width_lp+byte_offset_width_lp)
   
   , localparam bsg_cache_pkt_width_lp=`bsg_cache_pkt_width(paddr_width_p,dword_width_p)
   , localparam counter_width_lp=`BSG_SAFE_CLOG2(cce_block_width_p/dword_width_p)
   )
  (input                                             clk_i
    , input                                          reset_i

    // BP interface
    , input  [cce_mem_msg_header_width_lp-1:0]       mem_cmd_header_i
    , input [cache_data_width_p-1:0]                 mem_cmd_data_i
    , input                                          mem_cmd_v_i
    , output logic                                   mem_cmd_ready_o
    , input                                          mem_cmd_lock_i

    , output logic [cce_mem_msg_header_width_lp-1:0] mem_resp_header_o
    , output logic [cache_data_width_p-1:0]          mem_resp_data_o
    , output logic                                   mem_resp_v_o
    , input                                          mem_resp_yumi_i
    , output logic                                   mem_resp_lock_o

    // bsg_cache-side
    , output [bsg_cache_pkt_width_lp-1:0]            cache_pkt_o
    , output logic                                   cache_pkt_v_o
    , input                                          cache_pkt_ready_i

    , input [cache_data_width_p-1:0]                 cache_data_i
    , input                                          cache_v_i
    , output logic                                   cache_yumi_o
  );

  `declare_bp_mem_if(paddr_width_p, cce_block_width_p, lce_id_width_p, lce_assoc_p, cce_mem);
  bp_cce_mem_msg_header_s mem_cmd_header, mem_resp_header;
  assign mem_cmd_header = mem_cmd_header_i;
  assign mem_resp_header_o = mem_resp_header;
  
  `declare_bsg_cache_pkt_s(paddr_width_p, dword_width_p);
  bsg_cache_pkt_s cache_pkt;
  assign cache_pkt_o = cache_pkt;

  enum logic [1:0] {e_cmd_reset, e_cmd_clear, e_cmd_ready} cmd_state_n, cmd_state_r;

  wire is_reset = (cmd_state_r == e_cmd_reset);
  wire is_clear = (cmd_state_r == e_cmd_clear);
  wire is_ready = (cmd_state_r == e_cmd_ready);

  logic [lg_sets_lp+lg_ways_lp:0] tagst_sent_r, tagst_sent_n;
  logic [lg_sets_lp+lg_ways_lp:0] tagst_recv_r, tagst_recv_n;
  
  // synopsys sync_set_reset "reset_i"
  always_ff @(posedge clk_i)
    if (reset_i)
      begin
        cmd_state_r      <= e_cmd_reset;
        tagst_sent_r     <= '0;
        tagst_recv_r     <= '0;
      end
    else
      begin
        cmd_state_r      <= cmd_state_n;
        tagst_sent_r     <= tagst_sent_n;
        tagst_recv_r     <= tagst_recv_n;
      end

  // This is a 4-fifo so that a hit stream will not clog the fifo
  //   while waiting for the cache response
  logic mem_cmd_v_li, mem_cmd_ready_lo;
  logic mem_resp_v_lo;
  bsg_fifo_1r1w_small
   #(.width_p($bits(bp_cce_mem_msg_header_s)), .els_p(4))
   stream_fifo
    (.clk_i(clk_i)
     ,.reset_i(reset_i)

     ,.data_i(mem_cmd_header)
     ,.v_i(mem_cmd_v_li)
     ,.ready_o(mem_cmd_ready_lo)

     ,.data_o(mem_resp_header)
     ,.v_o(mem_resp_v_lo)
     ,.yumi_i(mem_resp_yumi_i)
     );
  // Mask the ready signal if we're not ready, or the fifo or cache aren't ready
  assign mem_cmd_ready_o = is_ready & mem_cmd_ready_lo & cache_pkt_ready_i;
  wire is_read  = mem_cmd_header.msg_type inside {e_mem_msg_uc_rd, e_mem_msg_rd};
  wire is_write = mem_cmd_header.msg_type inside {e_mem_msg_uc_rd, e_mem_msg_rd};
  wire is_uc    = (mem_cmd_header.addr < dram_base_addr_gp);
  wire is_tagfl = is_uc & ((mem_cmd_header.addr[0+:20] == cache_tagfl_base_addr_gp));
  wire [paddr_width_p-1:0] tagfl_addr = {mem_cmd_data_i[0+:lg_sets_lp+lg_ways_lp], block_offset_width_lp'(0)};
  wire [paddr_width_p-1:0] cmd_addr   = mem_cmd_header.addr;
  assign mem_resp_data = cache_data_i;

  // At the reset, this module intializes all the tags and valid bits to zero.
  //   After all the tags are completedly initialized, this module starts
  //   accepting incoming commands
  always_comb
    begin
      cache_pkt     = '0;
      cache_pkt_v_o = 1'b0;

      mem_cmd_v_li    = 1'b0;
      
      tagst_sent_n = tagst_sent_r;
      tagst_recv_n = tagst_recv_r;
      cmd_state_n  = cmd_state_r;

      case (cmd_state_r)
        e_cmd_reset: cmd_state_n = e_cmd_clear;
        e_cmd_clear:
          begin
            cache_pkt.opcode = TAGST;
            cache_pkt.data = '0;
            cache_pkt.addr = {
              {(paddr_width_p-lg_sets_lp-lg_ways_lp-block_offset_width_lp){1'b0}},
              tagst_sent_r[0+:lg_sets_lp+lg_ways_lp],
              {(block_offset_width_lp){1'b0}}
            };

            cache_pkt_v_o = cache_pkt_ready_i & (tagst_sent_r != (l2_assoc_p*l2_sets_p));
            tagst_sent_n = tagst_sent_r + cache_pkt_v_o;
            tagst_recv_n = tagst_recv_r + cache_v_i;
            cmd_state_n = (tagst_recv_r == l2_assoc_p*l2_sets_p) ? e_cmd_ready : e_cmd_clear;
          end
        e_cmd_ready:
          begin
            case ({is_tagfl, mem_cmd_header.size})
              {1'b1, 3'b???          }: cache_pkt.opcode = TAGFL;
              {1'b0, e_mem_msg_size_1}: cache_pkt.opcode = is_read ? LB : SB;
              {1'b0, e_mem_msg_size_2}: cache_pkt.opcode = is_read ? LH : SH;
              {1'b0, e_mem_msg_size_4}: cache_pkt.opcode = is_read ? LW : SH;
              {1'b0, 3'b???          }: cache_pkt.opcode = is_read ? LD : SD;
            endcase

            cache_pkt.addr = is_tagfl ? tagfl_addr : cmd_addr;
            cache_pkt.data = mem_cmd_data_i;
            // This mask is only used for the LM/SM operations for >64 bit mask operations
            cache_pkt.mask = '1;
            cache_pkt_v_o  = cache_pkt_ready_i;

            mem_resp_v_o    = mem_resp_v_lo & cache_v_i;
            mem_resp_lock_o = mem_resp_v_lo;
            cache_yumi_o    = mem_resp_yumi_i;
          end
      endcase
    end
  
endmodule

