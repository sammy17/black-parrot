
module bp_stream_to_lite
 import bp_common_pkg::*;
 import bp_common_aviary_pkg::*;
 import bp_me_pkg::*;
 #(parameter bp_params_e bp_params_p = e_bp_default_cfg
   `declare_bp_proc_params(bp_params_p)

   , parameter in_data_width_p  = "inv"
   , parameter out_data_width_p = "inv"

   , parameter logic master_p = 0

   `declare_bp_mem_if_widths(paddr_width_p, in_data_width_p, lce_id_width_p, lce_assoc_p, in_mem)
   `declare_bp_mem_if_widths(paddr_width_p, out_data_width_p, lce_id_width_p, lce_assoc_p, out_mem)
   )
  (input                                     clk_i
   , input                                   reset_i

   // Master BP Stream
   , input [out_mem_msg_header_width_lp-1:0] mem_header_i
   , input [out_data_width_p-1:0]            mem_data_i
   , input                                   mem_v_i
   , input                                   mem_ready_o
   , input                                   mem_lock_i

   // Client BP Lite
   , output logic [in_mem_msg_width_lp-1:0]  mem_o
   , output logic                            mem_v_o
   , input                                   mem_yumi_i
   );

  `declare_bp_mem_if(paddr_width_p, cce_block_width_p, lce_id_width_p, lce_assoc_p, in_mem);
  `declare_bp_mem_if(paddr_width_p, cce_block_width_p, lce_id_width_p, lce_assoc_p, out_mem);
  bp_out_mem_msg_s mem_cast_o;
  assign mem_o = mem_cast_o;

  localparam in_data_bytes_lp = in_data_width_p/8;
  localparam out_data_bytes_lp = out_data_width_p/8;
  localparam stream_words_lp = in_data_width_p/out_data_width_p;
  localparam data_ptr_width_lp = `BSG_SAFE_CLOG2(stream_words_lp);
  localparam stream_offset_width_lp = `BSG_SAFE_CLOG2(out_data_bytes_lp);

  bp_in_mem_msg_header_s header_lo;
  logic mem_v_lo, mem_yumi_li;
  bsg_one_fifo
   #(.width_p($bits(bp_in_mem_msg_header_s)))
   header_fifo
    (.clk_i(clk_i)
     ,.reset_i(reset_i)

     ,.data_i(mem_header_i)
     // We ready on ready/and failing on the stream after the first
     ,.v_i(mem_v_i)

     ,.data_o(header_lo)
     ,.v_o(mem_v_lo)
     ,.yumi_i(mem_yumi_li)

     // We rely on sipo handshaking
     ,.ready_o(/* Unused */)
     );

  logic [out_data_width_p-1:0] data_lo;
  wire is_wr = mem_cast_i.header.msg_type inside {e_mem_msg_uc_wr, e_mem_msg_wr};
  wire [data_ptr_width_lp-1:0] num_stream_cmds = (master_p ^ is_wr)
    ? 1'b1
    : `BSG_MAX(((1'b1 << mem_lo.size) / out_data_bytes_lp), 1'b1);
  bsg_serial_in_parallel_out_dynamic
   #(.width_p(out_data_width_p), .max_els_p(stream_words_lp))
   sipo
    (.clk_i(clk_i)
     ,.reset_i(reset_i)

     ,.data_i(mem_data_i)
     ,.len_i(num_stream_cmds)
     ,.v_i(mem_v_i)
     ,.ready_o(mem_ready_o)

     ,.data_o(data_lo)
     ,.v_o(mem_v_o)
     ,.yumi_i(mem_yumi_i)

     ,.len_ready_o(/* Unused */)
     );

  wire unused = &{mem_lock_i};

  assign mem_cast_o = '{header: header, data: data_lo};
  assign mem_o = mem_cast_o;

  //synopsys translate_off
  initial
    begin
      assert (in_data_width_p < out_data_width_p)
        else $error("Master data cannot be larger than client");
      assert (out_data_width_p % in_data_width_p)
        else $error("Client data must be a multiple of master data");
    end
  //synopsys translate_on

endmodule

