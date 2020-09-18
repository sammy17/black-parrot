/**
 *
 * Name:
 *   bp_be_pipe_sys.v
 *
 * Description:
 *
 * Notes:
 *
 */
module bp_be_pipe_sys
 import bp_common_pkg::*;
 import bp_common_aviary_pkg::*;
 import bp_common_rv64_pkg::*;
 import bp_be_pkg::*;
 #(parameter bp_params_e bp_params_p = e_bp_default_cfg
   `declare_bp_proc_params(bp_params_p)

   , localparam cfg_bus_width_lp       = `bp_cfg_bus_width(vaddr_width_p, core_id_width_p, cce_id_width_p, lce_id_width_p, cce_pc_width_p, cce_instr_width_p)
   , localparam calc_status_width_lp   = `bp_be_calc_status_width(vaddr_width_p)
   , localparam csr_cmd_width_lp       = `bp_be_csr_cmd_width
   // Generated parameters
   , localparam dispatch_pkt_width_lp = `bp_be_dispatch_pkt_width(vaddr_width_p)
   , localparam exception_width_lp    = `bp_be_exception_width
   , localparam ptw_miss_pkt_width_lp = `bp_be_ptw_miss_pkt_width(vaddr_width_p)
   , localparam ptw_fill_pkt_width_lp = `bp_be_ptw_fill_pkt_width(vaddr_width_p)
   , localparam commit_pkt_width_lp   = `bp_be_commit_pkt_width(vaddr_width_p)
   , localparam trans_info_width_lp   = `bp_be_trans_info_width(ptag_width_p)
   , localparam wb_pkt_width_lp       = `bp_be_wb_pkt_width(vaddr_width_p)
   )
  (input                                  clk_i
   , input                                reset_i

   , input [cfg_bus_width_lp-1:0]         cfg_bus_i

   , input [dispatch_pkt_width_lp-1:0]    reservation_i

   , input                                btaken_int1
   , input [vaddr_width_p-1:0]            br_tgt_int1
   , input                                pipe_long_ready_i
   , input                                pipe_mem_ready_i

   // TODO: Get rid of kill
   , input                                kill_ex1_i
   , input                                kill_ex2_i
   , input                                kill_ex3_i
   , input                                flush_i

   , input                                dtlb_miss_i
   , input                                dcache_miss_i
   , input                                fencei_i
   , input                                load_misaligned_i
   , input                                load_access_fault_i
   , input                                load_page_fault_i
   , input                                store_misaligned_i
   , input                                store_access_fault_i
   , input                                store_page_fault_i

   , output [calc_status_width_lp-1:0]    calc_status_o

   , input [exception_width_lp-1:0]       exception_i
   , input [vaddr_width_p-1:0]            exception_pc_i
   , input [vaddr_width_p-1:0]            exception_vaddr_i

   , output [ptw_miss_pkt_width_lp-1:0]   ptw_miss_pkt_o
   , input [ptw_fill_pkt_width_lp-1:0]    ptw_fill_pkt_i

   , output [wb_pkt_width_lp-1:0]         iwb_pkt_o
   , output [wb_pkt_width_lp-1:0]         fwb_pkt_o

   , output logic                         miss_v_o
   , output logic                         exc_v_o
   , output logic [dpath_width_p-1:0]     data_o

   , input [wb_pkt_width_lp-1:0]          fast_iwb_pkt_o
   , input [wb_pkt_width_lp-1:0]          fast_fwb_pkt_o
   , output [wb_pkt_width_lp-1:0]         slow_iwb_pkt_i
   , output [wb_pkt_width_lp-1:0]         slow_fwb_pkt_i

   , output [commit_pkt_width_lp-1:0]     commit_pkt_o

   , input                                interrupt_v_i
   , output                               interrupt_ready_o
   , input                                timer_irq_i
   , input                                software_irq_i
   , input                                external_irq_i

   , output [trans_info_width_lp-1:0]     trans_info_o
   , output rv64_frm_e                    frm_dyn_o
   , output                               fpu_en_o
   );

  `declare_bp_be_internal_if_structs(vaddr_width_p, paddr_width_p, asid_width_p, branch_metadata_fwd_width_p);
  `declare_bp_be_mem_structs(vaddr_width_p, ppn_width_p, lce_sets_p, cce_block_width_p/8)

  bp_be_dispatch_pkt_s reservation;
  bp_be_decode_s decode;
  bp_be_csr_cmd_s csr_cmd_li, csr_cmd_r, csr_cmd_lo;
  rv64_instr_s instr;
  bp_be_ptw_miss_pkt_s ptw_miss_pkt;
  bp_be_ptw_fill_pkt_s ptw_fill_pkt;
  bp_be_commit_pkt_s commit_pkt;
  bp_be_wb_pkt_s fast_iwb_pkt, fast_fwb_pkt;
  bp_be_wb_pkt_s slow_iwb_pkt, slow_fwb_pkt;
  bp_be_trans_info_s trans_info;
  bp_be_calc_status_s calc_status;

  assign ptw_miss_pkt_o = ptw_miss_pkt;
  assign ptw_fill_pkt = ptw_fill_pkt_i;
  assign commit_pkt_o = commit_pkt;
  assign fast_iwb_pkt = fast_iwb_pkt_i;
  assign fast_fwb_pkt = fast_fwb_pkt_i;
  assign trans_info_o = trans_info;

  assign reservation = reservation_i;
  assign decode = reservation.decode;
  assign instr  = reservation.instr;
  wire [vaddr_width_p-1:0] pc  = reservation.pc[0+:vaddr_width_p];
  wire [dword_width_p-1:0] rs1 = reservation.rs1[0+:dword_width_p];
  wire [dword_width_p-1:0] rs2 = reservation.rs2[0+:dword_width_p];
  wire [dword_width_p-1:0] imm = reservation.imm[0+:dword_width_p];

  wire csr_imm_op = decode.fu_op inside {e_csrrwi, e_csrrsi, e_csrrci};

  always_comb
    begin
      csr_cmd_li.csr_op   = decode.fu_op;
      csr_cmd_li.csr_addr = instr.t.itype.imm12;
      csr_cmd_li.data     = csr_imm_op ? imm : rs1;
      csr_cmd_li.exc      = '0;
    end

  logic csr_cmd_v_lo;
  bsg_shift_reg
   #(.width_p($bits(bp_be_csr_cmd_s))
     ,.stages_p(2)
     )
   csr_shift_reg
    (.clk(clk_i)
     ,.reset_i(reset_i)

     ,.valid_i(decode.csr_v)
     ,.data_i(csr_cmd_li)

     ,.valid_o(csr_cmd_v_lo)
     ,.data_o(csr_cmd_r)
     );

  // Track if an incoming tlb miss is store or load
  logic is_store_r;
  bsg_dff_chain
   #(.width_p(1)
     ,.num_stages_p(2)
     )
   store_reg
    (.clk_i(clk_i)

     ,.data_i(decode.dcache_w_v)
     ,.data_o(is_store_r)
     );

  always_comb
    begin
      ptw_miss_pkt.instr_miss_v = ~kill_ex3_i & csr_cmd_lo.exc.itlb_miss;
      ptw_miss_pkt.load_miss_v = ~kill_ex3_i & csr_cmd_lo.exc.dtlb_miss & ~is_store_r;
      ptw_miss_pkt.store_miss_v = ~kill_ex3_i & csr_cmd_lo.exc.dtlb_miss & is_store_r;
      ptw_miss_pkt.pc = exception_pc_i;
      ptw_miss_pkt.vaddr = csr_cmd_lo.exc.itlb_miss ? exception_pc_i : exception_vaddr_i;
    end

  always_comb
    begin
      csr_cmd_lo = csr_cmd_r;

      if (ptw_fill_pkt.instr_page_fault_v)
        begin
          csr_cmd_lo.exc.instr_page_fault = 1'b1;
        end
      else if (ptw_fill_pkt.store_page_fault_v)
        begin
          csr_cmd_lo.exc.store_page_fault = 1'b1;
        end
      else if (ptw_fill_pkt.load_page_fault_v)
        begin
          csr_cmd_lo.exc.load_page_fault = 1'b1;
        end
      else
        begin
          // Override data width vaddr for dtlb fill
          // Kill exception on ex3
          csr_cmd_lo.exc = kill_ex3_i ? '0 : exception_i;
          csr_cmd_lo.data = csr_cmd_lo.data;
        end
    end

  wire commit_pkt_v_i = calc_stage_r[2].v & ~exc_stage_r[2].poison_v;
  wire commit_pkt_queue_v_i = calc_stage_r[2].v & ~exc_stage_r[2].roll_v;
  wire commit_pkt_instret_i = calc_stage_r[2].v & ~exc_stage_r[2].poison_v & ~exc_v_o & ~miss_v_o;
  wire [vaddr_width_p-1:0] commit_pkt_pc_i = calc_stage_r[2].pc;
  wire [vaddr_width_p-1:0] commit_pkt_npc_i = calc_stage_r[1].pc;
  wire [instr_width_p-1:0] commit_pkt_instr_i = calc_stage_r[2].instr;

  wire ptw_page_fault_v  = ptw_fill_pkt.instr_page_fault_v | ptw_fill_pkt.load_page_fault_v | ptw_fill_pkt.store_page_fault_v;
  wire exception_v_li = ptw_page_fault_v | commit_pkt_v_i;
  wire [vaddr_width_p-1:0] exception_pc_li = ptw_page_fault_v ? ptw_fill_pkt.pc : commit_pkt_pc_i;
  wire [vaddr_width_p-1:0] exception_npc_li = ptw_page_fault_v ? '0 : commit_pkt_npc_i;
  wire [vaddr_width_p-1:0] exception_vaddr_li = ptw_page_fault_v ? ptw_fill_pkt.vaddr : exception_vaddr_i;
  wire [instr_width_p-1:0] exception_instr_li = commit_pkt_instr_i;

  logic [dword_width_p-1:0] csr_data_lo;
  bp_be_csr
   #(.bp_params_p(bp_params_p))
    csr
    (.clk_i(clk_i)
     ,.reset_i(reset_i)

     ,.cfg_bus_i(cfg_bus_i)

     ,.csr_cmd_i(csr_cmd_lo)
     ,.csr_cmd_v_i(csr_cmd_v_lo & ~kill_ex3_i)
     ,.csr_data_o(csr_data_lo)

     ,.instret_i(commit_pkt_instret_i)
     ,.fflags_acc_i(iwb_pkt.fflags_acc | fwb_pkt.fflags_acc)
     ,.frf_w_v_i(fwb_pkt.rd_w_v)

     ,.commit_pkt_v_i(commit_pkt_v_i)
     ,.commit_pkt_queue_v_i(commit_pkt_queue_v_i)

     ,.exception_v_i(exception_v_li)
     ,.exception_pc_i(exception_pc_li)
     ,.exception_npc_i(exception_npc_li)
     ,.exception_vaddr_i(exception_vaddr_li)
     ,.exception_instr_i(exception_instr_li)

     ,.timer_irq_i(timer_irq_i)
     ,.software_irq_i(software_irq_i)
     ,.external_irq_i(external_irq_i)
     ,.interrupt_ready_o(interrupt_ready_o)
     ,.interrupt_v_i(interrupt_v_i)

     ,.commit_pkt_o(commit_pkt)
     ,.trans_info_o(trans_info)
     ,.frm_dyn_o(frm_dyn_o)
     ,.fpu_en_o(fpu_en_o)
     );

  // If a pipeline has completed an instruction (pipe_xxx_v), then mux in the calculated result.
  // Else, mux in the previous stage of the completion pipe. Since we are single issue and have
  //   static latencies, we cannot have two pipelines complete at the same time.
  assign pipe_fma_data_lo_v       = calc_stage_r[4].pipe_fma_v;
  assign pipe_mul_data_lo_v       = calc_stage_r[3].pipe_mul_v;
  assign pipe_sys_data_lo_v       = calc_stage_r[2].pipe_sys_v;
  assign pipe_mem_final_data_lo_v = calc_stage_r[2].pipe_mem_final_v;
  assign pipe_mem_early_data_lo_v = calc_stage_r[1].pipe_mem_early_v;
  assign pipe_aux_data_lo_v       = calc_stage_r[1].pipe_aux_v;
  assign pipe_int_data_lo_v       = calc_stage_r[0].pipe_int_v;
  assign pipe_ctl_data_lo_v       = calc_stage_r[0].pipe_ctl_v;

  localparam pipe_stage_els_lp = 6;
  bp_be_pipe_stage_reg_s [pipe_stage_els_lp-1:0] calc_stage_r;
  always_comb
    begin
      // Strip out elements of the dispatch packet that we want to save for later
      calc_stage_r[0].pc               = reservation.pc;
      calc_stage_r[0].instr            = reservation.instr;
      calc_stage_r[0].v                = reservation.v;
      calc_stage_r[0].pipe_ctl_v       = reservation.decode.pipe_ctl_v;
      calc_stage_r[0].pipe_aux_v       = reservation.decode.pipe_aux_v;
      calc_stage_r[0].pipe_int_v       = reservation.decode.pipe_int_v;
      calc_stage_r[0].pipe_mem_early_v = reservation.decode.pipe_mem_early_v;
      calc_stage_r[0].pipe_mem_final_v = reservation.decode.pipe_mem_final_v;
      calc_stage_r[0].pipe_sys_v       = reservation.decode.pipe_sys_v;
      calc_stage_r[0].pipe_mul_v       = reservation.decode.pipe_mul_v;
      calc_stage_r[0].pipe_fma_v       = reservation.decode.pipe_fma_v;
      calc_stage_r[0].pipe_long_v      = reservation.decode.pipe_long_v;
      calc_stage_r[0].mem_v            = reservation.decode.mem_v;
      calc_stage_r[0].csr_v            = reservation.decode.csr_v;
      calc_stage_r[0].irf_w_v          = reservation.decode.irf_w_v;
      calc_stage_r[0].frf_w_v          = reservation.decode.frf_w_v;
      calc_stage_r[0].fflags_w_v       = reservation.decode.fflags_w_v;
    end

  always_ff @(posedge clk_i)
    begin
      calc_stage_r[pipe_stage_els_lp-1:1] <= calc_stage_r[0+:pipe_stage_els_lp-1];
    end

  // Exception aggregation
  localparam commit_point_lp = 3;
  bp_be_exc_stage_s [commit_point_lp:0] exc_stage_n, exc_stage_r;
  always_comb
    begin
      // Calculator status EX1 information
      calc_status.ex1_v                    = ~exc_stage_r[0].poison_v;
      calc_status.ex1_npc                  = br_tgt_int1;
      calc_status.ex1_br_or_jmp            = reservation.decode.pipe_ctl_v;
      calc_status.ex1_btaken               = btaken_int1;

      calc_status.long_busy                = ~pipe_long_ready_i;
      calc_status.mem_busy                 = ~pipe_mem_ready_i;
      calc_status.commit_v                 = commit_pkt.v;

      // Dependency information for pipelines
      for (integer i = 0; i < pipe_stage_els_lp; i++)
        begin : dep_status
          calc_status.dep_status[i].instr_v    = calc_stage_r[i].v                & ~exc_stage_n[i+1].poison_v;
          calc_status.dep_status[i].csr_v      = calc_stage_r[i].csr_v            & ~exc_stage_n[i+1].poison_v;
          calc_status.dep_status[i].mem_v      = calc_stage_r[i].mem_v            & ~exc_stage_n[i+1].poison_v;
          calc_status.dep_status[i].fflags_w_v = calc_stage_r[i].fflags_w_v       & ~exc_stage_n[i+1].poison_v;
          calc_status.dep_status[i].ctl_iwb_v  = calc_stage_r[i].pipe_ctl_v       & ~exc_stage_n[i+1].poison_v & calc_stage_r[i].irf_w_v;
          calc_status.dep_status[i].aux_iwb_v  = calc_stage_r[i].pipe_aux_v       & ~exc_stage_n[i+1].poison_v & calc_stage_r[i].irf_w_v;
          calc_status.dep_status[i].aux_fwb_v  = calc_stage_r[i].pipe_aux_v       & ~exc_stage_n[i+1].poison_v & calc_stage_r[i].frf_w_v;
          calc_status.dep_status[i].int_iwb_v  = calc_stage_r[i].pipe_int_v       & ~exc_stage_n[i+1].poison_v & calc_stage_r[i].irf_w_v;
          calc_status.dep_status[i].emem_iwb_v = calc_stage_r[i].pipe_mem_early_v & ~exc_stage_n[i+1].poison_v & calc_stage_r[i].irf_w_v;
          calc_status.dep_status[i].emem_fwb_v = calc_stage_r[i].pipe_mem_early_v & ~exc_stage_n[i+1].poison_v & calc_stage_r[i].frf_w_v;
          calc_status.dep_status[i].fmem_iwb_v = calc_stage_r[i].pipe_mem_final_v & ~exc_stage_n[i+1].poison_v & calc_stage_r[i].irf_w_v;
          calc_status.dep_status[i].fmem_fwb_v = calc_stage_r[i].pipe_mem_final_v & ~exc_stage_n[i+1].poison_v & calc_stage_r[i].frf_w_v;
          calc_status.dep_status[i].mul_iwb_v  = calc_stage_r[i].pipe_mul_v       & ~exc_stage_n[i+1].poison_v & calc_stage_r[i].irf_w_v;
          calc_status.dep_status[i].fma_fwb_v  = calc_stage_r[i].pipe_fma_v       & ~exc_stage_n[i+1].poison_v & calc_stage_r[i].frf_w_v;
          calc_status.dep_status[i].rd_addr    = calc_stage_r[i].instr.t.rtype.rd_addr;
        end

      // Aggregate exceptions
      for (integer i = 0; i <= commit_point_lp; i++)
        begin : exc_stage
          // Normally, shift down in the pipe
          exc_stage_n[i] = (i == 0) ? '0 : exc_stage_r[i-1];
        end
          exc_stage_n[0].roll_v          |= commit_pkt.rollback;
          exc_stage_n[1].roll_v          |= commit_pkt.rollback;
          exc_stage_n[2].roll_v          |= commit_pkt.rollback;

          exc_stage_n[0].poison_v        |= flush_i;
          exc_stage_n[1].poison_v        |= flush_i | ~reservation.v;
          exc_stage_n[2].poison_v        |= flush_i;
          // Make 2, and just kill commit
          exc_stage_n[3].poison_v        |= commit_pkt.rollback
                                            | commit_pkt.exception
                                            | (ptw_miss_pkt.instr_miss_v | ptw_miss_pkt.load_miss_v | ptw_miss_pkt.store_miss_v);

          exc_stage_n[1].exc.itlb_miss          = reservation.decode.itlb_miss;
          exc_stage_n[1].exc.instr_access_fault = reservation.decode.instr_access_fault;
          exc_stage_n[1].exc.instr_page_fault   = reservation.decode.instr_page_fault;
          exc_stage_n[1].exc.illegal_instr      = reservation.decode.illegal_instr;
          exc_stage_n[1].exc.dtlb_miss          = dtlb_miss_i;

          exc_stage_n[2].exc.dcache_miss        = dcache_miss_i;
          exc_stage_n[2].exc.fencei_v           = fencei_i;
          exc_stage_n[2].exc.load_misaligned    = load_misaligned_i;
          exc_stage_n[2].exc.load_access_fault  = load_access_fault_i;
          exc_stage_n[2].exc.load_page_fault    = load_page_fault_i;
          exc_stage_n[2].exc.store_misaligned   = store_misaligned_i;
          exc_stage_n[2].exc.store_access_fault = store_access_fault_i;
          exc_stage_n[2].exc.store_page_fault   = store_page_fault_i;
    end

  always_ff @(posedge clk_i)
    begin
      exc_stage_r <= exc_stage_n;
    end

  assign data_o           = csr_data_lo;
  assign exc_v_o          = commit_pkt.exception | (ptw_miss_pkt.instr_miss_v | ptw_miss_pkt.load_miss_v | ptw_miss_pkt.store_miss_v);
  assign miss_v_o         = commit_pkt.rollback;

  assign iwb_pkt.rd_w_v     = calc_stage_r[4].irf_w_v & ~exc_stage_r[4].poison_v;
  assign iwb_pkt.rd_addr    = calc_stage_r[4].instr.t.rtype.rd_addr;
  assign iwb_pkt.rd_data    = comp_stage_r[4].data;
  assign iwb_pkt.fflags_acc = comp_stage_r[4].fflags & {5{calc_stage_r[4].fflags_w_v & ~exc_stage_r[4].poison_v}};

  assign fwb_pkt.rd_w_v      = calc_stage_r[5].frf_w_v & ~exc_stage_r[5].poison_v;
  assign fwb_pkt.rd_addr     = calc_stage_r[5].instr.t.rtype.rd_addr;
  assign fwb_pkt.rd_data     = comp_stage_r[5].data;
  assign fwb_pkt.fflags_acc  = comp_stage_r[5].fflags & {5{calc_stage_r[5].fflags_w_v & ~exc_stage_r[5].poison_v}};


endmodule

