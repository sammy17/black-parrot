/*
 * bp_me_pkg.vh
 *
 * Contains the interface structures used for communicating between the CCE and Memory.
 *
 */

package bp_me_pkg;

  `include "bsg_defines.v"
  `include "bp_common_mem_if.vh"
  `include "bp_mem_wormhole.vh"

  localparam mem_cmd_payload_mask_gp  = (1 << e_mem_msg_uc_wr) | (1 << e_mem_msg_wr);
  localparam mem_resp_payload_mask_gp = (1 << e_mem_msg_uc_rd) | (1 << e_mem_msg_rd);

endpackage : bp_me_pkg

