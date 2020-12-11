`timescale 1ns / 1ps
//////////////////////////////////////////////////////////////////////////////////
// Company: 
// Engineer: 
// 
// Create Date: 12/04/2020 12:39:45 AM
// Design Name: 
// Module Name: vcache
// Project Name: 
// Target Devices: 
// Tool Versions: 
// Description: 
// 
// Dependencies: 
// 
// Revision:
// Revision 0.01 - File Created
// Additional Comments:
// 
//////////////////////////////////////////////////////////////////////////////////


module vcache
 #( parameter vcache_depth_p = 4
  , parameter block_width_p = 512
  , parameter address_width_p = 32
  , parameter vcache_tag_width_p = address_width_p - $clog2(vcache_depth_p)
   )
(
       input clk_i
  ,    input reset_i

  ,    input data_valid_i
  ,    input [block_width_p-1:0] data_i

  ,    input tag_valid_i
  ,    input [vcache_tag_width_p-1:0] tag_i

 // ,    input [1:0] mem_op //memory operation type, read write
  ,    output logic [block_width_p-1:0] data_o
  ,    output logic valid_o
   // ,    output logic hit_o
);

   localparam vcache_index_lp = $clog2(vcache_depth_p);
   
   logic [vcache_tag_width_p-1 :0] tag_mem  [vcache_depth_p-1:0];

   logic [block_width_p-1:0] data_mem [vcache_depth_p-1:0]; 

   logic [vcache_depth_p-1:0] tag_match_flag ;
   
   logic [vcache_index_lp-1:0] write_index;
   logic [vcache_index_lp-1:0] read_index;
   
   logic hit_lo ;
   logic [block_width_p-1:0] data_lo;

   //logic [vcache_depth_p-1:0] lru_way; //one-hot encoded
   logic [vcache_index_lp-1:0] lru_reg [vcache_depth_p-1:0];

   for(genvar i = 0; i<vcache_depth_p ; i++) begin:tag_match  // compare the tag_mem with the incoming tag and generate a 1 hot encoded signal if there is a match 

      assign tag_match_flag[i] = (tag_mem[i] == tag_i);

   end

   assign hit_lo = (check_one_hot(tag_match_flag) & tag_valid_i) ? 1'b1 : 1'b0 ;   // set hit signal if there is a tag match and tag input is valid
/*
   always_comb
   begin
    data_lo = 'z;
    for(int i = 0; i < vcache_depth_p; i++) begin  // data_o is connected with the matched tag index of the data_mem
      if (tag_match_flag == (1 << i)) begin
         data_lo = data_mem[i];
         index = i;
      end
    end
   end
*/
   //assign read_index = one_hot_to_index(tag_match_flag);
   assign data_lo = data_mem[read_index];

  always_comb
  begin
    for (int i=0; i<vcache_depth_p; i++) begin //4
			if (tag_match_flag == (1 << i)) begin //
				read_index = i; 
			end
	 end
  end


  always@(posedge clk_i) begin // data output is registered at the negedge - reading from victim cache is handled here
    
    if (reset_i) begin

	data_o  =  '0;
	valid_o = 1'b0;

    end else if (hit_lo) begin

	data_o  = data_lo;
	valid_o = 1'b1;

    end else begin

	data_o = '0;
	valid_o = 1'b0;

    end

  end


  for (genvar i = 0; i < vcache_depth_p; i++) begin
	
	  always@(posedge clk_i) begin 
		if (reset_i) begin
			lru_reg[i] = i;
		end
		else if (data_valid_i & tag_valid_i) begin
			if (lru_reg[i]==vcache_depth_p-1) begin // replacing the oldest value
				write_index = i;
				tag_mem[i] = tag_i;
				data_mem[i] = data_i;
				lru_reg[i] = lru_reg[i] + 1;
			end else begin
				lru_reg[i] = lru_reg[i] + 1;
			end
		end
	  end

  end


function  check_one_hot;
	input [vcache_depth_p-1:0] tag_match_flag ;
	integer ones;
	begin
		ones = 0;
		for (int i=0; i<vcache_depth_p; i++) begin
		       ones = ones + tag_match_flag[i];
	        end
		check_one_hot = (ones == 1) ? 1'b1: 1'b0;
	end
endfunction


function one_hot_to_index;
	input [vcache_depth_p-1:0] one_hot ; // 1000 = 8
	logic [vcache_index_lp-1:0] index;
	begin
		for (int i=0; i<vcache_depth_p; i++) begin //4
			if (one_hot == (1 << i)) begin //
				index = i; 
			end
	        end
		one_hot_to_index = index;
	end
endfunction

endmodule
