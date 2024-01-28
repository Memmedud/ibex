// Copyright lowRISC contributors.
// Copyright 2018 ETH Zurich and University of Bologna, see also CREDITS.md.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

/**
 * Special multiplier for P-extension
 */

module ibex_mult_pext (
  //input  logic             clk_i,
  //input  logic             rst_ni,

  //input  logic             mult_en_i,  // dynamic enable signal, for FSM control
  //input  logic             mult_sel_i, // static decoder output, for data muxes
  input  ibex_pkg_pext::zpn_op_e operator_i,
  input  ibex_pkg_pext::signed_type_e signed_operands_i,
  input  logic [31:0]      op_a_i,
  input  logic [31:0]      op_b_i,
  //input  logic [33:0]      alu_adder_ext_i,
  //input  logic [31:0]      alu_adder_i,
  //input  logic             equal_to_zero_i,
  //input  logic             data_ind_timing_i,

  //output logic [32:0]      alu_operand_a_o,
  //output logic [32:0]      alu_operand_b_o,

  //input  logic [33:0]      imd_val_q_i[2],
  //output logic [33:0]      imd_val_d_o[2],
  //output logic [1:0]       imd_val_we_o,

  //input  logic             multdiv_ready_id_i,

  output logic [31:0]      mult_result_o
  //output logic             valid_o
);

  import ibex_pkg_pext::*;

  // We only operate at one halfword per cycle;
  logic[15:0]   mult_op_a0, mult_op_a1;     // Assign these inside the FSM
  logic[7:0]    mult_op_b0, mult_op_b1;     // Assign these inside the FSM
  logic[25:0]   mult_res0,  mult_res1;       // Results will be 26 bits wide

  logic[35:0] unused_bits;
  assign unused_bits = {mult_res0[25:24], mult_res1[25:24], op_a_i[31:16], op_b_i[31:16]};

  logic         signed_mult;
  logic         width16;
  logic         crossed;

  // Decode control signals
  always_comb begin
    unique case (signed_operands_i)
      S16, S8:  signed_mult = 1'b1;
      default:  signed_mult = 1'b0;
    endcase
  end

  always_comb begin
    unique case (signed_operands_i)
      S16, U16:  width16 = 1'b1;
      default:   width16 = 1'b0;
    endcase
  end

  always_comb begin
    unique case (operator_i)
      ZPN_UMULX16, ZPN_UMULX8,
      ZPN_SMULX16, ZPN_SMULX8:  crossed = 1'b1;
      default:                  crossed = 1'b0;
    endcase
  end

  logic second_half;      // TODO: Set in FSM
  assign second_half = 1'b0;

  // 8-bit mults will take 2 cycles     // Bottleneck is register file only having one write port
  // 16-bit mults will take 2 cycles    
  // MAC will take 3 cycles
  // Saturating mults will take 2 cycles

  // Prepare operand A
  always_comb begin
    unique case(width16)
      1'b1 : begin
        mult_op_a0 = second_half ? op_a_i[31:16] : op_a_i[15:0];
        mult_op_a1 = second_half ? op_a_i[31:16] : op_a_i[15:0];
      end

      1'b0 : begin
        mult_op_a0 = second_half ? { {8{op_a_i[23] & signed_mult}}, op_a_i[23:16]} : { {8{op_a_i[7] & signed_mult}}, op_a_i[7:0]};
        mult_op_a1 = second_half ? { {8{op_a_i[31] & signed_mult}}, op_a_i[31:24]} : { {8{op_a_i[15] & signed_mult}}, op_a_i[15:8]};
      end
    endcase
  end

  // Prepare operand B
  always_comb begin
    unique case(~width16 & crossed)
      1'b1 : begin
        mult_op_b0 = second_half ? op_b_i[31:24] : op_b_i[15:8];
        mult_op_b1 = second_half ? op_b_i[23:16] : op_b_i[7:0];
      end

      1'b0 : begin
        mult_op_b0 = (second_half ^ crossed) ? op_b_i[23:16] : op_b_i[7:0];
        mult_op_b1 = (second_half ^ crossed) ? op_b_i[31:24] : op_b_i[15:8];
      end
    endcase
  end

  // A is 16-bit, B is 8-bit, +1 bit for sign extension
  // Actual multipliers
  assign mult_res0 = $signed({signed_mult & mult_op_a0[15], mult_op_a0}) * $signed({signed_mult & mult_op_b0[7] & ~width16, mult_op_b0});
  assign mult_res1 = $signed({signed_mult & mult_op_a1[15], mult_op_a1}) * $signed({signed_mult & mult_op_b1[7], mult_op_b1});

  // Generate 16-bit result
  logic[31:0] width16_mult_result;
  assign width16_mult_result = {{mult_res1[23:0] +  { {8{mult_res0[23]}}, mult_res0[23:8]}}[23:0], mult_res0[7:0]};
  
  // Generate 8-bit result
  logic[31:0] width8_mult_result;
  assign width8_mult_result  = {mult_res1[15:0], mult_res0[15:0]};

  // Final result mux
  always_comb begin
    mult_result_o = '0;

    unique case (width16)
      1'b0:   mult_result_o = width8_mult_result;
      1'b1:   mult_result_o = width16_mult_result;
    endcase
  end

  /*
  // FSM state enum
  typedef enum logic[1:0] {
    ALBL, ALBH, AHBL, AHBH
  } mult_pext_fsm_e;
  mult_pext_fsm_e mult_state, mult_state_next;

  // FSM state decoding
  always_comb begin
    unique case (mult_state)
      ALBL: begin
        mult_op_a0    = op_a_i[7:0];
        mult_op_a1    = op_a_i[15:8];
        mult_op_b0    = op_b_i[7:0];
        mult_op_b1    = op_b_i[15:8];
      end

      ALBH: begin

      end

      AHBL: begin

      end

      AHBH: begin

      end

      default: ;
    endcase
  end

  // FSM state clocking
  always_ff @(posedge clk_i or negedge rst_ni) begin
    if (~rst_ni) begin
      mult_state <= // Default state
    end
    else begin
      if (mult_en) begin
        mult_state <= mult_state_next;
      end
    end
  end*/

endmodule
