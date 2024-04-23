// Copyright lowRISC contributors.
// Copyright 2018 ETH Zurich and University of Bologna, see also CREDITS.md.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

`define OP_L 15:0
`define OP_H 31:16

/*
 * Special multiplier for P-extension
 */

module ibex_mult_pext (
  input  logic                      clk_i,
  input  logic                      rst_ni,

  input  logic                      multdiv_en_i,
  input  logic                      mult_en_i,
  input  logic                      div_en_i,
  input  logic                      mult_sel_i,
  input  logic                      div_sel_i,

  input  ibex_pkg_pext::zpn_op_e    zpn_operator_i,
  input  logic                      zpn_instr_i,
  input  ibex_pkg::alu_op_e         alu_operator_i,
  input  logic[1:0]                 signed_mode_i,
  input  ibex_pkg::md_op_e          md_operator_i,

  input  logic[31:0]                op_a_i,
  input  logic[31:0]                op_b_i,
  input  logic[31:0]                rd_val_i,
  
  input  logic[31:0]                alu_adder_i,
  input  logic                      equal_to_zero_i,
  input  logic                      data_ind_timing_i,

  output logic [31:0]               alu_operand_a_o,
  output logic [31:0]               alu_operand_b_o,

  input  logic[33:0]                imd_val_q_i[2],
  output logic[33:0]                imd_val_d_o[2],
  output logic[1:0]                 imd_val_we_o,

  input  logic                      multdiv_ready_id_i,

  output logic[31:0]                multdiv_result_o,
  output logic                      valid_o,
  output logic                      set_ov_o
);

  import ibex_pkg_pext::*;
  import ibex_pkg::*;

  // TODO
  assign set_ov_o = 1'b0;

  // Intermediate value register
  logic       multdiv_en;
  logic[1:0]  imd_val_we_div, imd_val_we_mult;
  logic[31:0] op_denominator_d;
  logic[33:0] op_remainder_d;
  logic[33:0] imd_val_d_mult;
    
  assign multdiv_en     = mult_en_internal | div_en_internal;
  assign imd_val_we_o   = {div_en_internal, multdiv_en};
  assign imd_val_d_o[0] = div_sel_i ? op_remainder_d : mult_res_d;
  assign imd_val_d_o[1] = {2'b0, op_denominator_d};

  ////////////////////
  // Decoder helper //
  ////////////////////
  ibex_pkg_pext::mult_pext_mode_e mult_mode;
  logic[1:0]                      cycle_count;
  logic[1:0]                      accum_sub;
  logic                           dsum_mult;
  logic                           crossed, accum_en;

  ibex_mult_pext_helper mult_pext_helper_i (
    .zpn_operator_i   (zpn_operator_i),
    .md_operator_i    (md_operator_i),
    .alu_operator_i   (alu_operator_i),
    .mult_mode_o      (mult_mode),
    .cycle_count_o    (cycle_count),
    .accum_sub_o      (accum_sub),
    .dsum_mult_o      (dsum_mult),
    .crossed_o        (crossed),
    .accum_o          (accum_en)
  );


  //////////    __  __       _ _   _       _ _              //////////
  //////////   |  \/  |     | | | (_)     | (_)             //////////
  //////////   | \  / |_   _| | |_ _ _ __ | |_  ___ _ __    //////////
  //////////   | |\/| | | | | | __| | '_ \| | |/ _ \ '__|   //////////
  //////////   | |  | | |_| | | |_| | |_) | | |  __/ |      //////////
  //////////   |_|  |_|\__,_|_|\__|_| .__/|_|_|\___|_|      //////////
  //////////                        | |                     //////////
  //////////                        |_|                     //////////

  logic[31:0] mult_result;

  // All mults are signed except for UMAQA and SMAQA.su
  logic[1:0] zpn_signed_mult, signed_mult;
  assign zpn_signed_mult = {~(zpn_operator_i == ZPN_UMAQA), ~((zpn_operator_i == ZPN_UMAQA) | (zpn_operator_i == ZPN_SMAQAsu))};
  assign signed_mult = zpn_instr_i ? zpn_signed_mult : {signed_mode_i[0], signed_mode_i[1]};

  // Decode if we want most of least significant word
  logic mult_LSW;
  assign mult_LSW = zpn_instr_i ? ((zpn_operator_i == ZPN_MADDR32)  |
                                   (zpn_operator_i == ZPN_MSUBR32)) : (md_operator_i  == MD_OP_MULL);

  //////////////////////////////
  // Operand and Sign decoder //
  //////////////////////////////
  logic[2:0] op_a_signs, op_b_signs;
  always_comb begin
    // Default inputs for most modes
    mult1_op_a = op_a_i[`OP_L];
    mult2_op_a = op_a_i[`OP_H];
    mult3_op_a = (mult_state_q == MULH) ? op_a_i[`OP_H] : op_a_i[`OP_L];

    mult1_op_b = crossed ? op_b_i[`OP_H] : op_b_i[`OP_L];
    mult2_op_b = crossed ? op_b_i[`OP_H] : op_b_i[`OP_L];
    mult3_op_b = op_b_i[`OP_H];

    unique case(mult_mode)
      M8x8  : begin // TODO
        op_a_signs = {op_a_i[31], op_a_i[15], op_a_i[15]} & {3{signed_mult[1]}};
        op_b_signs = {op_b_i[31], op_b_i[15], op_a_i[15]} & {3{signed_mult[0]}};
      end

      M16x16: begin
        op_a_signs = {op_a_i[31], 1'b0, op_a_i[15]} & {3{signed_mult[1]}};
        op_b_signs = {op_b_i[31], 1'b0, (crossed ? op_b_i[31] : op_b_i[15])} & {3{signed_mult[0]}};

        mult3_op_a = op_a_i[`OP_H];
      end

      M32x16: begin
        op_a_signs = {1'b0, op_a_i[31], 1'b0} & {3{signed_mult[1]}};
        op_b_signs = {1'b0, (crossed ? {2{op_b_i[31]}} : {2{op_b_i[15]}})} & {3{signed_mult[0]}};
      end

      M32x32: begin
        op_a_signs = {((mult_state_q == MULH) ? op_a_i[31] : 1'b0), op_a_i[31], 1'b0} & {3{signed_mult[1]}};
        op_b_signs = {op_b_i[31], 1'b0, 1'b0} & {3{signed_mult[0]}};
      end
    endcase
  end

  typedef enum logic[1:0] {
    MULL, MULH, ACCUM
  } mult_fsm_e;
  mult_fsm_e mult_state_q, mult_state_d;

  logic               mult_valid, mult_hold;
  logic signed [33:0] mult1_res, mult2_res, mult3_res, accum, mult_res_d;
  logic signed [34:0] mult_res_imd, mult_res;
  logic        [15:0] mult1_op_a, mult1_op_b, mult2_op_a, 
                      mult2_op_b, mult3_op_a, mult3_op_b;
  logic        [33:0] summand_LL, summand_HL, summand_LH_HH;

  logic        [31:0] mult_16x16_0, mult_16x16_1;
  logic        [31:0] alu_operand_a_mult, alu_operand_b_mult;

  logic        [31:0] mult_sum_32x16MSW, mult_sum_32x32W;

  // Actual multipliers
  assign mult1_res = $signed({op_a_signs[0], mult1_op_a}) * $signed({op_b_signs[0], mult1_op_b}); // LL or LH
  assign mult2_res = $signed({op_a_signs[1], mult2_op_a}) * $signed({op_b_signs[1], mult2_op_b}); // HL or HH
  assign mult3_res = $signed({op_a_signs[2], mult3_op_a}) * $signed({op_b_signs[2], mult3_op_b}); // LH or HH

  // Result generation
  assign mult_res_imd = $signed(summand_LL)   + $signed(summand_HL);
  assign mult_res     = $signed(mult_res_imd) + $signed(summand_LH_HH);
  assign mult_res_d   = mult_LSW ? {2'b00, mult_res[`OP_L], $unsigned(mult1_res[`OP_L])} : mult_res[33:0];

  assign mult_sum_32x32W = mult_res_d[31:0];
  
  assign mult_sum_32x16MSW = mult_res_imd[31:0];
  
  assign mult_16x16_0 = mult1_res[31:0];
  assign mult_16x16_1 = mult3_res[31:0];

  // 8x8 MAC


  // 16x16 MAC


  
  /////////
  // FSM //
  /////////
  always_comb begin
    summand_LL    = {18'h0, $unsigned(mult1_res[`OP_H])};
    summand_HL    = $unsigned(mult2_res);
    summand_LH_HH = $unsigned(mult3_res);
    
    mult_state_d = MULL;

    mult_hold = 1'b0;
    mult_valid = 1'b0;

    alu_operand_a_mult = rd_val_i;
    alu_operand_b_mult = imd_val_q_i[0][31:0];

    unique case (mult_state_q)
      MULL: begin
        if (cycle_count[0]) begin
          mult_valid = 1'b0;
          mult_state_d = MULH;
        end 
        else if (cycle_count[1]) begin
          mult_valid = 1'b0;
          mult_state_d = ACCUM;
        end
        else begin
          mult_hold = ~multdiv_ready_id_i;
          mult_valid = 1'b1;
        end
      end

      MULH: begin
        summand_LL    = '0;
        summand_HL    = {{16{|signed_mult & imd_val_q_i[0][33]}}, imd_val_q_i[0][33:16]};;
        summand_LH_HH = $unsigned(mult3_res);

        if (cycle_count[1]) begin
          mult_valid = 1'b0;
          mult_state_d = ACCUM;
        end
        else begin
          mult_valid = 1'b1;
          mult_state_d = MULL;
          mult_hold = ~multdiv_ready_id_i;
        end
      end

      ACCUM: begin
        mult_state_d = MULL;
        mult_valid = 1'b1;

        mult_hold = ~multdiv_ready_id_i;
      end

      default: begin
        mult_state_d = MULL;
      end
    endcase
  end


  //////////////////////
  // Final result Mux //
  //////////////////////
  always_comb begin
    unique case(alu_operator_i)
      ZPN_INSTR: begin
        unique case(zpn_operator_i)
          // 8x8 ops ////
          /*ZPN_KHM8,     ZPN_KHMX8: mult_result = {saturated[3] ? 8'h7f : mult_sum_8x8_3, 
                                                  saturated[2] ? 8'h7f : mult_sum_8x8_2,
                                                  saturated[1] ? 8'h7f : mult_sum_8x8_1,
                                                  saturated[0] ? 8'h7f : mult_sum_8x8_0};*/

          //ZPN_SMAQA,    ZPN_SMAQAsu,
          //ZPN_UMAQA: mult_result = accum_Rd; 

          // 16x16 ops ////
          /*ZPN_KHM16,    ZPN_KHMX16: mult_result = {saturated[3] ? 16'h7fff : mult_sum_16x16_1[30:15],
                                                     saturated[1] ? 16'h7fff : mult_sum_16x16_0[30:15]};*/

          ZPN_SMBB16,   ZPN_SMBT16: mult_result = mult_16x16_0;

          ZPN_SMTT16: mult_result = mult_16x16_1;
  
          /*ZPN_KMABB,    ZPN_KMABT,    ZPN_KMATT,
          ZPN_KMADA,    ZPN_KMAXDA,
          ZPN_KMADS,    ZPN_KMADRS,
          ZPN_KMAXDS,   ZPN_KMSDA,
          ZPN_KMSXDA: mult_result = accum_Rd;*/

          /*ZPN_KMDA,     ZPN_KMXDA,
          ZPN_SMDS,     ZPN_SMDRS,
          ZPN_SMXDS: mult_result = sum_16x16;*/

          ZPN_KHMBB,    ZPN_KHMBT: mult_result = {{16{mult_16x16_0[31]}}, mult_16x16_0[30:15]};
          
          ZPN_KHMTT: mult_result = {{16{mult_16x16_1[31]}}, mult_16x16_1[30:15]};

          // 32x16 ops ////
          ZPN_SMMWB,  ZPN_SMMWT: mult_result = mult_sum_32x16MSW;

          // 32x32H ops ////
          ZPN_SMMUL,    ZPN_SMMULu: mult_result = mult_sum_32x32W[31:0];

          ZPN_KWMMUL,   ZPN_KWMMULu: mult_result = {mult_sum_32x32W[30:0], imd_val_q_i[0][15]};

          // All other mult ops are finished in ALU
          default: mult_result = '0;
        endcase
      end

      default: begin
        mult_result = mult_sum_32x32W[31:0];
      end
    endcase
  end

  logic mult_en_internal;
  assign mult_en_internal = mult_en_i & ~mult_hold;

  always_ff @(posedge clk_i or negedge rst_ni) begin
    if (!rst_ni) begin
      mult_state_q <= MULL;
    end else begin
      if (mult_en_internal) begin
        mult_state_q <= mult_state_d;
      end
    end
  end


  //////////    _____   _         _     _              //////////
  //////////   |  __ \ (_)       (_)   | |             //////////
  //////////   | |  | | _ __   __ _  __| | ___ _ __    //////////
  //////////   | |  | || |\ \ / /| |/ _` |/ _ \ '__|   //////////
  //////////   | |__| || | \ V / | | (_| |  __/ |      //////////
  //////////   |_____/ |_|  \_/  |_|\__,_|\___|_|      //////////
  //////////                                           //////////

  logic        div_sign_a, div_sign_b;
  logic        is_greater_equal;
  logic        div_change_sign, rem_change_sign;
  logic [31:0] alu_operand_a_div, alu_operand_b_div;
  logic [31:0] one_shift;
  logic [31:0] op_denominator_q;
  logic [31:0] op_numerator_q,   op_numerator_d;
  logic [31:0] op_quotient_q,    op_quotient_d;
  logic [31:0] next_remainder;
  logic [32:0] next_quotient;
  logic [31:0] res_adder_h;
  logic        div_valid;
  logic [ 4:0] div_counter_q, div_counter_d;
  logic        div_hold;
  logic        div_by_zero_q, div_by_zero_d;
  logic        div_en_internal;

  typedef enum logic [2:0] {
    MD_IDLE, MD_ABS_A, MD_ABS_B, MD_COMP, MD_LAST, MD_CHANGE_SIGN, MD_FINISH
  } md_fsm_e;
  md_fsm_e md_state_q, md_state_d;

  assign div_en_internal  = div_en_i & ~div_hold;

  // Clock in various registers
  always_ff @(posedge clk_i or negedge rst_ni) begin
    if (!rst_ni) begin
      div_counter_q    <= '0;
      md_state_q       <= MD_IDLE;
      op_numerator_q   <= '0;
      op_quotient_q    <= '0;
      div_by_zero_q    <= '0;
    end else if (div_en_internal) begin
      div_counter_q    <= div_counter_d;
      op_numerator_q   <= op_numerator_d;
      op_quotient_q    <= op_quotient_d;
      md_state_q       <= md_state_d;
      div_by_zero_q    <= div_by_zero_d;
    end
  end

  assign imd_val_we_div[0] = multdiv_en_i;
  assign imd_val_we_div[1] = div_en_internal;
  assign op_denominator_q = imd_val_q_i[1][31:0];

  assign res_adder_h = alu_adder_i;

  assign next_remainder = is_greater_equal ? res_adder_h[31:0] : imd_val_q_i[0][31:0];
  assign next_quotient  = is_greater_equal ? {1'b0, op_quotient_q} | {1'b0, one_shift} :
                                             {1'b0, op_quotient_q};

  assign one_shift      = {31'b0, 1'b1} << div_counter_q;

  // The adder in the ALU computes alu_operand_a_div + alu_operand_b_div which means
  // Remainder - Divisor. If Remainder - Divisor >= 0, is_greater_equal is equal to 1,
  // the next Remainder is Remainder - Divisor contained in res_adder_h and the
  always_comb begin
    if ((imd_val_q_i[0][31] ^ op_denominator_q[31]) == 1'b0) begin
      is_greater_equal = (res_adder_h[31] == 1'b0);
    end else begin
      is_greater_equal = imd_val_q_i[0][31];
    end
  end

  assign div_sign_a      = op_a_i[31] & signed_mode_i[0];
  assign div_sign_b      = op_b_i[31] & signed_mode_i[1];
  assign div_change_sign = (div_sign_a ^ div_sign_b) & ~div_by_zero_q;
  assign rem_change_sign = div_sign_a;

  // Divider state machine
  always_comb begin
    div_counter_d       = div_counter_q - 5'h1;
    op_remainder_d      = imd_val_q_i[0];
    op_quotient_d       = op_quotient_q;
    md_state_d          = md_state_q;
    op_numerator_d      = op_numerator_q;
    op_denominator_d    = op_denominator_q;
    alu_operand_a_div   = 32'h0;
    alu_operand_b_div   = op_b_i;
    div_valid           = 1'b0;
    div_hold            = 1'b0;
    div_by_zero_d       = div_by_zero_q;

    unique case (md_state_q)
      MD_IDLE: begin
        if (md_operator_i == MD_OP_DIV) begin
          // Check if the Denominator is 0
          // quotient for division by 0 is specified to be -1
          // Note with data-independent time option, the full divide operation will proceed as
          // normal and will naturally return -1
          op_remainder_d = '1;
          // SEC_CM: CORE.DATA_REG_SW.SCA
          md_state_d     = (!data_ind_timing_i && equal_to_zero_i) ? MD_FINISH : MD_ABS_A;
          // Record that this is a div by zero to stop the sign change at the end of the
          // division (in data_ind_timing mode).
          div_by_zero_d  = equal_to_zero_i;
        end else begin
          // Check if the Denominator is 0
          // remainder for division by 0 is specified to be the numerator (operand a)
          // Note with data-independent time option, the full divide operation will proceed as
          // normal and will naturally return operand a
          op_remainder_d = {2'b0, op_a_i};
          // SEC_CM: CORE.DATA_REG_SW.SCA
          md_state_d     = (!data_ind_timing_i && equal_to_zero_i) ? MD_FINISH : MD_ABS_A;
        end
        // 0 - B = 0 iff B == 0
        alu_operand_a_div  = 32'h0;
        alu_operand_b_div  = op_b_i;
        div_counter_d    = 5'd31;
      end

      MD_ABS_A: begin
        // quotient
        op_quotient_d   = '0;
        // A abs value
        op_numerator_d  = div_sign_a ? alu_adder_i : op_a_i;
        md_state_d      = MD_ABS_B;
        div_counter_d   = 5'd31;
        // ABS(A) = 0 - A
        alu_operand_a_div = 32'h0;
        alu_operand_b_div = op_a_i;
      end

      MD_ABS_B: begin
        // remainder
        op_remainder_d   = { 33'h0, op_numerator_q[31]};
        // B abs value
        op_denominator_d = div_sign_b ? alu_adder_i : op_b_i;
        md_state_d       = MD_COMP;
        div_counter_d    = 5'd31;
        // ABS(B) = 0 - B
        alu_operand_a_div  = 32'h0;
        alu_operand_b_div  = op_b_i;
      end

      MD_COMP: begin
        op_remainder_d  = {1'b0, next_remainder[31:0], op_numerator_q[div_counter_d]};
        op_quotient_d   = next_quotient[31:0];
        md_state_d      = (div_counter_q == 5'd1) ? MD_LAST : MD_COMP;
        // Division
        alu_operand_a_div = imd_val_q_i[0][31:0]; // it contains the remainder
        alu_operand_b_div = op_denominator_q[31:0];  // -denominator two's compliment
      end

      MD_LAST: begin
        if (md_operator_i == MD_OP_DIV) begin
          // this time we save the quotient in op_remainder_d (i.e. imd_val_q_i[0]) since
          // we do not need anymore the remainder
          op_remainder_d = {1'b0, next_quotient};
        end else begin
          // this time we do not save the quotient anymore since we need only the remainder
          op_remainder_d = {2'b0, next_remainder[31:0]};
        end
        // Division
        alu_operand_a_div  = imd_val_q_i[0][31:0]; // it contains the remainder
        alu_operand_b_div  = op_denominator_q[31:0];  // -denominator two's compliment

        md_state_d = MD_CHANGE_SIGN;
      end

      MD_CHANGE_SIGN: begin
        md_state_d  = MD_FINISH;
        if (md_operator_i == MD_OP_DIV) begin
          op_remainder_d = (div_change_sign) ? {2'h0, alu_adder_i} : imd_val_q_i[0];
        end else begin
          op_remainder_d = (rem_change_sign) ? {2'h0, alu_adder_i} : imd_val_q_i[0];
        end
        // ABS(Quotient) = 0 - Quotient (or Remainder)
        alu_operand_a_div  = 32'h0;
        alu_operand_b_div  = imd_val_q_i[0][31:0];
      end

      MD_FINISH: begin
        // Hold result until ID stage is ready to accept it
        // Note no state transition will occur if div_hold is set
        md_state_d = MD_IDLE;
        div_hold   = ~multdiv_ready_id_i;
        div_valid   = 1'b1;
      end

      default: begin
        md_state_d = MD_IDLE;
      end
    endcase
  end

  assign valid_o = div_sel_i ? div_valid : mult_valid;
  assign alu_operand_a_o = div_sel_i ? alu_operand_a_div : alu_operand_a_mult;
  assign alu_operand_b_o = div_sel_i ? alu_operand_b_div : alu_operand_b_mult;

  assign multdiv_result_o = div_sel_i ? imd_val_q_i[0][31:0] : mult_result;

endmodule
