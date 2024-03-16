// Copyright lowRISC contributors.
// Copyright 2018 ETH Zurich and University of Bologna, see also CREDITS.md.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

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

  // Intermediate value register
  logic[1:0] imd_val_we_div, imd_val_we_mult;
  assign imd_val_we_o = div_sel_i ? imd_val_we_div : imd_val_we_mult;
  assign imd_val_d_o[0] = div_sel_i ? op_remainder_d : imd_val_d_mult[0];
  assign imd_val_d_o[1] = div_sel_i ? {2'b0, op_denominator_d} : imd_val_d_mult[1];

  // Assign unused variable
  logic unused_mult_en_i;
  assign unused_mult_en_i = mult_en_i;

  ////////////////////
  // Decoder helper //
  ////////////////////
  ibex_pkg_pext::mult_pext_mode_e mult_mode;
  logic[1:0]                      cycle_count;
  logic[1:0]                      accum_sub;
  logic[1:0]                      add_mode;
  logic                           crossed, accum_en;

  ibex_mult_pext_helper mult_pext_helper_i (
    .zpn_operator_i   (zpn_operator_i),
    .alu_operator_i   (alu_operator_i),
    .mult_mode_o      (mult_mode),
    .cycle_count_o    (cycle_count),
    .accum_sub_o      (accum_sub),
    .add_mode_o       (add_mode),
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

  logic         mult_valid;
  logic [31:0]  mult_result;
  logic [31:0]  alu_operand_a_mult, alu_operand_b_mult;
  logic [33:0]  imd_val_d_mult[2];
  logic [1:0]   quadrant;
 
  assign imd_val_d_mult[0] = (mult_state == UPPER) ? {2'b0, mult_sum_32x32W} : {2'b0, mult_sum_32x16[31:0]};
  assign imd_val_d_mult[1] = {2'b0, {16{mult_sum_32x16[47]}}, mult_sum_32x16[47:32]};

  // Assign quadrant signal
  always_comb begin
    unique case (mult_mode)
      M8x8  : quadrant = 2'b00;
      M16x16: quadrant = crossed ? 2'b11 : 2'b00;
      M32x16: quadrant = crossed ? 2'b01 : 2'b10;
      M32x32: quadrant = (mult_state == UPPER) ? 2'b01 : 2'b10;
    endcase
  end

  // All mults are signed except for UMAQA and SMAQA.su
  logic[1:0] zpn_signed_mult, signed_mult;
  assign zpn_signed_mult = {~(zpn_operator_i == ZPN_UMAQA), ~((zpn_operator_i == ZPN_UMAQA) | (zpn_operator_i == ZPN_SMAQAsu))};
  assign signed_mult = zpn_instr_i ? zpn_signed_mult : {signed_mode_i[0], signed_mode_i[1]};
  
  //logic sign_extend;    // TODO
  //assign sign_extend = (~((mult_state == LOWER) & cycle_count[0])) | (md_operator_i == MD_OP_MULH);

  // Decode Rounding ops    // TODO
  /*logic[31:0] rounding_mask;
  always_comb begin
    unique case(zpn_operator_i)
      // 32x32
      ZPN_SMMULu,   ZPN_KMMACu,
      ZPN_KMMSBu,   ZPN_KWMMULu: rounding_mask = (mult_state == LOWER) ? 32'h0000_8000 : 32'h0;

      // 32x16
      ZPN_SMMWBu,   ZPN_SMMWTu,
      ZPN_KMMAWBu,  ZPN_KMMAWTu,
      ZPN_KMMWB2u,  ZPN_KMMWT2u,
      ZPN_KMMAWB2u, ZPN_KMMAWT2u: rounding_mask = (mult_state == LOWER) ? 32'h0000_0080 : 32'h0;

      default: rounding_mask = '0;
    endcase
  end

  logic[31:0] unused_rounding;    // TODO
  assign unused_rounding = rounding_mask;*/

  logic[7:0] mult_ker0_op_a0, mult_ker0_op_a1, mult_ker1_op_a0, mult_ker1_op_a1,
             mult_ker0_op_b0, mult_ker0_op_b1, mult_ker1_op_b0, mult_ker1_op_b1;

  // Prepare operands
  assign mult_ker0_op_a0 = op_a_i[7:0];
  assign mult_ker0_op_a1 = op_a_i[15:8];
  assign mult_ker1_op_a0 = op_a_i[23:16];
  assign mult_ker1_op_a1 = op_a_i[31:24];

  assign mult_ker0_op_b0 = quadrant[0] ? op_b_i[23:16] : op_b_i[7:0];
  assign mult_ker0_op_b1 = quadrant[0] ? op_b_i[31:24] : op_b_i[15:8];
  assign mult_ker1_op_b0 = quadrant[1] ? op_b_i[7:0]   : op_b_i[23:16];
  assign mult_ker1_op_b1 = quadrant[1] ? op_b_i[15:8]  : op_b_i[31:24];


  //////////////////
  // Sign decoder //
  //////////////////
  logic[3:0] op_a_signs, op_b_signs;
  always_comb begin
    unique case(mult_mode)
      M8x8  : begin
        op_a_signs = {mult_ker1_op_a1[7], mult_ker1_op_a0[7], mult_ker0_op_a1[7], mult_ker0_op_a0[7]} & {4{signed_mult[1]}};
        op_b_signs = {mult_ker1_op_b1[7], mult_ker1_op_b0[7], mult_ker0_op_b1[7], mult_ker0_op_b0[7]} & {4{signed_mult[0]}};
      end

      M16x16: begin
        op_a_signs = {mult_ker1_op_a1[7], 1'b0, mult_ker0_op_a1[7], 1'b0} & {4{signed_mult[1]}};
        op_b_signs = {mult_ker1_op_b1[7], 1'b0, mult_ker0_op_b1[7], 1'b0} & {4{signed_mult[0]}};
      end

      M32x16: begin
        op_a_signs = {mult_ker1_op_a1[7], 3'b000} & {4{signed_mult[1]}};
        op_b_signs = {mult_ker0_op_b1[7], 1'b0, mult_ker0_op_b1[7], 1'b0} & {4{signed_mult[0]}};
      end

      M32x32: begin
        op_a_signs = {mult_ker1_op_a1[7], 3'b000} & {4{signed_mult[1]}};
        op_b_signs = (mult_state == UPPER) ? {mult_ker0_op_b1[7], 1'b0, mult_ker0_op_b1[7], 1'b0} & {4{signed_mult[0]}} : 4'b0000;
      end
    endcase
  end


  ////////////////////////
  // Actual multipliers //
  ////////////////////////
  // Using 8 8x8 multipliers in a Baugh-Wooley scheme.
  // All 8x8, 16x16 and 32x16 mults take one clock cycle,
  // while 32x32 needs two or three cycles
  logic[17:0] mult_ker0_sum00, mult_ker0_sum01, mult_ker0_sum10, mult_ker0_sum11,
              mult_ker1_sum00, mult_ker1_sum01, mult_ker1_sum10, mult_ker1_sum11;

  assign mult_ker0_sum00 = $signed({op_a_signs[0], mult_ker0_op_a0}) * $signed({op_b_signs[0], mult_ker0_op_b0});
  assign mult_ker0_sum01 = $signed({op_a_signs[0], mult_ker0_op_a0}) * $signed({op_b_signs[1], mult_ker0_op_b1});
  assign mult_ker0_sum10 = $signed({op_a_signs[1], mult_ker0_op_a1}) * $signed({op_b_signs[0], mult_ker0_op_b0});
  assign mult_ker0_sum11 = $signed({op_a_signs[1], mult_ker0_op_a1}) * $signed({op_b_signs[1], mult_ker0_op_b1});

  assign mult_ker1_sum00 = $signed({op_a_signs[2], mult_ker1_op_a0}) * $signed({op_b_signs[2], mult_ker1_op_b0});
  assign mult_ker1_sum01 = $signed({op_a_signs[2], mult_ker1_op_a0}) * $signed({op_b_signs[3], mult_ker1_op_b1});
  assign mult_ker1_sum10 = $signed({op_a_signs[3], mult_ker1_op_a1}) * $signed({op_b_signs[2], mult_ker1_op_b0});
  assign mult_ker1_sum11 = $signed({op_a_signs[3], mult_ker1_op_a1}) * $signed({op_b_signs[3], mult_ker1_op_b1});

  logic[15:0] unused_mult_bits;
  assign unused_mult_bits = {mult_ker0_sum00[17:16], mult_ker0_sum01[17:16], mult_ker0_sum10[17:16], mult_ker0_sum11[17:16],
                             mult_ker1_sum00[17:16], mult_ker1_sum01[17:16], mult_ker1_sum10[17:16], mult_ker1_sum11[17:16]};

  
  /////////////////////////
  // 16x16 Kernel adders //     // Note: Also does 8x8 summation ops
  /////////////////////////

  // Prepare operands
  logic wide_ops;
  logic[15:0] sum_ker0_op_a0, sum_ker0_op_a1, sum_ker1_op_a0, sum_ker1_op_a1;
  logic[15:0] sum_ker0_op_b0, sum_ker0_op_b1, sum_ker1_op_b0, sum_ker1_op_b1;
  logic[23:0] sum_ker0_op_a, sum_ker0_op_b, sum_ker1_op_a, sum_ker1_op_b;

  logic[16:0] sum_ker0_0, sum_ker0_1, sum_ker1_0, sum_ker1_1;
  logic[24:0] sum_ker0, sum_ker1;

  assign wide_ops = (mult_mode != M8x8);

  assign sum_ker0_op_a0 = wide_ops ? mult_ker0_sum01[15:0] : mult_ker0_sum11[15:0];
  assign sum_ker0_op_a1 = wide_ops ? mult_ker0_sum11[15:0] : mult_ker1_sum11[15:0];
  assign sum_ker1_op_a0 = mult_ker1_sum01[15:0];
  assign sum_ker1_op_a1 = mult_ker1_sum11[15:0];
  assign sum_ker0_op_b0 = wide_ops ? {{8{mult_ker0_sum00[16]}}, mult_ker0_sum00[15:8]} : mult_ker0_sum00[15:0];
  assign sum_ker0_op_b1 = wide_ops ? {{8{mult_ker0_sum10[16]}}, mult_ker0_sum10[15:8]} : mult_ker1_sum00[15:0];
  assign sum_ker1_op_b0 = {{8{mult_ker1_sum00[16]}}, mult_ker1_sum00[15:8]};
  assign sum_ker1_op_b1 = {{8{mult_ker1_sum10[16]}}, mult_ker1_sum10[15:8]};

  assign sum_ker0_op_a = wide_ops ? {sum_ker0_1[15:0], mult_ker0_sum10[7:0]} : {{7{sum_ker0_1[16]}}, sum_ker0_1};
  assign sum_ker0_op_b = wide_ops ? {{8{sum_ker0_0[16]}}, sum_ker0_0[15:0]}  : {{7{sum_ker0_0[16]}}, sum_ker0_0};   // TODO maybe
  assign sum_ker1_op_a = {sum_ker1_1[15:0], mult_ker1_sum10[7:0]};
  assign sum_ker1_op_b = {{8{sum_ker1_0[16]}}, sum_ker1_0[15:0]};

  assign sum_ker0_0 = $signed(sum_ker0_op_a0) + $signed(sum_ker0_op_b0);  
  assign sum_ker0_1 = $signed(sum_ker0_op_a1) + $signed(sum_ker0_op_b1);
  assign sum_ker1_0 = $signed(sum_ker1_op_a0) + $signed(sum_ker1_op_b0);  
  assign sum_ker1_1 = $signed(sum_ker1_op_a1) + $signed(sum_ker1_op_b1);

  assign sum_ker0 = $signed(sum_ker0_op_a) + $signed(sum_ker0_op_b);
  assign sum_ker1 = $signed(sum_ker1_op_a) + $signed(sum_ker1_op_b);

  logic[1:0] unused_sum_ker1;
  assign unused_sum_ker1 = {sum_ker1[24], sum_ker1_1[16]};


  /////////////////////////
  // 32x16 Kernel adders //     // Note: also does sum1 + sum2 for accum ops
  /////////////////////////
  logic[31:0] sum_op_a_32x16, sum_op_b_32x16;
  logic[32:0] sum_total_32x16;
  logic       unused_sum_total_32x16;
  logic       narrow_ops;
  logic       reversed_mult;

  assign narrow_ops    = (mult_mode == M8x8)           | (mult_mode == M16x16);
  assign reversed_mult = (zpn_operator_i == ZPN_SMDRS) | (zpn_operator_i == ZPN_KMADRS);

  always_comb begin
    if (add_mode[0]) begin
      sum_op_a_32x16 = {sum_ker0[23:0], mult_ker0_sum00[7:0]};
      sum_op_b_32x16 = {sum_ker1[23:0], mult_ker1_sum00[7:0]};

      if (reversed_mult) begin
        sum_op_a_32x16 = ~{sum_ker0[23:0], mult_ker0_sum00[7:0]};
      end
      else if (accum_sub[0]) begin
        sum_op_b_32x16 = ~{sum_ker1[23:0], mult_ker1_sum00[7:0]};
      end
    end 
    else begin    // TODO
      if (narrow_ops) begin
        sum_op_a_32x16 = {8'h00, sum_ker0[23:0]};
        sum_op_b_32x16 = 32'h0;
      end
      else begin
        sum_op_a_32x16 = {sum_ker1[23:0], mult_ker1_sum00[7:0]};
        sum_op_b_32x16 = {{16{sum_ker0[24]}}, sum_ker0[23:8]};
      end
    end
  end

  assign sum_total_32x16 = $signed(sum_op_a_32x16) + $signed(sum_op_b_32x16) + {31'h0, accum_sub[0]};// + rounding_mask; // TODO
  assign unused_sum_total_32x16 = sum_total_32x16[32];


  /////////////////////////
  // 32x32 Kernel adders //     // Note: also does rd + sum for accum ops
  /////////////////////////
  logic[47:0] sum_op_a_32x32, sum_op_b_32x32;
  logic[48:0] sum_total_32x32;
  logic[16:0] unused_sum_total_32x32;
  logic       mult_LSW;

  assign mult_LSW = (md_operator_i == MD_OP_MULL)   | 
                    (zpn_operator_i == ZPN_MADDR32) |
                    (zpn_operator_i == ZPN_MSUBR32);

  always_comb begin
    if (add_mode[1]) begin
      sum_op_a_32x32 = {rd_val_i, 16'h0};
      sum_op_b_32x32 = {sum_total_32x16[31:0], 16'h0};
    end
    else begin
      if (mult_LSW) begin
        sum_op_a_32x32 = {mult_sum_32x16[15:0], 32'h0};
        sum_op_b_32x32 = {imd_val_q_i[0][31:0], 16'h0};
      end
      else begin
        sum_op_a_32x32 = mult_sum_32x16;
        sum_op_b_32x32 = {imd_val_q_i[1][31:0], imd_val_q_i[0][31:16]};
      end
    end
  end

  assign sum_total_32x32 = $signed(sum_op_a_32x32) + $signed(sum_op_b_32x32) + {31'h0, accum_sub[1], 16'h0};
  assign unused_sum_total_32x32 = {sum_total_32x32[48], sum_total_32x32[15:0]};


  ////////////////
  // Saturation //    // TODO: Fix this
  ////////////////
  // Decode saturation state
  logic[3:0] sat_zeros, sat_ones, saturated;
  always_comb begin   
    sat_zeros = { &(~mult_ker1_op_a1[6:0] & ~mult_ker1_op_b1[6:0]), 
                  &(~mult_ker1_op_a0[6:0] & ~mult_ker1_op_b0[6:0]), 
                  &(~mult_ker0_op_a1[6:0] & ~mult_ker0_op_b1[6:0]), 
                  &(~mult_ker0_op_a0[6:0] & ~mult_ker0_op_b0[6:0])};

    sat_ones  = {mult_ker1_op_a1[7] & mult_ker1_op_b0[7], mult_ker1_op_a0[7] & mult_ker1_op_b0[7], 
                 mult_ker0_op_a1[7] & mult_ker0_op_b0[7], mult_ker0_op_a0[7] & mult_ker0_op_b0[7]};

    unique case(mult_mode)
      M32x32: saturated = 4'b0000; // TODO
      M8x8  : saturated = {sat_ones[3] & sat_zeros[3], sat_ones[2] & sat_zeros[2], 
                           sat_ones[1] & sat_zeros[1], sat_ones[0] & sat_zeros[0]};
      M16x16: saturated = {sat_ones[3] & sat_zeros[3], 1'b0, sat_ones[1] & sat_zeros[1], 1'b0};
      M32x16: saturated = 4'b0000;
    endcase

    set_ov_o = (|saturated) & mult_sel_i;
  end
  

  /////////////////
  // 8x8 results //
  /////////////////
  logic[7:0] mult_sum_8x8_0, mult_sum_8x8_1, mult_sum_8x8_2, mult_sum_8x8_3;
  assign mult_sum_8x8_0 = crossed ? mult_ker0_sum01[14:7] : mult_ker0_sum00[14:7];
  assign mult_sum_8x8_1 = crossed ? mult_ker0_sum10[14:7] : mult_ker0_sum11[14:7];
  assign mult_sum_8x8_2 = crossed ? mult_ker1_sum01[14:7] : mult_ker1_sum00[14:7];
  assign mult_sum_8x8_3 = crossed ? mult_ker1_sum10[14:7] : mult_ker1_sum11[14:7];


  ///////////////////
  // 16x16 results //
  ///////////////////
  logic[31:0] mult_sum_16x16_0, mult_sum_16x16_1;
  assign mult_sum_16x16_0 = {sum_ker0[23:0], mult_ker0_sum00[7:0]};
  assign mult_sum_16x16_1 = {sum_ker1[23:0], mult_ker1_sum00[7:0]};


  ///////////////////
  // 32x16 results //
  ///////////////////
  logic[47:0] mult_sum_32x16;
  logic[31:0] mult_sum_32x16_MSW;

  assign mult_sum_32x16 = {sum_total_32x16[31:0], sum_ker0[7:0], mult_ker0_sum00[7:0]};
  assign mult_sum_32x16_MSW = mult_sum_32x16[47:16];


  ///////////////////
  // 32x32 results //
  ///////////////////
  logic[31:0] mult_sum_32x32W;
  assign mult_sum_32x32W = sum_total_32x32[47:16];


  //////////////////////
  // Final result Mux //
  //////////////////////
  always_comb begin
    unique case(alu_operator_i)
      ZPN_INSTR: begin
        unique case(zpn_operator_i)
          // 8x8 ops ////
          ZPN_KHM8, ZPN_KHMX8: mult_result = {saturated[3] ? 8'h7f : mult_sum_8x8_3, 
                                              saturated[2] ? 8'h7f : mult_sum_8x8_2,
                                              saturated[1] ? 8'h7f : mult_sum_8x8_1,
                                              saturated[0] ? 8'h7f : mult_sum_8x8_0};

          ZPN_SMAQA, ZPN_SMAQAsu,
          ZPN_UMAQA: mult_result = sum_total_32x32[47:16]; 

          // 16x16 ops ////
          ZPN_KHM16, ZPN_KHMX16: mult_result = {(saturated[3] & saturated[2]) ? 16'h7fff : mult_sum_16x16_1[30:15],
                                                (saturated[1] & saturated[0]) ? 16'h7fff : mult_sum_16x16_0[30:15]};

          ZPN_SMBB16,   ZPN_SMBT16: mult_result = mult_sum_16x16_0;

          ZPN_KDMBB,    ZPN_KDMBT: mult_result = {mult_sum_16x16_0[30:0], 1'b1};  // TODO: Add saturation as well

          ZPN_SMTT16: mult_result = mult_sum_16x16_1;
          
          ZPN_KDMTT: mult_result = {mult_sum_16x16_1[30:0], 1'b0};    // TODO: Add saturation as well

          ZPN_KMDA,     ZPN_KMXDA,
          ZPN_SMDS,     ZPN_SMDRS,    
          ZPN_SMXDS,    ZPN_KMABB,
          ZPN_KMABT,    ZPN_KMATT,
          ZPN_KMADA,    ZPN_KMAXDA,
          ZPN_KMADS,    ZPN_KMADRS,
          ZPN_KMAXDS,   ZPN_KMSDA,
          ZPN_KMSXDA: mult_result = sum_total_32x32[47:16];

          ZPN_KHMBB,    ZPN_KHMBT: mult_result = {15'h0, mult_sum_16x16_0[31:15]};    // TODO Add saturation
          
          ZPN_KHMTT: mult_result = {15'h0, mult_sum_16x16_1[31:15]};

          // TODO
          ZPN_KDMABB,   ZPN_KDMABT,  ZPN_KDMATT: mult_result = '0; // !!!!

          // 32x16 ops ////
          ZPN_SMMWB,    ZPN_SMMWBu,
          ZPN_SMMWT,    ZPN_SMMWTu,
          ZPN_KMMWB2,   ZPN_KMMWB2u,
          ZPN_KMMWT2,   ZPN_KMMWT2u: mult_result = mult_sum_32x16_MSW;

          ZPN_KMMAWB,   ZPN_KMMAWBu,
          ZPN_KMMAWT,   ZPN_KMMAWTu,
          ZPN_KMMAWB2,  ZPN_KMMAWB2u,
          ZPN_KMMAWT2,  ZPN_KMMAWT2u: mult_result = sum_total_32x32[47:16];

          // 32x32 ops ////
          ZPN_SMMUL,    ZPN_SMMULu,
          ZPN_KWMMUL,   ZPN_KWMMULu: mult_result = mult_sum_32x32W;

          // All other mult ops are finished in ALU
          default: mult_result = '0;
        endcase
      end

      default: begin
        mult_result = mult_sum_32x32W;
      end
    endcase
  end


  ////////////////////
  // Multiplier FSM //
  ////////////////////
  // FSM state enum
  typedef enum logic[1:0] {
    LOWER, UPPER, ACCUM
  } mult_pext_fsm_e;
  mult_pext_fsm_e    mult_state, mult_state_next;
  logic              fsm_en;

  // FSM state clocking
  always_ff @(posedge clk_i or negedge rst_ni) begin
    if (~rst_ni) begin
      mult_state <= LOWER;
    end
    else begin
      if (mult_sel_i & fsm_en) begin
        mult_state <= mult_state_next;
      end
    end
  end

  // FSM state decoding
  always_comb begin
    mult_valid = 1'b0;
    imd_val_we_mult = 2'b00;
    fsm_en = 1'b0;
    mult_state_next = LOWER;
    alu_operand_a_mult = '0;
    alu_operand_b_mult = '0;

    unique case (mult_state)
      LOWER: begin
        mult_valid = ~cycle_count[0];
        imd_val_we_mult = {2{cycle_count[0]}} & {2{mult_sel_i}};
        fsm_en = 1'b1;

        mult_state_next = cycle_count[0] ? UPPER: LOWER;
      end

      UPPER: begin
        mult_valid = ~cycle_count[1];
        imd_val_we_mult = (accum_en ? 2'b01 : 2'b00) & {2{mult_sel_i}};
        fsm_en = accum_en | multdiv_ready_id_i;

        mult_state_next = cycle_count[1] ? ACCUM : LOWER;
      end

      ACCUM: begin
        mult_valid = 1'b1;
        fsm_en = multdiv_ready_id_i;

        alu_operand_a_mult = rd_val_i;
        alu_operand_b_mult = imd_val_q_i[0][31:0];

        mult_state_next = LOWER;
      end
    endcase
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
  logic [33:0] op_remainder_d;
  logic [31:0] one_shift;
  logic [31:0] op_denominator_q, op_denominator_d;
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
