// Copyright lowRISC contributors.
// Copyright 2018 ETH Zurich and University of Bologna, see also CREDITS.md.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

/**
 * Special multiplier for P-extension
 */

module ibex_mult_pext (
  input  logic                      clk_i,
  input  logic                      rst_ni,

  input  logic                      mult_en_i,

  input  ibex_pkg_pext::zpn_op_e    operator_i,

  input  logic                      width32_i,
  input  logic                      width8_i,
  input  logic                      signed_ops_i,

  input  logic[31:0]                op_a_i,
  input  logic[31:0]                op_b_i,
  input  logic[31:0]                rd_val_i,
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
  // output logic            mult_set_ov_o
  //output logic             valid_o
);

  import ibex_pkg_pext::*;

  //logic[15:0]   mult_op_a0, mult_op_a1;     // Assign these inside the FSM
  //logic[7:0]    mult_op_b0, mult_op_b1;     // Assign these inside the FSM
  //logic[25:0]   mult_res0,  mult_res1;      // Results will be 26 bits wide

  //logic[35:0] unused_bits;
  //assign unused_bits = {mult_res0[25:24], mult_res1[25:24], op_a_i[31:16], op_b_i[31:16]};

  logic crossed;
  always_comb begin
    unique case (operator_i)
      // "Real" crossed ops
      ZPN_KHMX16, ZPN_KHMX8,
      ZPN_SMXDS,  ZPN_KMAXDA,
      ZPN_KMXDA,
      ZPN_KMAXDS, ZPN_KMSXDA,
      // Implicitly crossed ops
      ZPN_KHMBT,    ZPN_KDMBT,      // TODO: BT ops want Ah0*Bh1
      ZPN_KDMABT,   ZPN_KMABT,
      ZPN_KMMAWT,   ZPN_KMMAWTu,    // T ops want A*Bh1
      ZPN_KMMAWT2,  ZPN_KMMAWT2u,
      ZPN_SMMWT,    ZPN_SMMWTu,
      ZPN_KMMWT2,   ZPN_KMMWT2u:  crossed = 1'b1;

      default: crossed = 1'b0;
    endcase
  end

  // Decode MAC-ops
  logic accum_en;
  always_comb begin
    unique case(operator_i)
      // 8x8        32x32         32x16         16x16
      ZPN_SMAQA,    ZPN_KMMAC,    ZPN_KMMAWB,   ZPN_KMABB,
      ZPN_SMAQAsu,  ZPN_KMMACu,   ZPN_KMMAWBu,  ZPN_KMABT,
      ZPN_UMAQA,    ZPN_KMMSB,    ZPN_KMMAWT,   ZPN_KMATT,
                    ZPN_KMMSBu,   ZPN_KMMAWTu,  ZPN_KMADA,
                    ZPN_MADDR32,  ZPN_KMMAWB2,  ZPN_KMAXDA,
                    ZPN_MSUBR32,  ZPN_KMMAWB2u, ZPN_KMADS,
                                  ZPN_KMMAWT2,  ZPN_KMADRS,
                                  ZPN_KMMAWT2u, ZPN_KMAXDS,
                                                ZPN_KMSDA,
                                                ZPN_KMSXDA,
                                                ZPN_KDMABB,
                                                ZPN_KDMABT,
                                                ZPN_KDMATT: accum_en = 1'b1;

      default: accum_en = 1'b0;
    endcase
  end

  // Decode Rounding ops
  logic round_en;
  always_comb begin
    unique case(operator_i)
      ZPN_SMMULu,   ZPN_KMMACu,
      ZPN_KMMSBu,   ZPN_KWMMULu,
      ZPN_SMMWBu,   ZPN_SMMWTu,
      ZPN_KMMAWBu,  ZPN_KMMAWTu,
      ZPN_KMMWB2u,  ZPN_KMMWT2u,
      ZPN_KMMAWB2u, ZPN_KMMAWT2u: round_en = 1'b1;

      default: round_en = 1'b0;
    endcase
  end
  logic unused_fowNow;
  assign unused_fowNow = round_en;

  logic[2:0] unused_test;
  assign unused_test = {width32_i, width8_i, signed_ops_i};

  logic[31:0] unused_more;
  assign unused_more = {op_a_i[31:16], op_b_i[31:16]};


  // Preprocess operands
  logic[31:0] mult_ker0_op_ta, mult_ker0_op_tb;
  assign mult_ker0_op_ta = op_a_i;
  assign mult_ker0_op_tb = op_b_i;

  // Assign final operands
  logic[1:0] quadrant;      // TODO Control from FSM    // For 32x16, A will always be 32-bit, B always 16-bit
  // 00 for normal kernels  
  // 11 for inverted kernels  aka crossed 16x16 and 8x8  and second stage 32x32
  // 10 for full A bottom B aka 32x16
  // 01 for full A top B    aka 32x16

  logic[7:0] mult_ker0_op_a0, mult_ker0_op_a1, mult_ker1_op_a0, mult_ker1_op_a1,
             mult_ker0_op_b0, mult_ker0_op_b1, mult_ker1_op_b0, mult_ker1_op_b1;

  assign mult_ker0_op_a0 = mult_ker0_op_ta[7:0];
  assign mult_ker0_op_a1 = mult_ker0_op_ta[15:8];
  assign mult_ker1_op_a0 = mult_ker0_op_ta[23:16];
  assign mult_ker1_op_a1 = mult_ker0_op_ta[31:24];

  assign mult_ker0_op_b0 = quadrant[0] ? mult_ker0_op_tb[23:16] : mult_ker0_op_tb[7:0];
  assign mult_ker0_op_b1 = quadrant[0] ? mult_ker0_op_tb[31:24] : mult_ker0_op_tb[15:8];
  assign mult_ker1_op_b0 = quadrant[1] ? mult_ker0_op_tb[7:0]   : mult_ker0_op_tb[23:16];
  assign mult_ker1_op_b1 = quadrant[1] ? mult_ker0_op_tb[15:8]  : mult_ker0_op_tb[31:24];

  // Decode operator signs
  logic[3:0] mult_ker0_tmp_signs, mult_ker1_tmp_signs;
  logic[3:0] mult_ker0_signs, mult_ker1_signs;
  assign mult_ker0_tmp_signs = {(mult_ker0_op_a1[7] ^ mult_ker0_op_b1[7]), 
                                (mult_ker0_op_a1[7] ^ mult_ker0_op_b0[7]),
                                (mult_ker0_op_a0[7] ^ mult_ker0_op_b1[7]),
                                (mult_ker0_op_a0[7] ^ mult_ker0_op_b0[7])} & {4{signed_ops_i}};

  assign mult_ker1_tmp_signs = {(mult_ker1_op_a1[7] ^ mult_ker1_op_b1[7]), 
                                (mult_ker1_op_a1[7] ^ mult_ker1_op_b0[7]),
                                (mult_ker1_op_a0[7] ^ mult_ker1_op_b1[7]),
                                (mult_ker1_op_a0[7] ^ mult_ker1_op_b0[7])} & {4{signed_ops_i}};

  always_comb begin
    unique case(mult_mode)
      M8x8  : begin
        mult_ker0_signs = mult_ker0_tmp_signs;
        mult_ker1_signs = mult_ker1_tmp_signs;
      end

      M16x16: begin
        mult_ker0_signs = { {2{mult_ker0_tmp_signs[3]}}, {2{mult_ker0_tmp_signs[1]}} };
        mult_ker1_signs = { {2{mult_ker1_tmp_signs[3]}}, {2{mult_ker1_tmp_signs[1]}} };
      end

      M32x16: begin
        //mult_ker0_signs = { {1{mult_ker0_tmp_signs[3]}}, 1'b0, 1'b0, 1'b0 };
        mult_ker0_signs = { 1'b1, 1'b1, 1'b0, 1'b0 };
        //mult_ker1_signs = { {1{mult_ker1_tmp_signs[3]}}, 1'b0, 1'b1, 1'b1  };
        mult_ker1_signs = { 1'b1, 1'b0, 1'b0, 1'b0  };
        //mult_ker1_signs = crossed ? { {4{mult_ker1_tmp_signs[3]}} } : { {4{mult_ker1_tmp_signs[1]}} };
        //mult_ker0_signs = { {2{mult_ker0_tmp_signs[3]}}, {2{mult_ker0_tmp_signs[1]}} };
        //mult_ker1_signs = { {2{mult_ker1_tmp_signs[3]}}, {2{mult_ker1_tmp_signs[1]}} };
      end

      M32x32: begin
        mult_ker0_signs = { {4{mult_ker0_tmp_signs[3]}} };
        mult_ker1_signs = { {4{mult_ker1_tmp_signs[3]}} };
      end
    endcase
  end

  
  // Actual multipliers
  // Using 8 8x8 multipliers in a Baugh-Wooley scheme...
  // All 8x8, 16x16 and 32x16 mults take one clock cycle,
  // while 32x32 needs two cycles
  logic[17:0] mult_ker0_sum00, mult_ker0_sum01, mult_ker0_sum10, mult_ker0_sum11,
              mult_ker1_sum00, mult_ker1_sum01, mult_ker1_sum10, mult_ker1_sum11;
 
  assign mult_ker0_sum00 = $signed({mult_ker0_signs[0] & mult_ker0_op_a0[7], mult_ker0_op_a0}) * $signed({mult_ker0_signs[0] & mult_ker0_op_b0[7], mult_ker0_op_b0});
  assign mult_ker0_sum01 = $signed({mult_ker0_signs[1] & mult_ker0_op_a0[7], mult_ker0_op_a0}) * $signed({mult_ker0_signs[1] & mult_ker0_op_b1[7], mult_ker0_op_b1});
  assign mult_ker0_sum10 = $signed({mult_ker0_signs[2] & mult_ker0_op_a1[7], mult_ker0_op_a1}) * $signed({mult_ker0_signs[2] & mult_ker0_op_b0[7], mult_ker0_op_b0});
  assign mult_ker0_sum11 = $signed({mult_ker0_signs[3] & mult_ker0_op_a1[7], mult_ker0_op_a1}) * $signed({mult_ker0_signs[3] & mult_ker0_op_b1[7], mult_ker0_op_b1});

  assign mult_ker1_sum00 = $signed({1'b0, mult_ker1_op_a0}) * $signed({1'b0, mult_ker1_op_b0});
  assign mult_ker1_sum01 = $signed({1'b0, mult_ker1_op_a0}) * $signed({1'b0, mult_ker1_op_b1});
  assign mult_ker1_sum10 = $signed({1'b1, mult_ker1_op_a1}) * $signed({1'b0, mult_ker1_op_b0});     // Add one only at upper byte!!
  assign mult_ker1_sum11 = $signed({1'b1, mult_ker1_op_a1}) * $signed({1'b0, mult_ker1_op_b1});

  logic[15:0] unused_mult_bits;    // TODO
  assign unused_mult_bits = {mult_ker0_sum00[17:16], mult_ker0_sum01[17:16], mult_ker0_sum10[17:16], mult_ker0_sum11[17:16],
                             mult_ker1_sum00[17:16], mult_ker1_sum01[17:16], mult_ker1_sum10[17:16], mult_ker1_sum11[17:16]};

  // Assign Raw 8x8 results
  logic[17:0] mult_sum_8x8_0, mult_sum_8x8_1, mult_sum_8x8_2, mult_sum_8x8_3;
  assign mult_sum_8x8_0 = mult_ker0_sum00;
  assign mult_sum_8x8_1 = mult_ker0_sum11;
  assign mult_sum_8x8_2 = mult_ker1_sum00;
  assign mult_sum_8x8_3 = mult_ker1_sum11;

  // Generate 16x16 results
  logic[31:0] mult_ker0_sum, mult_ker1_sum;
  logic[24:0] mult_sum_16x16_partial00, mult_sum_16x16_partial01, mult_sum_16x16_partial10, mult_sum_16x16_partial11;
  
  // First Halfword
  assign mult_sum_16x16_partial00 = {$signed(mult_ker0_sum01[16:0]) + $signed({ {8{1'b0}}, mult_ker0_sum00[15:8]}), mult_ker0_sum00[7:0]};
  assign mult_sum_16x16_partial01 = {$signed(mult_ker0_sum11[16:0]) + $signed({ {8{1'b0}}, mult_ker0_sum10[15:8]}), mult_ker0_sum10[7:0]};
  assign mult_ker0_sum = {mult_sum_16x16_partial01[23:0] + { {8{mult_sum_16x16_partial00[23]}}, mult_sum_16x16_partial00[23:8]}, mult_sum_16x16_partial00[7:0]};

  // Second Halfword
  assign mult_sum_16x16_partial10 = {$signed(mult_ker1_sum01[16:0]) + $signed({ {8{mult_ker1_sum00[15]}}, mult_ker1_sum00[15:8]}), mult_ker1_sum00[7:0]};
  assign mult_sum_16x16_partial11 = {$signed(mult_ker1_sum11[16:0]) + $signed({ {8{mult_ker1_sum10[15]}}, mult_ker1_sum10[15:8]}), mult_ker1_sum10[7:0]};
  assign mult_ker1_sum = {mult_sum_16x16_partial11[23:0] + { {8{mult_sum_16x16_partial10[23]}}, mult_sum_16x16_partial10[23:8]}, mult_sum_16x16_partial10[7:0]};

  // Generate 32x16 results
  logic[47:0] mult_sum_32x16;
  // TODO: Do this through a GP adder that can be shared with accum and 32x32   // TODO: Check if we need sign-extension
  assign mult_sum_32x16 = {mult_ker1_sum[31:0] + {16'h0000, mult_ker0_sum[31:16]}, mult_ker0_sum[15:0]};
  // TODO Check if we can get away with only calculating 32-MSB, only saving 32 MSB in accum at least

  // Generate 32x32
  // Kinda tricky since we do it in two stages
  // First calculate quadrant 1 and 2, then 3 and 4, then add it all together
  logic[31:0] mult_sum_32x32_MSW;     // TODO: sign extension
  assign mult_sum_32x32_MSW = {mult_sum_32x16 + { {16{mult_accum_val[31]}}, mult_accum_val}}[47:16];    // TODO: Make sure mult_accum is on form {16'h0000, 16 MSB of LSBs}


  /*// Concatinate 16x16 results
  logic[31:0] mult_resH00;//, multresH11;

  // Brent-Krüger adder
  logic[24:0] mult_partial_add0, mult_partial_add1;
  assign mult_partial_add0 = {16'h0000, mult_resB00[15:8]} + {8'h00, mult_resB01[15:0]};
  assign mult_partial_add1 = {8'h00, mult_resB10[15:0]} + {mult_resB11[15:0], 8'h00};

  logic[25:0] mult_final_add;
  assign mult_final_add = mult_partial_add0 + mult_partial_add1;

  assign mult_resH00 = {mult_final_add, mult_resB00[7:0]}[31:0];


  // Brent-Krüger adder for 8-bit MAC and 16-bit results
  // 
  logic[23:0] mult_add_op_a0, mult_add_op_b0, mult_add_op_a1, mult_add_op_b1;
  logic[24:0] mult_add_p_sum0, mult_add_p_sum1;
  logic[25:0] mult_add_sum;

  assign mult_add_p_sum0 = mult_add_op_a0 + mult_add_op_b0;
  assign mult_add_p_sum1 = mult_add_op_a1 + mult_add_op_b1;
  assign mult_add_sum = mult_add_p_sum0 + mult_add_p_sum1;*/


  // Generate normal result
  logic[31:0] mult_normal_result;
  always_comb begin
    unique case(mult_mode)
      M8x8  : mult_normal_result = '0;
      M16x16: mult_normal_result = '0;
      M32x16: mult_normal_result = mult_sum_32x16[47:16];
      M32x32: mult_normal_result = '0;
    endcase
  end

  ////////////////
  // Saturation //
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

    unique case({width32_i, width8_i})    // Saturation mults are signed
      2'b10  :   saturated = {sat_ones[3] & sat_zeros[3], 3'b000};
      2'b01  :   saturated = {sat_ones[3] & sat_zeros[3], sat_ones[2] & sat_zeros[2], 
                              sat_ones[1] & sat_zeros[1], sat_ones[0] & sat_zeros[0]};
      default:   saturated = {sat_ones[3] & sat_zeros[3], 1'b0, sat_ones[1] & sat_zeros[1], 1'b0};
    endcase
  end

  // Generate Saturating results
  logic[31:0] mult_sat_result;
  always_comb begin
    unique case({signed_ops_i, width32_i, width8_i})                                              
      3'b101 : mult_sat_result = {saturated[3] ? 8'h7f : mult_sum_8x8_3[14:7], 
                                  saturated[2] ? 8'h7f : mult_sum_8x8_2[14:7],
                                  saturated[1] ? 8'h7f : mult_sum_8x8_1[14:7],
                                  saturated[0] ? 8'h7f : mult_sum_8x8_0[14:7]};

      3'b100 : mult_sat_result = {(saturated[3] & saturated[2]) ? 16'h7fff : mult_ker0_sum[30:15], // TODO
                                  (saturated[1] & saturated[0]) ? 16'h7fff : mult_ker1_sum[30:15]};

      default: mult_sat_result = saturated[3] ? 32'h7fff_ffff: mult_sum_32x32_MSW;
    endcase
  end

  logic[9:0] unused0, unused1, unused2, unused3;
  assign unused0 = {mult_sum_8x8_0[17:15], mult_sum_8x8_0[6:0]};
  assign unused1 = {mult_sum_8x8_1[17:15], mult_sum_8x8_1[6:0]};
  assign unused2 = {mult_sum_8x8_2[17:15], mult_sum_8x8_2[6:0]};
  assign unused3 = {mult_sum_8x8_3[17:15], mult_sum_8x8_3[6:0]};

  // Multiplier result mux
  /*always_comb begin
    unique case (operator_i)

      default: 
    endcase
  end*/

  // Final result Mux
  always_comb begin
    unique case(operator_i)
      // Saturating results
      ZPN_KHM16,  ZPN_KHMX16,
      ZPN_KHM8,   ZPN_KHMX8: mult_result_o = mult_sat_result;


      // Rounding results
      // TODO

      // Accumulating results
      // Accumulating ops are output in ALU

      ZPN_MADDR32: mult_result_o = mult_sum_32x32_MSW;

      // All other
      default: mult_result_o = mult_normal_result;
    endcase
  end

  // Concatinate 32x32 result
  //logic[63:0] mult_resW;
  logic[31:0] mult_accum_val_nxt;
  //assign mult_accum_val_nxt = '0;

  // Generate mult_accum_val_nxt
  always_comb begin
    unique case(operator_i)
      ZPN_SMAQA,  ZPN_UMAQA,
      ZPN_SMAQAsu: mult_accum_val_nxt = '0;
      default: mult_accum_val_nxt = mult_sum_32x16[47:16];
    endcase
  end


  /////////////////
  // Accumulator //
  /////////////////
  logic[31:0] mult_accum_val;
  logic       load_rd;
  always_ff @(posedge clk_i or negedge rst_ni) begin
    if (~rst_ni) begin
      mult_accum_val <= 32'h0000_0000;
    end
    else begin
      if (accum_en) begin
        if (load_rd) begin
          mult_accum_val <= rd_val_i;
        end
        else begin
          mult_accum_val <= mult_accum_val_nxt;
        end
      end
      else begin
        mult_accum_val <= mult_accum_val;
      end
    end
  end

  // Decode multiplier mode
  // Mostly for controlling the quadrant signal
  typedef enum logic[1:0] {
    M8x8, M16x16, M32x16, M32x32
  } mult_pext_mode_e;
  mult_pext_mode_e mult_mode;

  always_comb begin
    unique case (operator_i)
      ZPN_SMAQA,    ZPN_SMAQAsu,
      ZPN_UMAQA,    ZPN_KHM8,
      ZPN_KHMX8: mult_mode = M8x8;

      ZPN_SMMUL,    ZPN_SMMULu,
      ZPN_KMMAC,    ZPN_KMMACu,
      ZPN_KMMSB,    ZPN_KMMSBu,
      ZPN_KWMMUL,   ZPN_KWMMULu,
      ZPN_MADDR32,  ZPN_MSUBR32: mult_mode = M32x32;

      ZPN_SMMWB,    ZPN_SMMWBu,
      ZPN_SMMWT,    ZPN_SMMWTu,
      ZPN_KMMAWB,   ZPN_KMMAWBu,
      ZPN_KMMAWT,   ZPN_KMMAWTu,
      ZPN_KMMWB2,   ZPN_KMMWB2u,
      ZPN_KMMWT2,   ZPN_KMMWT2u,
      ZPN_KMMAWB2,  ZPN_KMMAWB2u,
      ZPN_KMMAWT2,  ZPN_KMMAWT2u: mult_mode = M32x16;

      default: mult_mode = M16x16;    // Defaulting to 16x16 mults
    endcase
  end

  // Assign quadrant signal
  always_comb begin
    unique case (mult_mode)
      M8x8  : quadrant = 2'b00;
      M16x16: quadrant = crossed ? 2'b11 : 2'b00;
      M32x16: quadrant = crossed ? 2'b01 : 2'b10;
      M32x32: quadrant = (mult_state == UPPER) ? 2'b01 : 2'b10;
    endcase
  end

  // FSM state enum
  typedef enum logic[1:0] {
    LOWER, UPPER, ACCUM
  } mult_pext_fsm_e;
  mult_pext_fsm_e    mult_state, mult_state_next;

  // FSM state decoding
  always_comb begin
    unique case (mult_state)
      LOWER: begin
        load_rd = accum_en ? 1'b0 : 1'b0;

        mult_state_next = (mult_mode == M32x32) ? UPPER : (accum_en ? ACCUM : LOWER);
      end

      UPPER: begin
        load_rd = 1'b0;

        mult_state_next = accum_en ? ACCUM : LOWER;
      end

      ACCUM: begin
        load_rd = 1'b0;

        mult_state_next = LOWER;
      end

      default: mult_state_next = LOWER;
    endcase
  end

  // FSM state clocking
  always_ff @(posedge clk_i or negedge rst_ni) begin
    if (~rst_ni) begin
      mult_state <= LOWER;
    end
    else begin
      if (mult_en_i) begin
        mult_state <= mult_state_next;
      end
    end
  end

endmodule
