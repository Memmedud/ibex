// Copyright lowRISC contributors.
// Copyright 2018 ETH Zurich and University of Bologna, see also CREDITS.md.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

/*
 * Special Arithmetic logic unit for P-ext instructions
 */
module ibex_alu_pext #(
  parameter SAT_VAL_U8    = 8'hff,    // 255
  parameter SAT_VAL_S8L   = 8'h80,    // -128
  parameter SAT_VAL_S8H   = 8'h7f,    // 127
  parameter SAT_VAL_S16L  = 16'h8000, // -32768
  parameter SAT_VAL_S16H  = 16'h7fff  // 32767
) (
  input  logic [31:0]                   operand_a_i,
  input  logic [31:0]                   operand_b_i,
  input  logic                          enable_i,

  // Decoder signals
  input  ibex_pkg_pext::signed_type_e   signed_operands_i,
  input  ibex_pkg_pext::zpn_op_e        operator_i,

  //input  logic [32:0]                   multdiv_operand_a_i,
  //input  logic [32:0]                   multdiv_operand_b_i,

  //input  logic [31:0]                   imd_val_q_i[2],
  //output logic [31:0]                   imd_val_d_o[2],
  //output logic [1:0]                    imd_val_we_o,
  input  logic [31:0]                   mult_result_i,
  output logic [31:0]                   result_o
);
  import ibex_pkg_pext::*;

  ///////////
  // Adder //
  ///////////

  // Decode instructions that use subtraction
  logic[1:0] sub;
  always_comb begin
    unique case (operator_i)
      // Subtraction ops
      ZPN_RSUB16,   ZPN_RSUB8,
      ZPN_KSUB16,   ZPN_KSUB8,
      ZPN_URSUB16,  ZPN_URSUB8,
      ZPN_UKSUB16,  ZPN_UKSUB8,
      ZPN_SUB16,    ZPN_SUB8,
      // Comparator ops
      ZPN_CMPEQ16,  ZPN_CMPEQ8,
      ZPN_SCMPLT16, ZPN_SCMPLT8,
      ZPN_SCMPLE16, ZPN_SCMPLE8,
      ZPN_UCMPLT16, ZPN_UCMPLT8,
      ZPN_UCMPLE16, ZPN_UCMPLE8,
      // Min/Max ops
      ZPN_SMIN16, ZPN_SMIN8,
      ZPN_SMAX16, ZPN_SMAX8,
      ZPN_UMIN16, ZPN_UMIN8,
      ZPN_UMAX16, ZPN_UMAX8: sub = 2'b11;

      // Sub/Add ops
      ZPN_RCRSA16,  ZPN_RSTSA16,
      ZPN_KCRSA16,  ZPN_KSTSA16,
      ZPN_URCRSA16, ZPN_URSTSA16,
      ZPN_UKCRSA16, ZPN_UKSTSA16,
      ZPN_CRSA16,   ZPN_STSA16: sub = 2'b10;

      // Add/Sub ops
      ZPN_RCRAS16,  ZPN_RSTAS16,
      ZPN_KCRAS16,  ZPN_KSTAS16,
      ZPN_URCRAS16, ZPN_URSTAS16,
      ZPN_UKCRAS16, ZPN_UKSTAS16,
      ZPN_CRAS16,   ZPN_STAS16: sub = 2'b01;
      
      // All other ops require Add
      default: sub = 2'b00;
    endcase
  end

  // Decode data width
  logic width8;
  always_comb begin
    unique case(signed_operands_i)
      U8, S8:   width8 = 1'b1;
      default:  width8 = 1'b0;
    endcase
  end

  // Decode cross Add/Sub
  logic crossed;
  always_comb begin
    unique case(operator_i)
          ZPN_RCRAS16,  ZPN_RCRSA16, 
          ZPN_KCRAS16,  ZPN_KCRSA16,
          ZPN_URCRAS16, ZPN_URCRSA16, 
          ZPN_UKCRAS16, ZPN_UKCRSA16,
          ZPN_CRAS16,   ZPN_CRSA16: crossed = 1'b1;

          default: crossed = 1'b0;
    endcase
  end

  // Prepare operands
  logic[7:0]  adder_in_a0, adder_in_a1, adder_in_a2, adder_in_a3,
              adder_tmp_b0, adder_tmp_b1, adder_tmp_b2, adder_tmp_b3,
              adder_in_b0, adder_in_b1, adder_in_b2, adder_in_b3;
  logic       sub8;

  assign sub8 = width8 & sub[0];  // For 8-bit we assume no combined add/sub

  assign adder_in_a0 = {operand_a_i[7:0]};
  assign adder_in_a1 = {operand_a_i[15:8]};
  assign adder_in_a2 = {operand_a_i[23:16]};
  assign adder_in_a3 = {operand_a_i[31:24]};

  assign adder_tmp_b0 = crossed ? {operand_b_i[23:16]} : {operand_b_i[7:0]};
  assign adder_tmp_b1 = crossed ? {operand_b_i[31:24]} : {operand_b_i[15:8]};
  assign adder_tmp_b2 = crossed ? {operand_b_i[7:0]}   : {operand_b_i[23:16]};
  assign adder_tmp_b3 = crossed ? {operand_b_i[15:8]}  : {operand_b_i[31:24]};

  assign adder_in_b0 = sub[0] ? ~adder_tmp_b0 : adder_tmp_b0;
  assign adder_in_b1 = sub[0] ? ~adder_tmp_b1 : adder_tmp_b1;
  assign adder_in_b2 = sub[1] ? ~adder_tmp_b2 : adder_tmp_b2;
  assign adder_in_b3 = sub[1] ? ~adder_tmp_b3 : adder_tmp_b3;

  // Actual adder
  logic[8:0]  adder_result0, adder_result1, adder_result2, adder_result3;
  logic       carry_out0, carry_out1;

  assign adder_result0 = adder_in_a0 + adder_in_b0 + {7'b000_0000, sub[0]};
  assign adder_result1 = adder_in_a1 + adder_in_b1 + {7'b000_0000, sub8} + {7'b000_0000, carry_out0};
  assign adder_result2 = adder_in_a2 + adder_in_b2 + {7'b000_0000, sub[1]};
  assign adder_result3 = adder_in_a3 + adder_in_b3 + {7'b000_0000, sub8} + {7'b000_0000, carry_out1};

  assign carry_out0 = ~width8 & adder_result0[8];
  assign carry_out1 = ~width8 & adder_result2[8];

  // Concatinate the regular output
  logic[31:0] normal_result;
  assign normal_result = {adder_result3[7:0], adder_result2[7:0], adder_result1[7:0], adder_result0[7:0]};

  // Calulate halving results
  logic[31:0] halving_result;
  always_comb begin
    unique case (signed_operands_i)
      U8:   halving_result = { {adder_result3[8:1]},
                               {adder_result2[8:1]},
                               {adder_result1[8:1]},
                               {adder_result0[8:1]} };

      S8:   halving_result = { {adder_result3[7], adder_result3[7:1]},
                               {adder_result2[7], adder_result2[7:1]},
                               {adder_result1[7], adder_result1[7:1]},
                               {adder_result0[7], adder_result0[7:1]} };

      U16:  halving_result = { {adder_result3[8:0]},
                               {adder_result2[7:1]},
                               {adder_result1[8:0]},
                               {adder_result0[7:1]} };

      S16:  halving_result = { {adder_result3[7], adder_result3[7:0]},
                               {adder_result2[7:1]                  },
                               {adder_result1[7], adder_result1[7:0]},
                               {adder_result0[7:1]                  } };
    endcase
  end

  // Calulate saturating result     // TODO: Remember to set OV bit when overflow
  logic[31:0] saturating_result;
  logic[3:0]  saturated;
  logic       set_ov;

  // Decode saturation state
  assign set_ov = |saturated;
  assign saturated = { ((adder_in_a0[7] ^ adder_tmp_b0[7]) ^ sub[0]) & (^adder_result0[8:7]), 
                       ((adder_in_a1[7] ^ adder_tmp_b1[7]) ^ sub[0]) & (^adder_result1[8:7]), 
                       ((adder_in_a2[7] ^ adder_tmp_b2[7]) ^ sub[1]) & (^adder_result2[8:7]), 
                       ((adder_in_a3[7] ^ adder_tmp_b3[7]) ^ sub[1]) & (^adder_result3[8:7]) };

  always_comb begin
    unique case (signed_operands_i)
      U8:  saturating_result = { (adder_result3[8] ? SAT_VAL_U8 : adder_result3[7:0]),      // TODO: Need to check lower bound for sub on unsigned!!!!
                                 (adder_result2[8] ? SAT_VAL_U8 : adder_result2[7:0]),
                                 (adder_result1[8] ? SAT_VAL_U8 : adder_result1[7:0]),
                                 (adder_result0[8] ? SAT_VAL_U8 : adder_result0[7:0]) }; 

      // [8:7] == 10 gives underflow, [8:7] == 01 gives overflow  // TODO: Give S8 the same treatment...
      S8:  saturating_result = { (adder_result3[8:7] == 2'b10) ? SAT_VAL_S8L : (adder_result3[8:7] == 2'b01 ? SAT_VAL_S8H : adder_result3[7:0]),
                                 (adder_result2[8:7] == 2'b10) ? SAT_VAL_S8L : (adder_result2[8:7] == 2'b01 ? SAT_VAL_S8H : adder_result2[7:0]),
                                 (adder_result1[8:7] == 2'b10) ? SAT_VAL_S8L : (adder_result1[8:7] == 2'b01 ? SAT_VAL_S8H : adder_result1[7:0]),
                                 (adder_result0[8:7] == 2'b10) ? SAT_VAL_S8L : (adder_result0[8:7] == 2'b01 ? SAT_VAL_S8H : adder_result0[7:0]) }; 

      U16: saturating_result = { (adder_result3[8] ? SAT_VAL_U8 : adder_result3[7:0]),      // TODO: Figure out if we need to do lower saturating as well YES WE DO
                                 (adder_result3[8] ? SAT_VAL_U8 : adder_result2[7:0]),
                                 (adder_result1[8] ? SAT_VAL_U8 : adder_result1[7:0]),
                                 (adder_result1[8] ? SAT_VAL_U8 : adder_result0[7:0]) };

      // S16, [8:7] == 10 gives underflow, [8:7] == 01 gives overflow
      default: saturating_result = { saturated[3] ? (adder_result3[8] ? SAT_VAL_S16L : SAT_VAL_S16H) : {adder_result3[7:0], adder_result2[7:0]},
                                     saturated[1] ? (adder_result1[8] ? SAT_VAL_S16L : SAT_VAL_S16H) : {adder_result1[7:0], adder_result0[7:0]} };
    endcase
  end

  // Adder results mux
  logic[31:0] adder_result;

  always_comb begin
    unique case(operator_i)
      ZPN_URCRAS16, ZPN_URCRSA16,
      ZPN_RCRAS16,  ZPN_RCRSA16,
      ZPN_URSTAS16, ZPN_URSTSA16,
      ZPN_RSTAS16,  ZPN_RSTSA16,
      ZPN_URADD16,  ZPN_URADD8,
      ZPN_RADD16,   ZPN_RADD8,
      ZPN_URSUB16,  ZPN_URSUB8,
      ZPN_RSUB16,   ZPN_RSUB8: adder_result = halving_result;

      ZPN_UKCRAS16, ZPN_UKCRSA16,
      ZPN_KCRAS16,  ZPN_KCRSA16,
      ZPN_UKSTAS16, ZPN_UKSTSA16,
      ZPN_KSTAS16,  ZPN_KSTSA16,
      ZPN_UKADD16,  ZPN_UKADD8,
      ZPN_KADD16,   ZPN_KADD8,
      ZPN_UKSUB16,  ZPN_UKSUB8,
      ZPN_KSUB16,   ZPN_KSUB8: adder_result = saturating_result;

      default: adder_result = normal_result;
    endcase 
  end


  ////////////////
  // Multiplier //
  ////////////////
  // Im afraid
  // Sorta donee??
  


  ////////////////
  // Comparison //
  ////////////////
  logic[3:0]    is_byte_equal, is_equal;   // One bit for each byte
  logic[3:0]    is_byte_less,  is_less;    // handles both signed and unsigned forms
  logic         comp_signed;

  // Determine if operands are signed
  always_comb begin
    unique case (signed_operands_i)
      S8, S16:  comp_signed = 1'b1;
      default:  comp_signed = 1'b0;
    endcase
  end

  // calculate is_equal
  always_comb begin
    is_byte_equal = 4'b0000;

    // Decoding is done in the adder
    for (int unsigned b = 0; b < 4; b++) if (adder_result[8*b +: 8] == 8'h00) begin
      is_byte_equal[b] = 1'b1;
    end

    unique case (signed_operands_i)
      U16, S16: is_equal = { &is_byte_equal[3:2], 
                             &is_byte_equal[3:2], 
                             &is_byte_equal[1:0], 
                             &is_byte_equal[1:0] };

      default:  is_equal = is_byte_equal;
    endcase
  end

  // Calculate is_less
  always_comb begin
    is_byte_less = 4'b0000;
    
    for (int unsigned b = 0; b < 4; b++) begin
      if ((operand_a_i[8*b+7] ^ operand_b_i[8*b+7]) == 1'b0) begin
        is_byte_less[b] = (adder_result[8*b+7] == 1'b1);
      end
      else begin
        is_byte_less[b] = ~(operand_a_i[8*b+7] ^ (comp_signed));
      end
    end

    unique case (signed_operands_i)
      U16, S16: is_less = { is_byte_less[3], 
                            is_byte_less[3], 
                            is_byte_less[1], 
                            is_byte_less[1] };

      // Including U8 and S8
      default:  is_less = is_byte_less;
    endcase
  end

  // Comparator result mux
  logic[3:0]    comp_result_packed;

  always_comb begin
    unique case (operator_i)
      // Less than
      ZPN_SMIN16,   ZPN_SMIN8,
      ZPN_UMIN16,   ZPN_UMIN8,
      ZPN_SCMPLT16, ZPN_SCMPLT8,
      ZPN_UCMPLT16, ZPN_UCMPLT8:  comp_result_packed = is_less;

      // Less than or equal
      ZPN_SCMPLE16, ZPN_SCMPLE8,
      ZPN_UCMPLE16, ZPN_UCMPLE8:  comp_result_packed = is_equal | is_less;

      // Greater than, only used for max
      ZPN_SMAX16,   ZPN_SMAX8,
      ZPN_UMAX16,   ZPN_UMAX8:    comp_result_packed = ~(is_equal | is_less);
      
      // Including is equal
      default:                    comp_result_packed = is_equal;
    endcase
  end

  // Widen output from bitwise to bytewise
  logic[31:0]   comp_result;
  assign comp_result = { {8{comp_result_packed[3]}},
                         {8{comp_result_packed[2]}},
                         {8{comp_result_packed[1]}},
                         {8{comp_result_packed[0]}} };


  // TODO: Clip, abs, function...
  /////////////
  // Min/Max //
  /////////////
  logic[31:0]   minmax_result;

  // Dont need to check for byte or halfword as this is done in the comparator
  always_comb begin
    for (int unsigned b = 0; b < 4; b++) begin
      minmax_result[8*b +: 8] = comp_result_packed[b] ? operand_a_i[8*b +: 8] : operand_b_i[8*b +: 8];
    end
  end


  ////////////////
  // Bit-shifts //
  ////////////////
  // TODO: Fix this description
  // Using 2 16-bit shifters. to shift both halfwords right
  // then 2 8-bit shifters to conditionally shift byte 2 and 0 left then choose between 16 or 8 bit 
  

  // Decode if we should left-shift (right shifting by default)
  logic shift_left;
  always_comb begin
    unique case (operator_i)
      ZPN_SLL16,  ZPN_SLL8,
      ZPN_SLLI16, ZPN_SLLI8: shift_left = 1'b1;
      default:               shift_left = 1'b0;
    endcase
  end

  // Decode if we should do arithmetic shift
  logic shift_arith;
  always_comb begin
    unique case (signed_operands_i)
      S16, S8: shift_arith = 1'b1;
      default: shift_arith = 1'b0;
    endcase
  end

  // bit-reverse operand_a for left shifts
  logic[31:0] operand_a_rev;
  for (genvar i = 0; i < 32; i++) begin : gen_rev_operand
    assign operand_a_rev[i] = operand_a_i[31-i];
  end

  // Prepare operands
  logic[15:0]   shift_operand0, shift_operand1;
  logic[3:0]    shift_amt;

  assign shift_operand0 = shift_left ? operand_a_rev[15:0]  : operand_a_i[15:0];
  assign shift_operand1 = shift_left ? operand_a_rev[31:16] : operand_a_i[31:16];
  assign shift_amt      = operand_b_i[3:0];
  
  // First shifter
  logic[16:0]   shift_result_first0, shift_result_first1;
  logic[1:0]    unused_shift_result_first; 
  
  assign shift_result_first0 = $signed({ (shift_arith & shift_operand0[15]), shift_operand0}) >>> shift_amt;
  assign shift_result_first1 = $signed({ (shift_arith & shift_operand1[15]), shift_operand1}) >>> shift_amt;
  assign unused_shift_result_first = {shift_result_first0[16], shift_result_first1[16]};

  // Second conditional shifter 
  logic[8:0]    shift_result_second0, shift_result_second2;   // Only need to do this for byte 2 and 0
  logic[1:0]    unused_shift_result_second;

  assign shift_result_second0  = $signed({ (shift_arith & shift_operand0[7]), shift_operand0[7:0]}) >>> shift_amt[2:0];
  assign shift_result_second2  = $signed({ (shift_arith & shift_operand1[7]), shift_operand1[7:0]}) >>> shift_amt[2:0];
  assign unused_shift_result_second = {shift_result_second2[8], shift_result_second0[8]};

  // Concatinate result
  logic[31:0] shift_result_full;
  always_comb begin
    unique case (signed_operands_i)
      S8, U8 :  shift_result_full = {shift_result_first1[15:8], shift_result_second2[7:0], shift_result_first0[15:8], shift_result_second0[7:0]};
      default:  shift_result_full = {shift_result_first1[15:0], shift_result_first0[15:0]};
    endcase
  end
  
  // Flip bytes for Left-shifting
  logic[31:0] shift_result_rev;
  always_comb begin
    for (int unsigned i = 0; i < 32; i++) begin
      shift_result_rev[i] = shift_result_full[31-i];
    end
  end

  // Produce final shifter output
  logic[31:0] shift_result;
  assign shift_result = shift_left ? shift_result_rev : shift_result_full;


  //////////////////
  // Bit-counting //
  //////////////////
  // Prepare operand
  logic[3:0] negate;
  always_comb begin
    unique case(signed_operands_i)
      U8, U16: negate = 4'b1111;
      S8:      negate = {~operand_a_i[31], ~operand_a_i[24], ~operand_a_i[15], ~operand_a_i[7]};
      S16:     negate = { {2{~operand_a_i[31]}}, {2{~operand_a_i[15]}}};
    endcase
  end

  // Have to do this because Verilat0r is quirky, Im sorry... 
  logic bc0, bc1, bc2, bc3, bc4, bc5, bc6, bc7, bc8, bc9, bc10, bc11, bc12, bc13, bc14, bc15,
        bc16, bc17, bc18, bc19, bc20, bc21, bc22, bc23, bc24, bc25, bc26, bc27, bc28, bc29, bc30, bc31;

  assign bc31 = negate[3] ? ~operand_a_i[31] : operand_a_i[31];
  assign bc30 = negate[3] ? (~operand_a_i[30] & bc31) : (operand_a_i[30] & bc31);
  assign bc29 = negate[3] ? (~operand_a_i[29] & bc30) : (operand_a_i[29] & bc30);
  assign bc28 = negate[3] ? (~operand_a_i[28] & bc29) : (operand_a_i[28] & bc29);
  assign bc27 = negate[3] ? (~operand_a_i[27] & bc28) : (operand_a_i[27] & bc28);
  assign bc26 = negate[3] ? (~operand_a_i[27] & bc27) : (operand_a_i[27] & bc27);
  assign bc25 = negate[3] ? (~operand_a_i[25] & bc26) : (operand_a_i[25] & bc26);
  assign bc24 = negate[3] ? (~operand_a_i[24] & bc25) : (operand_a_i[24] & bc25);

  assign bc23 = width8 ? (negate[2] ? ~operand_a_i[23] : operand_a_i[23]) : (negate[2] ? (~operand_a_i[23] & bc24) : (operand_a_i[23] & bc24)); 
  assign bc22 = negate[2] ? (~operand_a_i[22] & bc23) : (operand_a_i[22] & bc23);
  assign bc21 = negate[2] ? (~operand_a_i[21] & bc22) : (operand_a_i[21] & bc22);
  assign bc20 = negate[2] ? (~operand_a_i[20] & bc21) : (operand_a_i[20] & bc21);
  assign bc19 = negate[2] ? (~operand_a_i[19] & bc20) : (operand_a_i[19] & bc20);
  assign bc18 = negate[2] ? (~operand_a_i[18] & bc19) : (operand_a_i[18] & bc19);
  assign bc17 = negate[2] ? (~operand_a_i[17] & bc18) : (operand_a_i[17] & bc18);
  assign bc16 = negate[2] ? (~operand_a_i[16] & bc17) : (operand_a_i[16] & bc17);

  assign bc15 = negate[1] ? ~operand_a_i[15] : operand_a_i[15];
  assign bc14 = negate[1] ? (~operand_a_i[14] & bc15) : (operand_a_i[14] & bc15);
  assign bc13 = negate[1] ? (~operand_a_i[13] & bc14) : (operand_a_i[13] & bc14);
  assign bc12 = negate[1] ? (~operand_a_i[12] & bc13) : (operand_a_i[12] & bc13);
  assign bc11 = negate[1] ? (~operand_a_i[11] & bc12) : (operand_a_i[11] & bc12);
  assign bc10 = negate[1] ? (~operand_a_i[10] & bc11) : (operand_a_i[10] & bc11);
  assign bc9  = negate[1] ? (~operand_a_i[9] & bc10)  : (operand_a_i[9]  & bc10);
  assign bc8  = negate[1] ? (~operand_a_i[8] & bc9)   : (operand_a_i[8]  & bc9);

  assign bc7  = width8 ? (negate[0] ? ~operand_a_i[7] : operand_a_i[7]) : (negate[0] ? (~operand_a_i[7] & bc8) : (operand_a_i[7] & bc8)); 
  assign bc6  = negate[0] ? (~operand_a_i[6] & bc7)   : (operand_a_i[6] & bc7);
  assign bc5  = negate[0] ? (~operand_a_i[5] & bc6)   : (operand_a_i[5] & bc6);
  assign bc4  = negate[0] ? (~operand_a_i[4] & bc5)   : (operand_a_i[4] & bc5);
  assign bc3  = negate[0] ? (~operand_a_i[3] & bc4)   : (operand_a_i[3] & bc4);
  assign bc2  = negate[0] ? (~operand_a_i[2] & bc3)   : (operand_a_i[2] & bc3);
  assign bc1  = negate[0] ? (~operand_a_i[1] & bc2)   : (operand_a_i[1] & bc2);
  assign bc0  = negate[0] ? (~operand_a_i[0] & bc1)   : (operand_a_i[0] & bc1);
    
  logic[31:0]   bit_cnt_operand;
  assign bit_cnt_operand = {bc31, bc30, bc29, bc28, bc27, bc26, bc25, bc24, bc23, bc22, bc21, bc20, bc19, bc18, bc17, bc16, 
                            bc15, bc14, bc13, bc12, bc11, bc10, bc9,  bc8,  bc7,  bc6,  bc5,  bc4,  bc3,  bc2,  bc1,  bc0};

  // Bit counter is a Brent-Kung Adder
  // TODO: Add some more info on this
  // First Adder layer
  logic[31:0]   bit_cnt_first_layer;  // We get 16 2-bit results
  for (genvar i = 0; i < 16; i++) begin : gen_bit_cnt_adder1
    assign bit_cnt_first_layer[2*i+1 : 2*i] = bit_cnt_operand[2*i] + bit_cnt_operand[2*i + 1];
  end

  // Second adder layer
  logic[23:0]   bit_cnt_second_layer; // And 8 3-bit results
  for (genvar i = 0; i < 8; i++) begin : gen_bit_cnt_adder2
    assign bit_cnt_second_layer[3*i +: 3] = bit_cnt_first_layer[4*i+1 : 4*i] + bit_cnt_first_layer[4*i+3 : 4*i+2];
  end

  // Third adder layer  // For 8-bit we stop at 3 layers
  logic[15:0]   bit_cnt_third_layer;  // And 4 4-bit results
  for (genvar i = 0; i < 4; i++) begin : gen_bit_cnt_adder3
    assign bit_cnt_third_layer[4*i +: 4] = bit_cnt_second_layer[6*i+2 : 6*i] + bit_cnt_second_layer[6*i+5 : 6*i+3];
  end

  // Fourth adder layer
  logic[9:0]   bit_cnt_fourth_layer;  // And 2 5-bit results
  assign bit_cnt_fourth_layer[4:0] = {1'b0, bit_cnt_third_layer[3:0]}  + {1'b0, bit_cnt_third_layer[7:4]};
  assign bit_cnt_fourth_layer[9:5] = {1'b0, bit_cnt_third_layer[11:8]} + {1'b0, bit_cnt_third_layer[15:12]};

  // Concatinate results
  logic[31:0]   bit_cnt_result_width8, bit_cnt_result_width16;
  assign bit_cnt_result_width8 = {4'b0000, bit_cnt_third_layer[15:12], 
                                  4'b0000, bit_cnt_third_layer[11:8] , 
                                  4'b0000, bit_cnt_third_layer[7:4]  , 
                                  4'b0000, bit_cnt_third_layer[3:0]   };

  assign bit_cnt_result_width16 = {11'h000, bit_cnt_fourth_layer[9:5], 
                                   11'h000, bit_cnt_fourth_layer[4:0] };

  // Bit-count result mux
  logic[31:0]   bit_cnt_result;   // TODO: Make a "global" width8 signal
  assign bit_cnt_result = width8 ? bit_cnt_result_width8 : bit_cnt_result_width16;


  ////////////////
  // UNPACK-X-Y //
  ////////////////
  logic[31:0]   unpack_result;
  logic[7:0]    byte0, byte1, byte2, byte3;

  // We ignore operand B for this operator
  assign byte0 = operand_a_i[7:0];
  assign byte1 = operand_a_i[15:8];
  assign byte2 = operand_a_i[23:16];
  assign byte3 = operand_a_i[31:24];

  always_comb begin
    unpack_result = '0;

    unique case (operator_i)
      ZPN_SUNPKD810: unpack_result = { {8{byte1[7]}}, byte1, {8{byte0[7]}}, byte0};
      ZPN_SUNPKD820: unpack_result = { {8{byte2[7]}}, byte2, {8{byte0[7]}}, byte0};
      ZPN_SUNPKD830: unpack_result = { {8{byte3[7]}}, byte3, {8{byte0[7]}}, byte0};
      ZPN_SUNPKD831: unpack_result = { {8{byte3[7]}}, byte3, {8{byte1[7]}}, byte1};
      ZPN_SUNPKD832: unpack_result = { {8{byte3[7]}}, byte3, {8{byte2[7]}}, byte2};
      ZPN_ZUNPKD810: unpack_result = {  8'b0000_0000, byte1,  8'b0000_0000, byte0};
      ZPN_ZUNPKD820: unpack_result = {  8'b0000_0000, byte2,  8'b0000_0000, byte0};
      ZPN_ZUNPKD830: unpack_result = {  8'b0000_0000, byte3,  8'b0000_0000, byte0};
      ZPN_ZUNPKD831: unpack_result = {  8'b0000_0000, byte3,  8'b0000_0000, byte1};
      ZPN_ZUNPKD832: unpack_result = {  8'b0000_0000, byte3,  8'b0000_0000, byte2};
      default: ;
    endcase
  end


  /////////////
  // PACKING //
  /////////////
  logic[31:0] packing_result;
  logic[15:0] paking_half_a0, paking_half_a1, paking_half_b0, paking_half_b1;

  assign paking_half_a0 = operand_a_i[15:0];
  assign paking_half_a1 = operand_a_i[31:16];
  assign paking_half_b0 = operand_b_i[15:0];
  assign paking_half_b1 = operand_b_i[31:16];

  always_comb begin
    packing_result = '0;
    unique case (operator_i)
      ZPN_PKBB16: packing_result = {paking_half_a0, paking_half_b0};
      ZPN_PKBT16: packing_result = {paking_half_a0, paking_half_b1};
      ZPN_PKTB16: packing_result = {paking_half_a1, paking_half_b0};
      ZPN_PKTT16: packing_result = {paking_half_a1, paking_half_b1};
    endcase
  end

  /////////////
  // Average //
  /////////////
  // TODO
    // Assuming we can put rd on rs2, then we good
  // Make the adder support full 32-bit add


  /////////////////
  // Insert Byte //
  /////////////////
  // TODO
  /*logic[31:0]   insb_result;
  logic[7:0]    insb_byte;

  assign insb_byte = operand_a_i[7:0];

  always_comb begin
    insbre
  end*/


  ////////////////
  // Result mux //
  ////////////////
  always_comb begin
    result_o   = '0;

    if (enable_i) begin
      unique case (operator_i)
        // Add ops
        // TODO: Figure out if we need Add/Sub64
        /*ZPN_RADD64, */  ZPN_RADD16,   ZPN_RADD8,
        /*ZPN_KADD64, */  ZPN_KADD16,   ZPN_KADD8,
        /*ZPN_URADD64,*/  ZPN_URADD16,  ZPN_URADD8,
        /*ZPN_UKADD64,*/  ZPN_UKADD16,  ZPN_UKADD8,
        /*ZPN_ADD64,  */  ZPN_ADD16,    ZPN_ADD8,
        // Sub ops
        /*ZPN_RSUB64, */  ZPN_RSUB16,   ZPN_RSUB8,
        /*ZPN_KSUB64, */  ZPN_KSUB16,   ZPN_KSUB8,
        /*ZPN_URSUB64,*/  ZPN_URSUB16,  ZPN_URSUB8,
        /*ZPN_UKSUB64,*/  ZPN_UKSUB16,  ZPN_UKSUB8,
        /*ZPN_SUB64,  */  ZPN_SUB16,    ZPN_SUB8,
        // Cross Add/Sub ops
        ZPN_RCRAS16,  ZPN_RCRSA16,
        ZPN_KCRAS16,  ZPN_KCRSA16,
        ZPN_URCRAS16, ZPN_URCRSA16,
        ZPN_UKCRAS16, ZPN_UKCRSA16,
        ZPN_CRAS16,   ZPN_CRSA16,
        // Staright Add/Sub ops
        ZPN_RSTAS16,  ZPN_RSTSA16,
        ZPN_KSTAS16,  ZPN_KSTSA16,
        ZPN_URSTAS16, ZPN_URSTSA16,
        ZPN_UKSTAS16, ZPN_UKSTSA16,
        ZPN_STAS16,   ZPN_STSA16: result_o = adder_result;

        // Mult ops
        ZPN_SMUL16,   ZPN_SMUL8,
        ZPN_SMULX16,  ZPN_SMULX8,
        ZPN_UMUL16,   ZPN_UMUL8,
        ZPN_UMULX16,  ZPN_UMULX8,
        ZPN_KHM16,    ZPN_KHM8,
        ZPN_KHMX16,   ZPN_KHMX8: result_o = mult_result_i;
        // TODO: There are many more multiplications

        // Comparison ops
        ZPN_CMPEQ16,  ZPN_CMPEQ8,
        ZPN_SCMPLT16, ZPN_SCMPLT8,
        ZPN_SCMPLE16, ZPN_SCMPLE8,
        ZPN_UCMPLT16, ZPN_UCMPLT8,
        ZPN_UCMPLE16, ZPN_UCMPLE8: result_o = comp_result;

        // Min/Max ops
        ZPN_SMIN16, ZPN_SMIN8,
        ZPN_SMAX16, ZPN_SMAX8,
        ZPN_UMIN16, ZPN_UMIN8,
        ZPN_UMAX16, ZPN_UMAX8: result_o = minmax_result;

        // Shift ops      // Omitting rounding shifts for now And Immediate is not implemented properly
        ZPN_SRA16,    ZPN_SRA8,
        ZPN_SRAI16,   ZPN_SRAI8,
        ZPN_SRL16,    ZPN_SRL8,
        ZPN_SRLI16,   ZPN_SRLI8,
        ZPN_SLL16,    ZPN_SLL8,
        ZPN_SLLI16,   ZPN_SLLI8: result_o = shift_result;
      //ZPN_KSLL16,   ZPN_KSLL8,
      //ZPN_KSLLI16,  ZPN_KSLLI8,
      //ZPN_KSLRA16,  ZPN_KSLRA8:    // These seems tricky to implement
        
        // Bit-count ops
        ZPN_CLRS16, ZPN_CLRS8,
        ZPN_CLZ16,  ZPN_CLZ8: result_o = bit_cnt_result;

        // Unpack ops
        ZPN_SUNPKD810, ZPN_ZUNPKD810,
        ZPN_SUNPKD820, ZPN_ZUNPKD820,
        ZPN_SUNPKD830, ZPN_ZUNPKD830,
        ZPN_SUNPKD831, ZPN_ZUNPKD831,
        ZPN_SUNPKD832, ZPN_ZUNPKD832: result_o = unpack_result;

        // Paking ops
        ZPN_PKBB16, ZPN_PKBT16,
        ZPN_PKTB16, ZPN_PKTT16: result_o = packing_result;

        // INSB ops   // TODO
      //ZPN_INSB0, ZPN_INSB1
      //ZPN_INSB2, ZPN_INSB3: result_o = insb_result;

        // Misc ops   // TODO
        //ZPN_AVE:  result_o = 

        default: ;
      endcase
    end
  end

endmodule
