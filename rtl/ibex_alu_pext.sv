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

  output logic [31:0]                   result_o
);
  import ibex_pkg_pext::*;

  ///////////
  // Adder //
  ///////////

  // Decode instructions that use subtraction
  logic sub;
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
      ZPN_UMAX16, ZPN_UMAX8: sub = 1'b1;

      default: sub = 1'b0;
    endcase
  end

  // Prepare operands
  logic[7:0]  adder_in_a0, adder_in_a1, adder_in_a2, adder_in_a3, 
              adder_in_b0, adder_in_b1, adder_in_b2, adder_in_b3;
  logic       sub8, sub16;
  logic       width8;

  assign adder_in_a0 = operand_a_i[7:0];
  assign adder_in_a1 = operand_a_i[15:8];
  assign adder_in_a2 = operand_a_i[23:16];
  assign adder_in_a3 = operand_a_i[31:24];

  // TODO: Change sub to more bits to support cross add/sub?
  assign adder_in_b0 = sub ? ~operand_b_i[7:0]   : operand_b_i[7:0];
  assign adder_in_b1 = sub ? ~operand_b_i[15:8]  : operand_b_i[15:8];
  assign adder_in_b2 = sub ? ~operand_b_i[23:16] : operand_b_i[23:16];
  assign adder_in_b3 = sub ? ~operand_b_i[31:24] : operand_b_i[31:24];

  always_comb begin
    sub16 = sub;
    unique case(signed_operands_i)
      U8,  S8: sub8 = sub;
      default: sub8 = 1'b0;
    endcase
  end

  always_comb begin
    unique case(signed_operands_i)
      U8, S8:   width8 = 1'b1;
      default:  width8 = 1'b0;
    endcase
  end

  // Actual adder
  logic[8:0]  alu_result0, alu_result1, alu_result2, alu_result3;
  logic       carry_out0, carry_out1;

  assign alu_result0 = (adder_in_a0) + (adder_in_b0) + {7'b000_0000, sub16};
  assign alu_result1 = (adder_in_a1) + (adder_in_b1) + {7'b000_0000, sub8} + {7'b000_0000, carry_out0};
  assign alu_result2 = (adder_in_a2) + (adder_in_b2) + {7'b000_0000, sub16};
  assign alu_result3 = (adder_in_a3) + (adder_in_b3) + {7'b000_0000, sub8} + {7'b000_0000, carry_out1};

  assign carry_out0 = ~width8 & alu_result0[8];
  assign carry_out1 = ~width8 & alu_result2[8];

  // Concatinate the regular output
  logic[31:0] normal_result;
  assign normal_result = {alu_result3[7:0], alu_result2[7:0], alu_result1[7:0], alu_result0[7:0]};

  // Calulate halving results
  logic[31:0] halving_result;
  assign halving_result = { {alu_result3[8:1]},
                            {alu_result2[8:1]},
                            {alu_result1[8:1]},
                            {alu_result0[8:1]} };

  // Calulate saturating result
  logic[31:0] saturating_result;

  always_comb begin
    unique case (signed_operands_i)
      U8:  saturating_result = { (alu_result3[8] ? SAT_VAL_U8 : alu_result3[7:0]),
                                 (alu_result2[8] ? SAT_VAL_U8 : alu_result2[7:0]),
                                 (alu_result1[8] ? SAT_VAL_U8 : alu_result1[7:0]),
                                 (alu_result0[8] ? SAT_VAL_U8 : alu_result0[7:0]) }; 

      // [8:7] == 10 gives underflow, [8:7] == 01 gives overflow
      S8:  saturating_result = { (alu_result3[8:7] == 2'b10) ? SAT_VAL_S8L : (alu_result3[8:7] == 2'b01 ? SAT_VAL_S8H : alu_result3[7:0]),
                                 (alu_result2[8:7] == 2'b10) ? SAT_VAL_S8L : (alu_result2[8:7] == 2'b01 ? SAT_VAL_S8H : alu_result2[7:0]),
                                 (alu_result1[8:7] == 2'b10) ? SAT_VAL_S8L : (alu_result1[8:7] == 2'b01 ? SAT_VAL_S8H : alu_result1[7:0]),
                                 (alu_result0[8:7] == 2'b10) ? SAT_VAL_S8L : (alu_result0[8:7] == 2'b01 ? SAT_VAL_S8H : alu_result0[7:0]) }; 

      U16: saturating_result = { (alu_result3[8] ? SAT_VAL_U8 : alu_result3[7:0]),
                                 (alu_result3[8] ? SAT_VAL_U8 : alu_result2[7:0]),
                                 (alu_result1[8] ? SAT_VAL_U8 : alu_result1[7:0]),
                                 (alu_result1[8] ? SAT_VAL_U8 : alu_result0[7:0]) };

      // S16, [8:7] == 10 gives underflow, [8:7] == 01 gives overflow
      default: saturating_result = { ((alu_result3[8:7] == 2'b10) ? SAT_VAL_S16L : (alu_result3[8:7] == 2'b01 ? SAT_VAL_S16H : {alu_result3[7:0], alu_result2[7:0]})),
                                     ((alu_result1[8:7] == 2'b10) ? SAT_VAL_S16L : (alu_result1[8:7] == 2'b01 ? SAT_VAL_S16H : {alu_result1[7:0], alu_result0[7:0]})) };
    endcase
  end

  // Adder results mux
  logic[31:0] adder_result;

  always_comb begin
    unique case(operator_i)
      ZPN_URADD16, ZPN_URADD8,
      ZPN_RADD16,  ZPN_RADD8,
      ZPN_URSUB16, ZPN_URSUB8,
      ZPN_RSUB16,  ZPN_RSUB8:   adder_result = halving_result;

      ZPN_UKADD16, ZPN_UKADD8,
      ZPN_KADD16,  ZPN_KADD8,
      ZPN_UKSUB16, ZPN_UKSUB8,
      ZPN_KSUB16,  ZPN_KSUB8:   adder_result = saturating_result;

      default:                  adder_result = normal_result;
    endcase 
  end


  ////////////////
  // Multiplier //
  ////////////////
  // Im afraid



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

    // TODO: Verify this actually works
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


  // TODO: Clip, abs, cls function...
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
  // TODO CHange to 2 16 bit and 2 8 bit in total, calculating in paralell...
  // Using 2 16-bit shifters. to shift both halfwords right
  // then 2 8-bit shifters to conditionally shift byte 2 and 0 right 
  // then 2 8-bit shifters to conditionally shift byte 2 and 0 back left

  // TODO: Decide if this should be moved to decoder
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
    assign operand_a_rev[i] = operand_a_i[31-i];    // TODO: Check if we need bytewise og wordwise reversing
  end

  // Prepare operands
  logic[15:0]   shift_operand0, shift_operand1;
  logic[3:0]    shift_amt;

  assign shift_operand0 = shift_left ? operand_a_rev[15:0]  : operand_a_i[15:0];
  assign shift_operand1 = shift_left ? operand_a_rev[31:16] : operand_a_i[31:16];
  assign shift_amt      = operand_b_i[3:0];
  
  // First shifter
  logic[16:0]   shift_result_first0, shift_result_first1;
  logic         unused_shift_result_first0, unused_shift_result_first1; 
  
  assign shift_result_first0 = $signed({ (shift_arith & shift_operand0[15]), shift_operand0}) >>> shift_amt;
  assign shift_result_first1 = $signed({ (shift_arith & shift_operand1[15]), shift_operand1}) >>> shift_amt;
  assign unused_shift_result_first0 = shift_result_first0[16];
  assign unused_shift_result_first1 = shift_result_first1[16];


  // TODO: Clean up signal names!!!
  // Second and third conditional shifter 
  logic[7:0]    shift_result_second0, shift_result_second2;   // Only need to do this for byte 2 and 0
  logic[8:0]    shift_result_third0, shift_result_third2;   // Only need to do this for byte 2 and 0
  logic         unused_shift_result_third0, unused_shift_result_third2;
  
  assign shift_result_second0 = shift_result_first0[7:0] << shift_amt[2:0];
  assign shift_result_second2 = shift_result_first1[7:0] << shift_amt[2:0];
  assign shift_result_third0  = $signed({ (shift_arith & shift_result_second0[7]), shift_result_second0}) >>> shift_amt[2:0];
  assign shift_result_third2  = $signed({ (shift_arith & shift_result_second2[7]), shift_result_second2}) >>> shift_amt[2:0];
  assign unused_shift_result_third0 = shift_result_third0[8];
  assign unused_shift_result_third2 = shift_result_third2[8];

  // Concatinate result
  logic[31:0] shift_result_full;
  always_comb begin
    unique case (signed_operands_i)   // TODO: This methodology migth be sub-optimal
      S8, U8 :  shift_result_full = {shift_result_first1[15:8], shift_result_third2[7:0], shift_result_first0[15:8], shift_result_third0[7:0]};
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

  ////////////////
  // Some other stuff... //
  ////////////////

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
        /*ZPN_SUB64,  */  ZPN_SUB16,    ZPN_SUB8: result_o = adder_result;

        // Mult ops
        /*ZPN_SMUL16,   ZPN_SMUL8,
        ZPN_SMULX16,  ZPN_SMULX8,
        ZPN_UMUL16,   ZPN_UMUL8,
        ZPN_UMULX16,  ZPN_UMULX8,
        ZPN_KHM16,    ZPN_KHM8,
        ZPN_KHMX16,   ZPN_KHMX8:    result_o = // TODO*/

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

        // Shift ops      // Omitting rounding shifts for now
        ZPN_SRA16,    ZPN_SRA8,
        ZPN_SRAI16,   ZPN_SRAI8,
        ZPN_SRL16,    ZPN_SRL8,
        ZPN_SRLI16,   ZPN_SRLI8,
        ZPN_SLL16,    ZPN_SLL8,
        ZPN_SLLI16,   ZPN_SLLI8: result_o = shift_result;
      //ZPN_KSLL16,   ZPN_KSLL8,
      //ZPN_KSLLI16,  ZPN_KSLLI8,
      //ZPN_KSLRA16,  ZPN_KSLRA8:    // These seems tricky to implement

        // Unpack ops
        ZPN_SUNPKD810, ZPN_ZUNPKD810,
        ZPN_SUNPKD820, ZPN_ZUNPKD820,
        ZPN_SUNPKD830, ZPN_ZUNPKD830,
        ZPN_SUNPKD831, ZPN_ZUNPKD831,
        ZPN_SUNPKD832, ZPN_ZUNPKD832: result_o = unpack_result;

        default: ;
      endcase
    end
  end

endmodule
