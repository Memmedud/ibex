// Copyright lowRISC contributors.
// Copyright 2018 ETH Zurich and University of Bologna, see also CREDITS.md.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

/*
 * Special Arithmetic logic unit for P-ext instructions
 *  -> Enabling P-extension will disable B-extension and use Zbpbo instead    // TODO: Add Zbpbo extension
 */
module ibex_alu_pext #(
  parameter SAT_VAL_U8    = 8'hff,          // 255
  parameter SAT_VAL_S8L   = 8'h80,          // -128
  parameter SAT_VAL_S8H   = 8'h7f,          // 127
  parameter SAT_VAL_S16L  = 16'h8000,       // -32768
  parameter SAT_VAL_S16H  = 16'h7fff,       // 32767
  parameter SAT_VAL_S32L  = 32'h8000_0000,  // -2147483648
  parameter SAT_VAL_S32H  = 32'h7fff_ffff   // 2147483647
) (
  input  logic                          clk_i,
  input  logic                          rst_ni,

  input  ibex_pkg_pext::zpn_op_e        zpn_operator_i,
  input  ibex_pkg::alu_op_e             alu_operator_i,
  input  ibex_pkg::md_op_e              multdiv_operator_i,

  input  logic                          multdiv_sel_i,
  input  logic                          mult_en_i,      // TODO: Make sure this is set for zpn mults as well
  input  logic                          div_en_i,
  input  logic                          mult_sel_i,
  input  logic                          div_sel_i,
  input  logic [1:0]                    signed_mode_i,
  input  logic                          multdiv_ready_id_i,
  input  logic                          data_ind_timing_i,

  input  logic [33:0]                   imd_val_q_i[2],
  output logic [33:0]                   imd_val_d_o[2],
  output logic [1:0]                    imd_val_we_o,

  input  logic [31:0]                   operand_a_i,
  input  logic [31:0]                   operand_b_i,
  input  logic [31:0]                   operand_rd_i,       // Only used for MULT and INSB

  input  logic [4:0]                    imm_val_i,

  output logic [31:0]                   adder_result_o,

  output logic [31:0]                   result_o,
  output logic                          valid_o,            // All ALU ops are single cycle, only used for Mults
  output logic                          set_ov_o,
  output logic                          comparison_result_o
);
  import ibex_pkg_pext::*;
  import ibex_pkg::*;

  // Common signals and logic
  // Use alu for multdiv operations as well
  logic[32:0] multdiv_operand_a, multdiv_operand_b;
  logic[31:0] adder_operand_a, adder_operand_b;

  assign adder_operand_a = multdiv_sel_i ? multdiv_operand_a[31:0] : operand_a_i; 
  assign adder_operand_b = multdiv_sel_i ? multdiv_operand_b[31:0] : operand_b_i; 

  // TODO
  logic[1:0] unused_operand;
  assign unused_operand = {multdiv_operand_a[32], multdiv_operand_b[32]};

  ////////////////////
  // Decoder helper //
  ////////////////////
  logic[1:0] sub;
  logic zpn_instr, imm_instr, width32, width8, signed_ops;
  
  ibex_alu_pext_helper alu_pext_helper (
    .zpn_operator_i     (zpn_operator_i),
    .alu_operator_i     (alu_operator_i),
    .zpn_instr_o        (zpn_instr),
    .imm_instr_o        (imm_instr),
    .width32_o          (width32),
    .width8_o           (width8),
    .signed_ops_o       (signed_ops),
    .alu_sub_o          (sub)
  );


  ///////////
  // Adder //
  ///////////

  // Decode cross Add/Sub
  logic crossed;
  always_comb begin
    unique case(zpn_operator_i)
      ZPN_RCRAS16,  ZPN_RCRSA16, 
      ZPN_KCRAS16,  ZPN_KCRSA16,
      ZPN_URCRAS16, ZPN_URCRSA16, 
      ZPN_UKCRAS16, ZPN_UKCRSA16,
      ZPN_CRAS16,   ZPN_CRSA16: crossed = zpn_instr;

      default: crossed = 1'b0;
    endcase
  end

  // Decode Halfs
  logic halved;
  always_comb begin
    unique case(zpn_operator_i)
      ZPN_KADDH, ZPN_UKADDH,      // TODO: Check out sign-extension for signed
      ZPN_KSUBH, ZPN_UKSUBH: halved = zpn_instr;

      default: halved = 1'b0;
    endcase
  end

  // Decode if we only use A_in
  logic oneop;
  always_comb begin
    unique case(zpn_operator_i)
      ZPN_KABS16, ZPN_KABS8,
      ZPN_KABSW: oneop = zpn_instr;

      default: oneop = 1'b0;
    endcase
  end

  // Decode if op is using rounding
  logic rounding;
  always_comb begin
    unique case (zpn_operator_i)
      ZPN_AVE/*,
      ZPN_SCLIP16,  ZPN_SCLIP8,
      ZPN_SCLIP32,  ZPN_UCLIP32*/: rounding = zpn_instr;

      default: rounding = 1'b0;
    endcase
  end

  // Prepare operands
  logic       sub8, sub16, sub32;
  logic[7:0]  adder_in_a0, adder_in_a1, adder_in_a2, adder_in_a3,
              adder_tmp_b0, adder_tmp_b1, adder_tmp_b2, adder_tmp_b3,
              adder_in_b0, adder_in_b1, adder_in_b2, adder_in_b3;

  assign sub8  = sub[0] &  width8;   // For 8-bit we assume no combined add/sub
  assign sub16 = sub[1] & ~width32;   // For 32-bit we assume add/sub cannot occur
  assign sub32 = sub[0];

  assign adder_in_a0 = adder_operand_a[7:0]   & {8{~oneop}};
  assign adder_in_a1 = adder_operand_a[15:8]  & {8{~oneop}};
  assign adder_in_a2 = adder_operand_a[23:16] & {8{~oneop | ~halved}};    // TODO fix for signed halved
  assign adder_in_a3 = adder_operand_a[31:24] & {8{~oneop | ~halved}};

  assign adder_tmp_b0 = crossed ? adder_operand_b[23:16] : adder_operand_b[7:0];
  assign adder_tmp_b1 = crossed ? adder_operand_b[31:24] : adder_operand_b[15:8];
  assign adder_tmp_b2 = crossed ? adder_operand_b[7:0]   : adder_operand_b[23:16];
  assign adder_tmp_b3 = crossed ? adder_operand_b[15:8]  : adder_operand_b[31:24];

  assign adder_in_b0 = (sub[0] ? (oneop ? ~adder_operand_a[7:0]   : ~adder_tmp_b0) : adder_tmp_b0);
  assign adder_in_b1 = (sub[0] ? (oneop ? ~adder_operand_a[15:8]  : ~adder_tmp_b1) : adder_tmp_b1);
  assign adder_in_b2 = (sub[1] ? (oneop ? ~adder_operand_a[23:16] : ~adder_tmp_b2) : adder_tmp_b2) & {8{~halved}};
  assign adder_in_b3 = (sub[1] ? (oneop ? ~adder_operand_a[31:24] : ~adder_tmp_b3) : adder_tmp_b3) & {8{~halved}};

  // Actual adder
  logic[8:0]  adder_result0, adder_result1, adder_result2, adder_result3;
  logic       carry_out0, carry_out1, carry_out2;

  assign adder_result0 = adder_in_a0 + adder_in_b0 + {7'b000_0000, (sub32 | rounding)};
  assign adder_result1 = adder_in_a1 + adder_in_b1 + {7'b000_0000,  sub8}  + {7'b000_0000, carry_out0};
  assign adder_result2 = adder_in_a2 + adder_in_b2 + {7'b000_0000,  sub16} + {7'b000_0000, carry_out1};
  assign adder_result3 = adder_in_a3 + adder_in_b3 + {7'b000_0000,  sub8}  + {7'b000_0000, carry_out2};

  assign carry_out0 = ~width8  & adder_result0[8];
  assign carry_out1 =  width32 & adder_result1[8];
  assign carry_out2 = ~width8  & adder_result2[8];

  // Concatinate the regular output
  logic[31:0] normal_result;
  assign normal_result = {adder_result3[7:0], adder_result2[7:0], adder_result1[7:0], adder_result0[7:0]};

  // Calulate halving results
  logic[31:0] halving_result;
  always_comb begin
    unique case ({signed_ops, width32, width8})

      3'b001 : halving_result = { adder_result3[8:1], 
                                  adder_result2[8:1], 
                                  adder_result1[8:1], 
                                  adder_result0[8:1] };

      3'b101 : halving_result = { adder_result3[7],   adder_result3[7:1], 
                                  adder_result2[7],   adder_result2[7:1], 
                                  adder_result1[7],   adder_result1[7:1], 
                                  adder_result0[7],   adder_result0[7:1] };
                                  
      3'b100 : halving_result = { adder_result3[7],   adder_result3[7:0], adder_result2[7:1], 
                                  adder_result1[7],   adder_result1[7:0], adder_result0[7:1] };

      3'b010 : halving_result = { adder_result3[8:0], adder_result2[7:0], adder_result1[7:0], adder_result0[7:1]};

      3'b110 : halving_result = { adder_result3[7],   adder_result3[7:0], adder_result2[7:0], adder_result1[7:0], adder_result0[7:1]};
      
      default: halving_result = { adder_result3[8:0], adder_result2[7:1], 
                                  adder_result1[8:0], adder_result0[7:1] };
    endcase
  end

  // Decode saturation state
  logic[3:0]  saturated;      // [8:7] == 10 gives underflow, [8:7] == 01 gives overflow
  logic       alu_set_ov;
  assign alu_set_ov = |saturated;   
  assign saturated = { ((adder_in_a3[7] ^ adder_tmp_b3[7]) ^ ~sub[1]) & (^adder_result3[8:7]), 
                       ((adder_in_a2[7] ^ adder_tmp_b2[7]) ^ ~sub[1]) & (^adder_result2[8:7]), 
                       ((adder_in_a1[7] ^ adder_tmp_b1[7]) ^ ~sub[0]) & (^adder_result1[8:7]), 
                       ((adder_in_a0[7] ^ adder_tmp_b0[7]) ^ ~sub[0]) & (^adder_result0[8:7]) };
  
  // Calulate saturating result
  logic[31:0] saturating_result;
  always_comb begin
    unique case ({signed_ops, width32, width8})

      3'b101 :  saturating_result = { saturated[3] ? (adder_result3[8] ? SAT_VAL_S8L : SAT_VAL_S8H) : adder_result3[7:0], 
                                      saturated[2] ? (adder_result2[8] ? SAT_VAL_S8L : SAT_VAL_S8H) : adder_result2[7:0],
                                      saturated[1] ? (adder_result1[8] ? SAT_VAL_S8L : SAT_VAL_S8H) : adder_result1[7:0],
                                      saturated[0] ? (adder_result0[8] ? SAT_VAL_S8L : SAT_VAL_S8H) : adder_result0[7:0] }; 
 
      3'b100 : saturating_result  = { saturated[3] ? (adder_result3[8] ? SAT_VAL_S16L : SAT_VAL_S16H) : {adder_result3[7:0], adder_result2[7:0]},
                                      saturated[1] ? (adder_result1[8] ? SAT_VAL_S16L : SAT_VAL_S16H) : {adder_result1[7:0], adder_result0[7:0]} };

      3'b110 : saturating_result  = { saturated[3] ? (adder_result3[8] ? SAT_VAL_S32L : SAT_VAL_S32H) : {adder_result3[7:0], adder_result2[7:0], adder_result1[7:0], adder_result0[7:0]}};
      
      3'b001 :  saturating_result = { (adder_result3[8] ^ sub[1] ? (sub[1] ? 8'b0 : SAT_VAL_U8) : adder_result3[7:0]),
                                      (adder_result2[8] ^ sub[1] ? (sub[1] ? 8'b0 : SAT_VAL_U8) : adder_result2[7:0]),
                                      (adder_result1[8] ^ sub[0] ? (sub[0] ? 8'b0 : SAT_VAL_U8) : adder_result1[7:0]),
                                      (adder_result0[8] ^ sub[0] ? (sub[0] ? 8'b0 : SAT_VAL_U8) : adder_result0[7:0]) }; 

      3'b010 : saturating_result  = { (adder_result3[8] ^ sub[1] ? (sub[1] ? 8'b0 : SAT_VAL_U8) : adder_result3[7:0]),
                                      (adder_result3[8] ^ sub[1] ? (sub[1] ? 8'b0 : SAT_VAL_U8) : adder_result2[7:0]),
                                      (adder_result3[8] ^ sub[1] ? (sub[1] ? 8'b0 : SAT_VAL_U8) : adder_result1[7:0]),
                                      (adder_result3[8] ^ sub[1] ? (sub[1] ? 8'b0 : SAT_VAL_U8) : adder_result0[7:0]) };

      default: saturating_result  = { (adder_result3[8] ^ sub[1] ? (sub[1] ? 8'b0 : SAT_VAL_U8) : adder_result3[7:0]),
                                      (adder_result3[8] ^ sub[1] ? (sub[1] ? 8'b0 : SAT_VAL_U8) : adder_result2[7:0]),
                                      (adder_result1[8] ^ sub[0] ? (sub[0] ? 8'b0 : SAT_VAL_U8) : adder_result1[7:0]),
                                      (adder_result1[8] ^ sub[0] ? (sub[0] ? 8'b0 : SAT_VAL_U8) : adder_result0[7:0]) };
    endcase
  end

  // Adder results mux
  logic[31:0] adder_result;
  logic[33:0] adder_result_ext;
  always_comb begin
    unique case(alu_operator_i)
      ZPN_INSTR: begin
        unique case(zpn_operator_i)   
          ZPN_AVE,    // TODO add rounding ops to halving...
          ZPN_RADDW,    ZPN_URADDW,
          ZPN_RSUBW,    ZPN_URSUBW,
          ZPN_URCRAS16, ZPN_URCRSA16,
          ZPN_RCRAS16,  ZPN_RCRSA16,
          ZPN_URSTAS16, ZPN_URSTSA16,
          ZPN_RSTAS16,  ZPN_RSTSA16,
          ZPN_URADD16,  ZPN_URADD8,
          ZPN_RADD16,   ZPN_RADD8,
          ZPN_URSUB16,  ZPN_URSUB8,
          ZPN_RSUB16,   ZPN_RSUB8: adder_result = halving_result;

          ZPN_KADDW,    ZPN_UKADDW,   // TODO: Add Saturating shifts here
          ZPN_KADDH,    ZPN_UKADDH,
          ZPN_KSUBW,    ZPN_UKSUBW,
          ZPN_KSUBH,    ZPN_UKSUBH,
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

      default: adder_result = normal_result;
    endcase

    adder_result_ext = {adder_result3[8], normal_result, 1'b1};
    adder_result_o   = normal_result;

  end


  ////////////////
  // Multiplier //
  ////////////////
  logic[31:0] multdiv_result;
  logic multdiv_valid, multdiv_set_ov;
  logic is_equal_result;

  ibex_mult_pext mult_pext_i (
    .clk_i                (clk_i),
    .rst_ni               (rst_ni),
    .mult_en_i            (mult_en_i),
    .div_en_i             (div_en_i),
    .mult_sel_i           (mult_sel_i),
    .div_sel_i            (div_sel_i),
    .zpn_operator_i       (zpn_operator_i),
    .alu_operator_i       (alu_operator_i),
    .zpn_instr_i          (zpn_instr),
    .signed_mode_i        (signed_mode_i),
    .md_operator_i        (multdiv_operator_i),
    .op_a_i               (operand_a_i),
    .op_b_i               (operand_b_i),
    .rd_val_i             (operand_rd_i),
    .alu_adder_ext_i      (adder_result_ext),
    .alu_adder_i          (adder_result_o),
    .equal_to_zero_i      (is_equal_result),
    .data_ind_timing_i    (data_ind_timing_i),
    .alu_operand_a_o      (multdiv_operand_a),
    .alu_operand_b_o      (multdiv_operand_b),
    .imd_val_q_i          (imd_val_q_i),
    .imd_val_d_o          (imd_val_d_o),
    .imd_val_we_o         (imd_val_we_o),
    .multdiv_ready_id_i   (multdiv_ready_id_i),
    .multdiv_result_o     (multdiv_result),
    .valid_o              (multdiv_valid),
    .set_ov_o             (multdiv_set_ov)
  );


  ////////////////
  // Comparison //
  ////////////////
  logic[3:0]    is_byte_equal, is_equal;   // One bit for each byte
  logic[3:0]    is_byte_less,  is_less;    // handles both signed and unsigned forms

  // calculate is_equal
  always_comb begin
    is_byte_equal = 4'b0000;

    // Decoding is done in the adder
    for (int unsigned b = 0; b < 4; b++) if (adder_result[8*b +: 8] == 8'h00) begin
      is_byte_equal[b] = 1'b1;
    end

    unique case ({width32, width8})
      2'b10  : is_equal = {{4{&is_byte_equal}}};
      2'b01  : is_equal = is_byte_equal;
      default: is_equal = {{2{&is_byte_equal[3:2]}}, {2{&is_byte_equal[1:0]}}};
    endcase

    is_equal_result = ~zpn_instr & is_equal[0];
  end

  // Calculate is_less
  always_comb begin   // TODO: Support 32-bit cmp
    is_byte_less = 4'b0000;
    
    for (int unsigned b = 0; b < 4; b++) begin
      if ((operand_a_i[8*b+7] ^ operand_b_i[8*b+7]) == 1'b0) begin
        is_byte_less[b] = (adder_result[8*b+7] == 1'b1);
      end
      else begin
        is_byte_less[b] = ~(operand_a_i[8*b+7] ^ (signed_ops)); // TODO: remember alu thingies for signed ops...
      end
    end

    unique case (width8)
      1'b0: is_less = {is_byte_less[3], is_byte_less[3], is_byte_less[1], is_byte_less[1]}; // Fix this as well
      1'b1: is_less = is_byte_less;   // TODO: Fix this for 32 bit
    endcase
  end

  // Comparator result mux
  logic[3:0]    comp_result_packed;

  always_comb begin
    unique case (alu_operator_i)
      ZPN_INSTR: begin
        unique case (zpn_operator_i)
          // Less than
          ZPN_SMIN16,   ZPN_SMIN8,
          ZPN_UMIN16,   ZPN_UMIN8,
          ZPN_SCMPLT16, ZPN_SCMPLT8,
          ZPN_UCMPLT16, ZPN_UCMPLT8: comp_result_packed = is_less;

          // Less than or equal
          ZPN_SCMPLE16, ZPN_SCMPLE8,
          ZPN_UCMPLE16, ZPN_UCMPLE8: comp_result_packed = is_equal | is_less;

          // Greater than, only used for max
          ZPN_SMAX16,   ZPN_SMAX8,
          ZPN_UMAX16,   ZPN_UMAX8: comp_result_packed = ~(is_equal | is_less);
          
          // Including is equal
          default: comp_result_packed = is_equal;
        endcase
      end

      ALU_EQ: comp_result_packed =  is_equal;

      ALU_NE: comp_result_packed = ~is_equal;

      ALU_GE,   ALU_GEU,
      ALU_MAX,  ALU_MAXU: comp_result_packed = ~is_less;
      
      ALU_LT,   ALU_LTU,
      ALU_MIN,  ALU_MINU,
      ALU_SLT,  ALU_SLTU: comp_result_packed = is_less;
      
      default: comp_result_packed = '0;
    endcase
  end

  // Widen output from bitwise to bytewise
  logic[31:0]   comp_result;      // TODO fix for noext
  assign comp_result = { {8{comp_result_packed[3]}},
                         {8{comp_result_packed[2]}},
                         {8{comp_result_packed[1]}},
                         {8{comp_result_packed[0]}} };    // TODO Make to for loop

  assign comparison_result_o = ~zpn_instr & comp_result_packed[0];


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


  /////////
  // ABS //
  /////////
  logic[31:0]   abs_result;
  logic[3:0]    abs_negative;

  always_comb begin
    unique case ({width32, width8})
      2'b10  : abs_negative = {4{operand_a_i[31]}};
      2'b01  : abs_negative = {operand_a_i[31], operand_a_i[23], operand_a_i[15], operand_a_i[7]};
      default: abs_negative = {{2{operand_a_i[31]}}, {2{operand_a_i[15]}}};
    endcase
  end

  // TODO: Add check for 80, 8000, 8000_0000

  for (genvar b = 0; b < 4; b++) begin : gen_abs_result
    assign abs_result[8*b +: 8] = abs_negative[b] ? normal_result[8*b +: 8] : operand_a_i[8*b +: 8];
  end


  ////////////////
  // Bit-shifts //
  ////////////////

  // Generate shift mask with inverse, reverse thermometer coding (only 16-bit since we will only need it for halfword and byte)
  // Will use this mask for both Shift and clip instructions
  // Ex: shift_amt=4 -> mask = 0000_1111_1111_1111

  logic shift_signed;
  assign shift_signed = (alu_operator_i == ALU_SRA) | signed_ops; 

  // bit-reverse operand_a for left shifts
  logic[31:0] shift_operand_rev;
  for (genvar i = 0; i < 32; i++) begin : gen_rev_operand
    assign shift_operand_rev[i] = operand_a_i[31-i];
  end

  // Prepare operands   // TODO: Support rounding as well pipe back into adder to add one 
  logic[31:0] shift_operand;
  logic[4:0]  shift_amt_raw, shift_amt;
  assign shift_operand = shift_left  ? shift_operand_rev : operand_a_i;
  assign shift_amt_raw = imm_instr ? imm_val_i : operand_b_i[4:0];
  assign shift_amt     = {(width32 ? shift_amt_raw[4] : 1'b0), (width8 ? 1'b0 : shift_amt_raw[3]), shift_amt_raw[2:0]};

  // Generate shift mask
  logic[3:0]  shift_signed_bytes;
  logic[31:0] shift_mask_base, shift_mask, shift_mask_signed;
  always_comb begin
    for (int unsigned i = 0; i < 32; i++) begin
      if (i < shift_amt) begin
        shift_mask_base[31-i] = 1'b0;
      end
      else begin
        shift_mask_base[31-i] = 1'b1;
      end
    end

    unique case ({width32, width8})
      2'b10  : shift_mask = shift_mask_base;
      2'b01  : shift_mask = {4{shift_mask_base[31:24]}};
      default: shift_mask = {2{shift_mask_base[31:16]}};
    endcase

    unique case ({width32, width8})
      2'b10  : shift_signed_bytes = 4'b0000;   // 32-bit is handled internally in shifter
      2'b01  : shift_signed_bytes = shift_signed ? {1'b0, shift_operand[23], shift_operand[15], shift_operand[7]} : 4'b0000;
      default: shift_signed_bytes = shift_signed ? {2'b00, {2{shift_operand[15]}}} : 4'b0000;
    endcase

    for (int unsigned b = 0; b < 4; b++) begin
      shift_mask_signed[8*b +: 8] = shift_signed_bytes[b] ? ~shift_mask[8*b +: 8] : 8'h0;
    end
  end

  // Decode if we should left-shift (right shifting by default)
  logic shift_left;
  always_comb begin
    unique case (alu_operator_i)
      ZPN_INSTR: begin
        unique case (zpn_operator_i)
          ZPN_SLL16,    ZPN_SLL8,
          ZPN_SLLI16,   ZPN_SLLI8,
          ZPN_SCLIP16,  ZPN_SCLIP8,
          ZPN_SCLIP32,  ZPN_UCLIP32: shift_left = 1'b1;

          default: shift_left = 1'b0;
        endcase
      end

      ALU_SLL: shift_left = 1'b1;

      default: shift_left = 1'b0;
    endcase
  end

  // Actual shifter and mask_application
  logic[32:0] shift_result_raw;
  logic       unused_shift_result;

  assign shift_result_raw = $signed({shift_signed & shift_operand[31], shift_operand}) >>> shift_amt;
  assign unused_shift_result = shift_result_raw[32];

  logic[31:0] shift_result_masked, shift_result_signed;
  assign shift_result_masked = shift_result_raw[31:0] & shift_mask;
  assign shift_result_signed = shift_result_masked | shift_mask_signed;

  // Flip bytes back for Left-shifting
  logic[31:0] shift_result_rev;
  always_comb begin
    for (int unsigned i = 0; i < 32; i++) begin
      shift_result_rev[i] = shift_result_signed[31-i];
    end
  end

  // Produce final shifter output
  logic[31:0] shift_result;
  assign shift_result = shift_left ? shift_result_rev : shift_result_signed;


  //////////
  // CLIP //
  //////////
  // Generate masks and clipped value
  logic[31:0] clip_mask, residual_mask, clip_val;
  for (genvar a = 0; a < 32; a++) begin : gen_rev_operand
    assign residual_mask[a] = shift_mask[31-a];
  end
  assign clip_mask =  ~residual_mask;
  assign clip_val  =  operand_a_i & clip_mask;

  // Detect if the operands are signed
  logic[3:0] operand_negative;
  always_comb begin
    unique case ({width32, width8})
      2'b01  : operand_negative = {operand_a_i[31], operand_a_i[23], operand_a_i[15], operand_a_i[7]} & {4{((~imm_val_i[4] & ~width32) | signed_ops)}};
      2'b10  : operand_negative = {4{operand_a_i[31]}} & {4{((~imm_val_i[4] & ~width32) | signed_ops)}};
      default: operand_negative = {{2{operand_a_i[31]}}, {2{operand_a_i[15]}}} & {4{((~imm_val_i[4] & ~width32) | signed_ops)}};
    endcase
  end

  // Detect if saturation is occuring
  logic[3:0] clrs_res;
  assign clrs_res = { (bit_cnt_result[27:24] <= {1'b0, ~shift_amt[2:0]}), 
                      (bit_cnt_result[20:16] <= {1'b0, ~shift_amt[3:0]}),
                      (bit_cnt_result[11:8]  <= {1'b0, ~shift_amt[2:0]}), 
                      (bit_cnt_result[5:0]   <= {1'b0, ~shift_amt[4:0]}) };

  logic[3:0] clip_saturation;
  always_comb begin
    unique case({width32, width8})
      2'b01  : clip_saturation = clrs_res;
      2'b10  : clip_saturation = {4{clrs_res[0]}};
      default: clip_saturation = {{2{clrs_res[2]}}, {2{clrs_res[0]}}};
    endcase
  end

  // Generate the residual value
  logic[31:0] residual_val, residual_result;
  assign residual_val = { {8{operand_negative[3]}}, {8{operand_negative[2]}}, {8{operand_negative[1]}}, {8{operand_negative[0]}}};
  assign residual_result = residual_val & residual_mask;

  // Gerenate the clipped value
  logic[31:0] clip_val_result;
  assign clip_val_result = {clip_saturation[3] ? (clip_mask[31:24] & {8{~operand_negative[3]}}) : clip_val[31:24],
                            clip_saturation[2] ? (clip_mask[23:16] & {8{~operand_negative[2]}}) : clip_val[23:16],
                            clip_saturation[1] ? (clip_mask[15:8]  & {8{~operand_negative[1]}}) : clip_val[15:8] ,
                            clip_saturation[0] ? (clip_mask[7:0]   & {8{~operand_negative[0]}}) : clip_val[7:0]   };

  // Generate final clipped result
  logic[31:0] clip_result;
  assign clip_result = residual_result | clip_val_result;


  //////////////////
  // Bit-counting //
  //////////////////
  // Prepare operand
  logic[3:0] negate;
  always_comb begin
    unique case({signed_ops, width32, width8})
      3'b101 : negate = {~operand_a_i[31], ~operand_a_i[24], ~operand_a_i[15], ~operand_a_i[7]};
      3'b100 : negate = {{2{~operand_a_i[31]}}, {2{~operand_a_i[15]}}};
      3'b110 : negate = {{4{~operand_a_i[31]}}};
      default: negate = 4'b1111;
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

  assign bc15 = ~width32 ? (negate[1] ? ~operand_a_i[15] : operand_a_i[15]) : (negate[2] ? (~operand_a_i[15] & bc16) : (operand_a_i[15] & bc16));
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

  // Bit counter is a 5-layer deep Brent-Kung Adder
  // First Adder layer
  logic[31:0] bit_cnt_first_layer;  // We get 16 2-bit results
  for (genvar i = 0; i < 16; i++) begin : gen_bit_cnt_adder1
    assign bit_cnt_first_layer[2*i+1 : 2*i] = bit_cnt_operand[2*i] + bit_cnt_operand[2*i + 1];
  end

  // Second adder layer
  logic[23:0] bit_cnt_second_layer; // And 8 3-bit results
  for (genvar i = 0; i < 8; i++) begin : gen_bit_cnt_adder2
    assign bit_cnt_second_layer[3*i +: 3] = bit_cnt_first_layer[4*i+1 : 4*i] + bit_cnt_first_layer[4*i+3 : 4*i+2];
  end

  // Third adder layer
  logic[15:0] bit_cnt_third_layer;  // And 4 4-bit results
  for (genvar i = 0; i < 4; i++) begin : gen_bit_cnt_adder3
    assign bit_cnt_third_layer[4*i +: 4] = bit_cnt_second_layer[6*i+2 : 6*i] + bit_cnt_second_layer[6*i+5 : 6*i+3];
  end

  // Fourth adder layer
  logic[9:0] bit_cnt_fourth_layer;  // And 2 5-bit results
  assign bit_cnt_fourth_layer[4:0] = {1'b0, bit_cnt_third_layer[3:0]}  + {1'b0, bit_cnt_third_layer[7:4]};
  assign bit_cnt_fourth_layer[9:5] = {1'b0, bit_cnt_third_layer[11:8]} + {1'b0, bit_cnt_third_layer[15:12]};

  // Fifth adder layer for 32-bit results
  logic[31:0] bit_cnt_result_width32;
  assign bit_cnt_result_width32 = {26'h0, {1'b0, bit_cnt_fourth_layer[4:0]} + {1'b0, bit_cnt_fourth_layer[9:5]}};

  // Concatinate partial results
  logic[31:0] bit_cnt_result_width8, bit_cnt_result_width16;
  assign bit_cnt_result_width8 = {4'h0, bit_cnt_third_layer[15:12], 4'h0, bit_cnt_third_layer[11:8], 
                                  4'h0, bit_cnt_third_layer[7:4]  , 4'h0, bit_cnt_third_layer[3:0]  };

  assign bit_cnt_result_width16 = {11'h0, bit_cnt_fourth_layer[9:5], 11'h0, bit_cnt_fourth_layer[4:0] };

  // Bit-count result mux
  logic[31:0] bit_cnt_result;
  always_comb begin
    unique case ({width32, width8})
      2'b10  : bit_cnt_result = bit_cnt_result_width32;
      2'b01  : bit_cnt_result = bit_cnt_result_width8;
      default: bit_cnt_result = bit_cnt_result_width16;
    endcase
  end

  
  ///////////////////
  // Bitwise Logic //
  ///////////////////
  logic[31:0] bw_or_result, bw_and_result, bw_xor_result, bw_result;

  assign bw_or_result  = operand_a_i | operand_b_i;
  assign bw_and_result = operand_a_i & operand_b_i;
  assign bw_xor_result = operand_a_i ^ operand_b_i;

  always_comb begin
    unique case (alu_operator_i)
      ALU_OR : bw_result = bw_or_result;
      ALU_AND: bw_result = bw_and_result;
      default: bw_result = bw_xor_result;
    endcase
  end


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

    unique case (zpn_operator_i)
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

  always_comb begin
    packing_result = '0;

    unique case(alu_operator_i)
      ALU_PACKU: packing_result = {operand_b_i[31:16], operand_a_i[31:16]};
      ALU_PACKH: packing_result = {16'h0, operand_b_i[7:0], operand_a_i[7:0]};
      default  : packing_result = {operand_b_i[15:0],  operand_a_i[15:0]};
    endcase

    unique case (zpn_operator_i)
      ZPN_PKBB16: packing_result = {operand_a_i[15:0],  operand_b_i[15:0]};
      ZPN_PKBT16: packing_result = {operand_a_i[15:0],  operand_b_i[31:16]};
      ZPN_PKTB16: packing_result = {operand_a_i[31:16], operand_b_i[15:0]};
      ZPN_PKTT16: packing_result = {operand_a_i[31:16], operand_b_i[31:16]};
      default: ;
    endcase
  end


  /////////////////
  // Insert Byte //
  /////////////////
  logic[31:0]   insb_result;
  logic[7:0]    insb_byte;

  assign insb_byte = operand_a_i[7:0];

  always_comb begin
    insb_result = '0;
    unique case (zpn_operator_i)
      ZPN_INSB0: insb_result = {operand_rd_i[31:8], insb_byte};
      ZPN_INSB1: insb_result = {operand_rd_i[31:16], insb_byte, operand_rd_i[7:0]};
      ZPN_INSB2: insb_result = {operand_rd_i[31:24], insb_byte, operand_rd_i[15:0]};
      ZPN_INSB3: insb_result = {insb_byte, operand_rd_i[23:0]};
      default: ;
    endcase
  end


  ////////////////////
  // Zpn Result mux //
  ////////////////////
  logic[31:0] zpn_result;
  always_comb begin
    unique case (zpn_operator_i)
      // Adder operation
      // Misc   // TODO: Add rounding ops here
      ZPN_AVE,
      // Add ops
      ZPN_KADDW,    ZPN_KADDH,
      ZPN_UKADDW,   ZPN_UKADDH,
      ZPN_RADDW,    ZPN_URADDW,
      ZPN_RADD16,   ZPN_RADD8,
      ZPN_KADD16,   ZPN_KADD8,
      ZPN_URADD16,  ZPN_URADD8,
      ZPN_UKADD16,  ZPN_UKADD8,
      ZPN_ADD16,    ZPN_ADD8,
      // Sub ops
      ZPN_KSUBW,    ZPN_KSUBH,
      ZPN_UKSUBW,   ZPN_UKSUBH,
      ZPN_RSUBW,    ZPN_URSUBW,
      ZPN_RSUB16,   ZPN_RSUB8,
      ZPN_KSUB16,   ZPN_KSUB8,
      ZPN_URSUB16,  ZPN_URSUB8,
      ZPN_UKSUB16,  ZPN_UKSUB8,
      ZPN_SUB16,    ZPN_SUB8,
      // Cross Add/Sub ops
      ZPN_RCRAS16,  ZPN_RCRSA16,
      ZPN_KCRAS16,  ZPN_KCRSA16,
      ZPN_URCRAS16, ZPN_URCRSA16,
      ZPN_UKCRAS16, ZPN_UKCRSA16,
      ZPN_CRAS16,   ZPN_CRSA16,
      // Straight Add/Sub ops
      ZPN_RSTAS16,  ZPN_RSTSA16,
      ZPN_KSTAS16,  ZPN_KSTSA16,
      ZPN_URSTAS16, ZPN_URSTSA16,
      ZPN_UKSTAS16, ZPN_UKSTSA16,
      ZPN_STAS16,   ZPN_STSA16,
      // Accumulating Mult ops that use ALU adder
      ZPN_KMMAC,    ZPN_KMMACu,     // TODO: make these work
      ZPN_KMMSB,    ZPN_KMMSBu,
      ZPN_KMMAWB,   ZPN_KMMAWBu,
      ZPN_KMMAWT,   ZPN_KMMAWTu,
      ZPN_KMMAWB2,  ZPN_KMMAWB2u,
      ZPN_KMMAWT2,  ZPN_KMMAWT2u: zpn_result = adder_result;
      
      // SIMD multiplication ops
      // 8x8       32x32         32x16          16x16      
      /*ZPN_SMAQA,   ZPN_SMMUL,    ZPN_SMMWB,     ZPN_SMBB16,
      ZPN_UMAQA,   ZPN_SMMULu,   ZPN_SMMWBu,    ZPN_SMBT16,
      ZPN_SMAQAsu, ZPN_KMMAC,    ZPN_SMMWT,     ZPN_SMTT16,
      ZPN_KHM8,    ZPN_KMMACu,   ZPN_SMMWTu,    ZPN_KMDA,  
      ZPN_KHMX8,   ZPN_KMMSB,    ZPN_KMMAWB,    ZPN_KMXDA, 
                    ZPN_KMMSBu,  ZPN_KMMAWBu,   ZPN_SMDS,
                    ZPN_KWMMUL,  ZPN_KMMAWT,    ZPN_SMDRS,
                    ZPN_KWMMULu, ZPN_KMMAWTu,   ZPN_SMXDS,
                    ZPN_MADDR32, ZPN_KMMWB2,    ZPN_KMABB,
                    ZPN_MSUBR32, ZPN_KMMWB2u,   ZPN_KMABT,
                                 ZPN_KMMWT2,    ZPN_KMATT,
                                 ZPN_KMMWT2u,   ZPN_KMADA,
                                 ZPN_KMMAWB2,   ZPN_KMAXDA,
                                 ZPN_KMMAWB2u,  ZPN_KMADS,
                                 ZPN_KMMAWT2,   ZPN_KMADRS,
                                 ZPN_KMMAWT2u,  ZPN_KMAXDS,
                                                ZPN_KMSDA,
                                                ZPN_KMSXDA,
                                                ZPN_KHMBB,
                                                ZPN_KHMBT,
                                                ZPN_KHMTT,
                                                ZPN_KDMBB,
                                                ZPN_KDMBT,
                                                ZPN_KDMTT,
                                                ZPN_KDMABB,
                                                ZPN_KDMABT,
                                                ZPN_KDMATT,
                                                ZPN_KHM16,
                                                ZPN_KHMX16: zpn_result = multdiv_result;*/

      // Comparison ops
      ZPN_CMPEQ16,  ZPN_CMPEQ8,
      ZPN_SCMPLT16, ZPN_SCMPLT8,
      ZPN_SCMPLE16, ZPN_SCMPLE8,
      ZPN_UCMPLT16, ZPN_UCMPLT8,
      ZPN_UCMPLE16, ZPN_UCMPLE8: zpn_result = comp_result;

      // Min/Max ops
      ZPN_SMIN16, ZPN_SMIN8,
      ZPN_SMAX16, ZPN_SMAX8,
      ZPN_UMIN16, ZPN_UMIN8,
      ZPN_UMAX16, ZPN_UMAX8: zpn_result = minmax_result;

      // Abs ops
      ZPN_KABS16, ZPN_KABS8,
      ZPN_KABSW: zpn_result = abs_result;

      // Clip ops
      ZPN_SCLIP32, ZPN_SCLIP16,
      ZPN_UCLIP32, ZPN_SCLIP8: zpn_result = clip_result;

      // Shift ops      // Omitting rounding shifts for now   // KSLRA8.u KSLRA16.u
      ZPN_SRA16,    ZPN_SRA8,
      ZPN_SRAI16,   ZPN_SRAI8,
      ZPN_SRL16,    ZPN_SRL8,
      ZPN_SRLI16,   ZPN_SRLI8,
      ZPN_SLL16,    ZPN_SLL8,
      ZPN_SLLI16,   ZPN_SLLI8,
      ZPN_KSLL16,   ZPN_KSLL8,      // TODO ========================================
      ZPN_KSLLI16,  ZPN_KSLLI8,
      ZPN_KSLRA16,  ZPN_KSLRA8: zpn_result = shift_result;
      
      // Bit-count ops
      ZPN_CLRS16, ZPN_CLRS8, ZPN_CLRS32,
      ZPN_CLZ16,  ZPN_CLZ8: zpn_result = bit_cnt_result;

      // Unpack ops
      ZPN_SUNPKD810, ZPN_ZUNPKD810,
      ZPN_SUNPKD820, ZPN_ZUNPKD820,
      ZPN_SUNPKD830, ZPN_ZUNPKD830,
      ZPN_SUNPKD831, ZPN_ZUNPKD831,
      ZPN_SUNPKD832, ZPN_ZUNPKD832: zpn_result = unpack_result;

      // Packing ops
      ZPN_PKBB16, ZPN_PKBT16,
      ZPN_PKTB16, ZPN_PKTT16: zpn_result = packing_result;

      // Insert Byte ops
      ZPN_INSB0, ZPN_INSB1,
      ZPN_INSB2, ZPN_INSB3: zpn_result = insb_result;

      default: zpn_result = '0;
    endcase
  end


  //////////////////////
  // Final Result mux //
  //////////////////////
  always_comb begin
    unique case(alu_operator_i)
      // Bitwise Logic ops
      ALU_XOR,  ALU_OR,
      ALU_AND: result_o = bw_result;

      // Adder ops (ADD is selected in the ALU when using multdiv ops)
      ALU_ADD,  ALU_SUB: result_o = multdiv_sel_i ? multdiv_result : adder_result;

      // Shift ops
      ALU_SLL,  ALU_SRL,
      ALU_SRA: result_o = shift_result;

      // Comparison ops
      ALU_EQ,   ALU_NE,
      ALU_GE,   ALU_GEU,
      ALU_LT,   ALU_LTU,
      ALU_SLT,  ALU_SLTU: result_o = {31'h0, comp_result[0]};

      // MinMax ops (Zbpbo)
      ALU_MIN,  ALU_MAX,
      ALU_MINU, ALU_MAXU: result_o = minmax_result;// TODO: check out how unsigned is handled here

      // Bitcount ops (Zbpbo)
      ALU_CLZ: result_o = bit_cnt_result;

      // Pack ops (Zbpbo)
      ALU_PACK, ALU_PACKH,
      ALU_PACKU: result_o = packing_result;

      // TODO: Add the rest from Zbpbo
      
      // P-ext ALU output
      ZPN_INSTR:  result_o = zpn_result;

      default: result_o = '0;
    endcase
  end

  // Assign output signals
  assign set_ov_o = (multdiv_sel_i ? multdiv_set_ov : alu_set_ov) & zpn_instr;
  assign valid_o  =  multdiv_sel_i ? multdiv_valid : 1'b1;

endmodule
