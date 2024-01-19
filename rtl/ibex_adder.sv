// Copyright lowRISC contributors.
// Copyright 2018 ETH Zurich and University of Bologna, see also CREDITS.md.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

/**
 * Packed adder for P-extension
 */
module ibex_adder #(
  input  ibex_pkg::alu_op_e     operator_i,
  input  logic [31:0]           adder_in_a_i,
  input  logic [31:0]           adder_in_b_i,

  output logic [31:0]           adder_result_o,
  output logic [33:0]           adder_result_ext_o,
);

  // Adder data width calculation
  ibex_pkg::aluwidth_e alu_width;
  always_comb begin
    unique case(operator_i)
      ZPN_ADD16,    ZPN_UKADD16,
      ZPN_URADD16,  ZPN_KADD16,
      ZPN_RADD16,   ZPN_SUB16,
      ZPN_UKSUB16,  ZPN_URSUB16,
      ZPN_KSUB16,   ZPN_RSUB16: alu_width = WIDTH16;

      ZPN_ADD8,     ZPN_UKADD8,
      ZPN_URADD8,   ZPN_KADD8,
      ZPN_RADD8,    ZPN_SUB8,
      ZPN_UKSUB8,   ZPN_URSUB8,
      ZPN_KSUB8,    ZPN_RSUB8: alu_width = WIDTH8;

      default: alu_width = WIDTH32;
    endcase
  end

  // Overflow type behaviour
  ibex_pkg::aluwidth_e overflow_type;
  always_comb begin
    unique case(operator_i)
      ZPN_UKADD16,  ZPN_KADD16,
      ZPN_UKSUB16,  ZPN_KSUB16,
      ZPN_UKADD8,   ZPN_KADD8,
      ZPN_UKSUB8,   ZPN_KSUB8: overflow_type = HALVING;

      ZPN_URADD16,  ZPN_RADD16,   
      ZPN_URSUB16,  ZPN_RSUB16, 
      ZPN_URADD8,   ZPN_RADD8,   
      ZPN_URSUB8,   ZPN_RSUB8: overflow_type = SATURATING;

      default: overflow_type = NONE;
    endcase
  end

  logic       carry_out0, carry_out1, carry_out2, carry_out3;
  logic[8:0]  alu_result0, alu_result1, alu_result2, alu_result3;
  
  assign alu_result0 = adder_in_a_i[8:1] + adder_in_b_i[8:1];
  assign carry_out0 = (alu_width == WIDTH8 ? 1'b0 : alu_result0[8]);

  assign alu_result1 = adder_in_a_i[16:9] + adder_in_b_i[16:9] + {7'b000_0000, carry_out0};
  assign carry_out1 = (alu_width != WIDTH32 ? 1'b0 : alu_result1[8]);

  assign alu_result2 = adder_in_a_i[24:17] + adder_in_b_i[24:17] + {7'b000_0000, carry_out1};
  assign carry_out2 = (alu_width == WIDTH8 ? 1'b0 : alu_result2[8]);

  assign alu_result3 = adder_in_a_i[32:25] + adder_in_b_i[32:25] + {7'b000_0000, carry_out2};
  assign carry_out3 = (alu_width == WIDTH32 ? alu_result3[8] : 1'b0);   // Not needed?

  unique case (overflow_type)
    HALVING: begin
      unique case (alu_width)
        WIDTH8:   adder_result_ext_o = {carry_out3, alu_result3[8:1], alu_result2[8:1], alu_result1[8:1], alu_result0[8:1], 1'b1};
        WIDTH16:  adder_result_ext_o = {carry_out3, {alu_result3[8:0], alu_result2[7:0]}[16:1], {alu_result1[8:0], alu_result0[7:0]}[16], 1'b1};
      endcase
    end

    SATURATING: begin
      unique case (alu_width)
        // TODO: Make this saturating
        WIDTH8:   adder_result_ext_o = {carry_out3, alu_result3[8:1], alu_result2[8:1], alu_result1[8:1], alu_result0[8:1], 1'b1};
        WIDTH16:  adder_result_ext_o = {carry_out3, {alu_result3[8:0], alu_result2[7:0]}[16:1], {alu_result1[8:0], alu_result0[7:0]}[16], 1'b1};
      endcase
    end

    NONE: begin
      assign adder_result_ext_o = {carry_out3, alu_result3[7:0], alu_result2[7:0], alu_result1[7:0], alu_result0[7:0], 1'b1};
    end
  endcase

  assign adder_result_o = adder_result_ext_o[32:1];

endmodule