// Copyright lowRISC contributors.
// Copyright 2018 ETH Zurich and University of Bologna, see also CREDITS.md.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

/*
 * Helper unit for decoding various Pext control signals
 */
 module ibex_mult_pext_helper (
  input  ibex_pkg_pext::zpn_op_e          zpn_operator_i,
  input  ibex_pkg::alu_op_e               alu_operator_i,

  output ibex_pkg_pext::mult_pext_mode_e  mult_mode_o,
  output logic[1:0]                       cycle_count_o,
  output logic[1:0]                       accum_sub_o,       // [sub in 32x32, sub in 32x16]
  output logic[1:0]                       dsum_mult_o,
  output logic                            crossed_o,
  output logic                            accum_o//,
  //output logic                            doubling_o
);
  import ibex_pkg_pext::*;
  import ibex_pkg::*;

  // Decode multiplier mode
  always_comb begin
    unique case (alu_operator_i)
      ZPN_INSTR: begin
        unique case (zpn_operator_i)
          ZPN_SMAQA,    ZPN_SMAQAsu,
          ZPN_UMAQA,    ZPN_KHM8,
          ZPN_KHMX8: mult_mode_o = M8x8;

          ZPN_SMMUL,    ZPN_SMMULu,
          ZPN_KMMAC,    ZPN_KMMACu,
          ZPN_KMMSB,    ZPN_KMMSBu,
          ZPN_KWMMUL,   ZPN_KWMMULu,
          ZPN_MADDR32,  ZPN_MSUBR32: mult_mode_o = M32x32;

          ZPN_SMMWB,    ZPN_SMMWBu,
          ZPN_SMMWT,    ZPN_SMMWTu,
          ZPN_KMMAWB,   ZPN_KMMAWBu,
          ZPN_KMMAWT,   ZPN_KMMAWTu,
          ZPN_KMMWB2,   ZPN_KMMWB2u,
          ZPN_KMMWT2,   ZPN_KMMWT2u,
          ZPN_KMMAWB2,  ZPN_KMMAWB2u,
          ZPN_KMMAWT2,  ZPN_KMMAWT2u: mult_mode_o = M32x16;

          default: mult_mode_o = M16x16;
        endcase
      end

      default: mult_mode_o = M32x32;
    endcase
  end

  // Decode how many cycles are required for mult op
  // 1 cycle  -> 2'b00
  // 2 cycles -> 2'b01
  // 3 cycles -> 2'b11
  always_comb begin
    unique case (alu_operator_i)
      ZPN_INSTR: begin
        unique case(zpn_operator_i)
          // 2 cycle ops
          ZPN_SMMUL,  ZPN_SMMULu,
          ZPN_KWMMUL, ZPN_KWMMULu: cycle_count_o = 2'b01;

          // 3 cycle ops
          ZPN_MADDR32,  ZPN_MSUBR32,
          ZPN_KMMAC,    ZPN_KMMACu,
          ZPN_KMMSB,    ZPN_KMMSBu: cycle_count_o = 2'b11;

          // 1 cycle ops
          default: cycle_count_o = 2'b00;
        endcase
      end
      
      // Normal mults are 2 cycle
      default: cycle_count_o = 2'b01;
    endcase
  end

  // Decode sub for accumulating ops (only used for less than 32x32 mults)
  always_comb begin
    unique case(alu_operator_i)
      ZPN_INSTR: begin
        unique case(zpn_operator_i) 
          ZPN_SMDS,  ZPN_SMXDS,  
          ZPN_KMADS, ZPN_KMAXDS: accum_sub_o = 2'b01;

          ZPN_KMSDA,  ZPN_KMSXDA: accum_sub_o = 2'b10;

          default: accum_sub_o = 2'b00;
        endcase
      end

      default: accum_sub_o = 2'b00;
    endcase
  end

  // Decode add mode
  always_comb begin
    unique case(alu_operator_i)
      ZPN_INSTR: begin
        unique case(zpn_operator_i)
          ZPN_KMADA,  ZPN_KMAXDA,   
          ZPN_KMADS,  ZPN_KMADRS,
          ZPN_KMAXDS, ZPN_KMSDA,
          ZPN_KMSXDA: dsum_mult_o = 1'b1;

          default: dsum_mult_o = 1'b0;
        endcase
      end

      default: dsum_mult_o = 1'b0;
    endcase
  end

  // Decode when operands should be crossed
  always_comb begin
    unique case (alu_operator_i)
      ZPN_INSTR: begin
        unique case (zpn_operator_i)
          // "Real" crossed ops
          ZPN_KHMX16, ZPN_KHMX8,
          ZPN_SMXDS,  ZPN_KMAXDA,
          ZPN_KMXDA,  ZPN_KMAXDS, 
          ZPN_KMSXDA,
          // Implicitly crossed ops
          ZPN_SMBT16,
          ZPN_KHMBT,    ZPN_KDMBT,      // BT ops want Ah0*Bh1
          ZPN_KDMABT,   ZPN_KMABT,
          ZPN_KMMAWT,   ZPN_KMMAWTu,    // T ops want A*Bh1
          ZPN_KMMAWT2,  ZPN_KMMAWT2u,
          ZPN_SMMWT,    ZPN_SMMWTu,
          ZPN_KMMWT2,   ZPN_KMMWT2u:  crossed_o = 1'b1;

          default: crossed_o = 1'b0;
        endcase
      end

      default: crossed_o = 1'b0;
    endcase
  end

  // Decode ops that use ALU for accumulation
  // Accumulating ops are ops that are defined as rd = rd + result
  always_comb begin
    unique case(alu_operator_i)
      ZPN_INSTR: begin
        unique case(zpn_operator_i)
          ZPN_KMMAC,    ZPN_KMMACu,
          ZPN_KMMSB,    ZPN_KMMSBu,
          ZPN_MADDR32,  ZPN_MSUBR32: accum_o = 1'b1;

          default: accum_o = 1'b0;
        endcase
      end

      default: accum_o = 1'b0;
    endcase
  end

  // Decode ops that double the multiplication result before accumulation
  /*always_comb begin
    unique case(alu_operator_i)
      ZPN_INSTR: begin
        unique case (zpn_operator_i)
          ZPN_KMMWB2
          
          default: doubling_o = 1'b0;
        endcase
      end

      default: doubling_o = 1'b0;
    endcase
  end
*/

endmodule
