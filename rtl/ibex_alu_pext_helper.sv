// Copyright lowRISC contributors.
// Copyright 2018 ETH Zurich and University of Bologna, see also CREDITS.md.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

/*
 * Helper unit for decoding various Pext control signals
 */
module ibex_alu_pext_helper (
  input  ibex_pkg_pext::zpn_op_e  zpn_operator_i,
  input  ibex_pkg::alu_op_e       alu_operator_i,
  input  ibex_pkg::md_op_e        md_operator_i,
  output logic                    zpn_instr_o,

  output logic                    imm_instr_o,
  output logic                    width32_o,
  output logic                    width8_o,
  output logic                    signed_ops_o,
  output logic                    comp_signed_o,
  output logic[1:0]               alu_sub_o,
  output logic                    crossed_o,
  output logic                    adder_sat_o,
  output logic                    rounding_o
);
  import ibex_pkg_pext::*;
  import ibex_pkg::*;

  logic zpn_instr;
  assign zpn_instr   = (alu_operator_i == ZPN_INSTR);
  assign zpn_instr_o = zpn_instr; 


  ///////////////////////
  // Immediate decoder //
  ///////////////////////
  always_comb begin
    unique case (zpn_operator_i)
      // Shift ops
      ZPN_SRAI16,   ZPN_SRAI8,
      ZPN_SRLI16,   ZPN_SRLI8,
      ZPN_SLLI16,   ZPN_SLLI8,
      ZPN_KSLLIW,   ZPN_SRAIu,
      ZPN_KSLLI16,  ZPN_KSLLI8,
      // Clip ops
      ZPN_SCLIP16,  ZPN_SCLIP8,  
      ZPN_SCLIP32,  ZPN_UCLIP32: imm_instr_o = zpn_instr;

      default: imm_instr_o = 1'b0;
    endcase
  end


  //////////////////////
  // Rounding decoder //
  //////////////////////
  always_comb begin
    unique case (zpn_operator_i)
      // Shift ops
      ZPN_AVE: rounding_o = zpn_instr;

      default: rounding_o = 1'b0;
    endcase
  end


  ////////////////////////
  // Width/sign decoder //
  ////////////////////////
  always_comb begin
    unique case (alu_operator_i)
      ZPN_INSTR: begin
        unique case (zpn_operator_i)
          // Signed 32-bit
          ZPN_MADDR32,  ZPN_MSUBR32,
          ZPN_KMMAC,    ZPN_KMMACu,
          ZPN_KMMSB,    ZPN_KMMSBu,
          ZPN_KADDW,    ZPN_RADDW,
          ZPN_KSUBW,    ZPN_RSUBW,
          ZPN_CLRS32,   ZPN_SCLIP32,
          ZPN_AVE,      ZPN_KABSW,
          ZPN_SRAu,     ZPN_SRAIu: begin

            width32_o    = 1'b1;
            width8_o     = 1'b0;
            signed_ops_o = 1'b1;

          end

          // Unsigned 32-bit
          ZPN_UKADDW,   ZPN_URADDW,
          ZPN_UKSUBW,   ZPN_URSUBW,
          ZPN_UCLIP32,  ZPN_KSLLW,  
          ZPN_KSLLIW: begin
            
            width32_o    = 1'b1;
            width8_o     = 1'b0;
            signed_ops_o = 1'b0;

          end

          // Signed 16-bit
          ZPN_RADD16,   ZPN_KADD16,
          ZPN_ADD16,    ZPN_RSUB16,
          ZPN_KSUB16,   ZPN_SUB16,    
          ZPN_KADDH,    ZPN_KSUBH,
          ZPN_RCRAS16,  ZPN_RCRSA16,
          ZPN_KCRAS16,  ZPN_KCRSA16,
          ZPN_CRAS16,   ZPN_CRSA16,
          ZPN_RSTAS16,  ZPN_RSTSA16,
          ZPN_KSTAS16,  ZPN_KSTSA16,
          ZPN_STAS16,   ZPN_STSA16,
          ZPN_SCMPLT16, ZPN_SCMPLE16,
          ZPN_CMPEQ16,  ZPN_SRA16,
          ZPN_SRA16u,   ZPN_SRAI16,
          ZPN_SMIN16,   ZPN_SMAX16,
          ZPN_SCLIP16,  ZPN_KABS16,
          ZPN_CLRS16: begin

            width32_o    = 1'b0;
            width8_o     = 1'b0;
            signed_ops_o = 1'b1;

          end

          // Signed 8-bit
          ZPN_RADD8,   ZPN_KADD8,
          ZPN_ADD8,    ZPN_RSUB8,
          ZPN_KSUB8,   ZPN_SUB8,    
          ZPN_SCMPLT8, ZPN_SCMPLE8,
          ZPN_CMPEQ8,  ZPN_SRA8,
          ZPN_SRA8u,   ZPN_SRAI8,
          ZPN_SMIN8,   ZPN_SMAX8,
          ZPN_SCLIP8,  ZPN_KABS8,
          ZPN_CLRS8: begin

            width32_o    = 1'b0;
            width8_o     = 1'b1;
            signed_ops_o = 1'b1;

          end

          // Unsiged 8-bit
          ZPN_URADD8,  ZPN_UKADD8,
          ZPN_URSUB8,  ZPN_UKSUB8,
          ZPN_UCMPLT8, ZPN_UCMPLE8,
          ZPN_SRL8,    ZPN_SRL8u,
          ZPN_SRLI8,   ZPN_SLL8,
          ZPN_KSLL8,   ZPN_SLLI8,
          ZPN_UMIN8,   ZPN_UMAX8,
          ZPN_CLZ8: begin

            width32_o    = 1'b0;
            width8_o     = 1'b1;
            signed_ops_o = 1'b0;

          end

          // Unsigned 16-bit
          default: begin

            width32_o    = 1'b0;
            width8_o     = 1'b0;
            signed_ops_o = 1'b0;

          end
        endcase
      end

      default: begin

        width32_o    = 1'b1;
        width8_o     = 1'b0;
        signed_ops_o = 1'b0;

      end
    endcase

  end


  /////////////////////////
  // Subtraction decoder //
  /////////////////////////
  always_comb begin
    unique case (alu_operator_i)
      ZPN_INSTR: begin
        unique case (zpn_operator_i)
          // Subtraction ops
          ZPN_RSUB16,   ZPN_RSUB8,   ZPN_RSUBW,   
          ZPN_KSUB16,   ZPN_KSUB8,   ZPN_KSUBW,   ZPN_KSUBH,
          ZPN_URSUB16,  ZPN_URSUB8,  ZPN_URSUBW,   
          ZPN_UKSUB16,  ZPN_UKSUB8,  ZPN_UKSUBW,  ZPN_UKSUBH,
          ZPN_SUB16,    ZPN_SUB8,
          // Comparator ops
          ZPN_CMPEQ16,  ZPN_CMPEQ8,
          ZPN_SCMPLT16, ZPN_SCMPLT8,
          ZPN_SCMPLE16, ZPN_SCMPLE8,
          ZPN_UCMPLT16, ZPN_UCMPLT8,
          ZPN_UCMPLE16, ZPN_UCMPLE8,
          // Abs ops
          ZPN_KABS16, ZPN_KABS8, ZPN_KABSW,
          // Min/Max ops
          ZPN_SMIN16, ZPN_SMIN8,
          ZPN_SMAX16, ZPN_SMAX8,
          ZPN_UMIN16, ZPN_UMIN8,
          ZPN_UMAX16, ZPN_UMAX8,
          // 32-bit Mult/Accum ops
          ZPN_KMMSB,  ZPN_KMMSBu,  ZPN_MSUBR32: alu_sub_o = 2'b11;

          // Sub/Add ops
          ZPN_RCRSA16,  ZPN_RSTSA16,
          ZPN_KCRSA16,  ZPN_KSTSA16,
          ZPN_URCRSA16, ZPN_URSTSA16,
          ZPN_UKCRSA16, ZPN_UKSTSA16,
          ZPN_CRSA16,   ZPN_STSA16: alu_sub_o = 2'b10;

          // Add/Sub ops
          ZPN_RCRAS16,  ZPN_RSTAS16,
          ZPN_KCRAS16,  ZPN_KSTAS16,
          ZPN_URCRAS16, ZPN_URSTAS16,
          ZPN_UKCRAS16, ZPN_UKSTAS16,
          ZPN_CRAS16,   ZPN_STAS16: alu_sub_o = 2'b01;
          
          // All other ops require Add
          default: alu_sub_o = 2'b00;
        endcase
      end

      ALU_ADD: begin
        unique case(md_operator_i)
          MD_OP_DIV, MD_OP_REM: alu_sub_o = 2'b11;

          default: alu_sub_o = 2'b00;
        endcase
      end

      // Adder OPs
      ALU_SUB,
      // Comparator OPs
      ALU_EQ,   ALU_NE,
      ALU_GE,   ALU_GEU,
      ALU_LT,   ALU_LTU,
      ALU_SLT,  ALU_SLTU,
      // MinMax OPs (RV32B Ops)
      ALU_MIN,  ALU_MINU,
      ALU_MAX,  ALU_MAXU: alu_sub_o = 2'b11;

      default: alu_sub_o = 2'b00;
    endcase
  end


  // non-zpn comp signed decoder
  always_comb begin
    unique case(alu_operator_i)
      ALU_GE,   ALU_LT,
      ALU_SLT,  ALU_MIN,
      ALU_MAX: comp_signed_o = 1'b1;

      default: comp_signed_o = 1'b0;
    endcase
  end


  // Decode cross Add/Sub
  always_comb begin
    unique case(alu_operator_i)
      ZPN_INSTR: begin
        unique case(zpn_operator_i)
          ZPN_RCRAS16,  ZPN_RCRSA16, 
          ZPN_KCRAS16,  ZPN_KCRSA16,
          ZPN_URCRAS16, ZPN_URCRSA16, 
          ZPN_UKCRAS16, ZPN_UKCRSA16,
          ZPN_CRAS16,   ZPN_CRSA16: crossed_o = 1'b1;

          default: crossed_o = 1'b0;
        endcase
      end

      default: crossed_o = 1'b0;
    endcase
  end


  // Decode which ops use saturation
  always_comb begin
    unique case(alu_operator_i)
      ZPN_INSTR: begin
        unique case(zpn_operator_i)
          ZPN_KSLLW,  ZPN_KSLL16,   ZPN_KSLL8,
          ZPN_KSLLIW, ZPN_KSLLI16,  ZPN_KSLLI8: adder_sat_o = 1'b0;

          default: adder_sat_o = 1'b1;
        endcase
      end

      default: adder_sat_o = 1'b0;
    endcase
  end

endmodule
