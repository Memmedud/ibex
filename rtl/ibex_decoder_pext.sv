// Copyright lowRISC contributors.
// Copyright 2018 ETH Zurich and University of Bologna, see also CREDITS.md.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

/*
 * P-ext instruction decoder
 */
module ibex_decoder_pext #(
  
) (
  input  logic[31:0]                instr_rdata_i,

  output ibex_pkg_pext::zpn_op_e    zpn_operator_o,
  output logic                      zpn_illegal_insn_o,
  output logic[4:0]                 imm_operand_o
); 
  import ibex_pkg_pext::*;

  logic[31:0] instr;
  assign instr = instr_rdata_i;
  assign imm_operand_o = instr[24:20];


  /////////////
  // Decoder //
  /////////////
  logic[2:0] funct3;
  logic[6:0] funct7;
  logic[4:0] subf5;

  assign funct3 = instr[14:12];
  assign funct7 = instr[31:25];
  assign subf5  = instr[24:20]; 

  always_comb begin
    zpn_illegal_insn_o = 1'b0;

    unique case (funct3)
      3'b000: begin
        unique case (funct7)
          // Add/Sub
          // 16-bit add instructions
          7'b010_0000: zpn_operator_o = ZPN_ADD16;
          7'b001_1000: zpn_operator_o = ZPN_UKADD16;
          7'b001_0000: zpn_operator_o = ZPN_URADD16;
          7'b000_1000: zpn_operator_o = ZPN_KADD16;
          7'b000_0000: zpn_operator_o = ZPN_RADD16;

          // 16-bit sub instructions
          7'b010_0001: zpn_operator_o = ZPN_SUB16;
          7'b001_1001: zpn_operator_o = ZPN_UKSUB16;
          7'b001_0001: zpn_operator_o = ZPN_URSUB16;
          7'b000_1001: zpn_operator_o = ZPN_KSUB16;
          7'b000_0001: zpn_operator_o = ZPN_RSUB16;

          // 8-bit add instructions
          7'b010_0100: zpn_operator_o = ZPN_ADD8;
          7'b001_1100: zpn_operator_o = ZPN_UKADD8;
          7'b001_0100: zpn_operator_o = ZPN_URADD8;
          7'b000_1100: zpn_operator_o = ZPN_KADD8;
          7'b000_0100: zpn_operator_o = ZPN_RADD8;

          // 8-bit sub instructions
          7'b010_0101: zpn_operator_o = ZPN_SUB8;
          7'b001_1101: zpn_operator_o = ZPN_UKSUB8;
          7'b001_0101: zpn_operator_o = ZPN_URSUB8;
          7'b000_1101: zpn_operator_o = ZPN_KSUB8;
          7'b000_0101: zpn_operator_o = ZPN_RSUB8;

          // Cross Add/Sub 
          7'b010_0010: zpn_operator_o = ZPN_CRAS16;
          7'b001_1010: zpn_operator_o = ZPN_UKCRAS16;
          7'b001_0010: zpn_operator_o = ZPN_URCRAS16;
          7'b000_1010: zpn_operator_o = ZPN_KCRAS16;
          7'b000_0010: zpn_operator_o = ZPN_RCRAS16;

          // Cross Sub/Add
          7'b010_0011: zpn_operator_o = ZPN_CRSA16;
          7'b001_1011: zpn_operator_o = ZPN_UKCRSA16;
          7'b001_0011: zpn_operator_o = ZPN_URCRSA16;
          7'b000_1011: zpn_operator_o = ZPN_KCRSA16;
          7'b000_0011: zpn_operator_o = ZPN_RCRSA16;

          // Multiplication (More mult instructions in funct3 = 001)
          // 16x16 multipliction
          7'b100_0011: zpn_operator_o = ZPN_KHM16;
          7'b100_1011: zpn_operator_o = ZPN_KHMX16;

          // 8x8 multiplication
          7'b100_0111: zpn_operator_o = ZPN_KHM8;
          7'b100_1111: zpn_operator_o = ZPN_KHMX8;
          7'b110_0100: zpn_operator_o = ZPN_SMAQA;
          7'b110_0101: zpn_operator_o = ZPN_SMAQAsu;
          7'b110_0110: zpn_operator_o = ZPN_UMAQA;

          // Comparison
          // 16-bit Comparison instructions
          7'b010_0110: zpn_operator_o = ZPN_CMPEQ16;
          7'b001_1110: zpn_operator_o = ZPN_UCMPLE16;
          7'b001_0110: zpn_operator_o = ZPN_UCMPLT16;
          7'b000_1110: zpn_operator_o = ZPN_SCMPLE16;
          7'b000_0110: zpn_operator_o = ZPN_SCMPLT16;

          // 8-bit Comparison instructions
          7'b010_0111: zpn_operator_o = ZPN_CMPEQ8;
          7'b001_1111: zpn_operator_o = ZPN_UCMPLE8;
          7'b001_0111: zpn_operator_o = ZPN_UCMPLT8;
          7'b000_1111: zpn_operator_o = ZPN_SCMPLE8;
          7'b000_0111: zpn_operator_o = ZPN_SCMPLT8;
          

          // Min/Max
          // Min/Max ops
          7'b100_0000: zpn_operator_o = ZPN_SMIN16;
          7'b100_0001: zpn_operator_o = ZPN_SMAX16;
          7'b100_1000: zpn_operator_o = ZPN_UMIN16;
          7'b100_1001: zpn_operator_o = ZPN_UMAX16;
          7'b100_0100: zpn_operator_o = ZPN_SMIN8;
          7'b100_0101: zpn_operator_o = ZPN_SMAX8;
          7'b100_1100: zpn_operator_o = ZPN_UMIN8;
          7'b100_1101: zpn_operator_o = ZPN_UMAX8;


          // Shift
          // 16-bit shift instructions
          7'b010_1000: zpn_operator_o = ZPN_SRA16;
          7'b011_0000: zpn_operator_o = ZPN_SRA16u;
          7'b011_1000: zpn_operator_o = ZPN_SRAI16;
          7'b010_1001: zpn_operator_o = ZPN_SRL16;
          7'b011_0001: zpn_operator_o = ZPN_SRL16u;
          7'b011_1001: zpn_operator_o = ZPN_SRLI16;
          7'b010_1010: zpn_operator_o = ZPN_SLL16;
          7'b011_0010: zpn_operator_o = ZPN_KSLL16;
          7'b011_1010: zpn_operator_o = ZPN_SLLI16; // NOTE: Rounding is determined in immediate value...
          7'b010_1011: zpn_operator_o = ZPN_KSLRA16; 
          7'b011_0011: zpn_operator_o = ZPN_KSLRA16u; 
      
          // 8-bit shift instructions
          7'b010_1100: zpn_operator_o = ZPN_SRA8;
          7'b011_0100: zpn_operator_o = ZPN_SRA8u;
          7'b011_1100: zpn_operator_o = ZPN_SRAI8;
          7'b010_1101: zpn_operator_o = ZPN_SRL8;
          7'b011_0101: zpn_operator_o = ZPN_SRL8u;
          7'b011_1101: zpn_operator_o = ZPN_SRLI8;
          7'b010_1110: zpn_operator_o = ZPN_SLL8;
          7'b011_0110: zpn_operator_o = ZPN_KSLL8;
          7'b011_1110: zpn_operator_o = ZPN_SLLI8; // NOTE: Rounding is determined in immediate value...
          7'b010_1111: zpn_operator_o = ZPN_KSLRA8; 
          7'b011_0111: zpn_operator_o = ZPN_KSLRA8u; 


          // Oneop1 instructions
          7'b101_0110: begin
            unique case (subf5)
              // INSB
              5'b0_0000: zpn_operator_o = ZPN_INSB0;
              5'b0_0001: zpn_operator_o = ZPN_INSB1;
              5'b0_0010: zpn_operator_o = ZPN_INSB2;
              5'b0_0011: zpn_operator_o = ZPN_INSB3;

              // SUNPKD
              5'b0_1000: zpn_operator_o = ZPN_SUNPKD810;
              5'b0_1001: zpn_operator_o = ZPN_SUNPKD820;
              5'b0_1010: zpn_operator_o = ZPN_SUNPKD830;
              5'b0_1011: zpn_operator_o = ZPN_SUNPKD831;
              5'b1_0011: zpn_operator_o = ZPN_SUNPKD832;

              //ZUNPKD
              5'b0_1100: zpn_operator_o = ZPN_ZUNPKD810;
              5'b0_1101: zpn_operator_o = ZPN_ZUNPKD820;
              5'b0_1110: zpn_operator_o = ZPN_ZUNPKD830;
              5'b0_1111: zpn_operator_o = ZPN_ZUNPKD831;
              5'b1_0111: zpn_operator_o = ZPN_ZUNPKD832;

              // ABS
              5'b1_0000: zpn_operator_o = ZPN_KABS8; 
              5'b1_0001: zpn_operator_o = ZPN_KABS16;
              5'b1_0100: zpn_operator_o = ZPN_KABSW; 

              default: ;
            endcase
          end
          
          // Oneop2 instructions
          7'b101_0111: begin
            unique case (subf5)
              5'b0_0000: zpn_operator_o = ZPN_CLRS8;
              5'b0_0001: zpn_operator_o = ZPN_CLZ8;
              5'b0_1000: zpn_operator_o = ZPN_CLRS16;
              5'b0_1001: zpn_operator_o = ZPN_CLZ16;
              5'b1_1000: zpn_operator_o = ZPN_CLRS32;

              default: ;
            endcase
          end

          // Misc instructions
          7'b111_0000: zpn_operator_o = ZPN_AVE;

          7'b100_0010: zpn_operator_o = ZPN_SCLIP16;    // Also UCLIP16
          7'b100_0110: zpn_operator_o = ZPN_SCLIP8;     // Also UCLIP8
          7'b111_0010: zpn_operator_o = ZPN_SCLIP32;
          7'b111_1010: zpn_operator_o = ZPN_UCLIP32;

          7'b111_1110: zpn_operator_o = ZPN_PBSAD;
          7'b111_1111: zpn_operator_o = ZPN_PBSADA;

          default: ;
        endcase
      end

      3'b001: begin
        unique case (funct7)
          // Add/Sub
          // 32-bit Add
          7'b000_0000: zpn_operator_o = ZPN_KADDW;
          7'b000_1000: zpn_operator_o = ZPN_UKADDW;
          7'b001_0000: zpn_operator_o = ZPN_RADDW;
          7'b001_1000: zpn_operator_o = ZPN_URADDW;

          // 16-bit Add
          7'b000_0010: zpn_operator_o = ZPN_KADDH;
          7'b000_1010: zpn_operator_o = ZPN_UKADDH;

          // 32-bit Sub
          7'b000_0001: zpn_operator_o = ZPN_KSUBW;
          7'b000_1001: zpn_operator_o = ZPN_UKSUBW;
          7'b001_0001: zpn_operator_o = ZPN_RSUBW;
          7'b001_1001: zpn_operator_o = ZPN_URSUBW;

          // 16-bit Sub
          7'b000_0011: zpn_operator_o = ZPN_KSUBW;
          7'b000_1011: zpn_operator_o = ZPN_UKSUBW;


          // Bit-shifting
          // 32-bit Shift
          7'b001_0010: zpn_operator_o = ZPN_SRAu;
          7'b001_0011: zpn_operator_o = ZPN_KSLLW;
          7'b001_1011: zpn_operator_o = ZPN_KSLLIW;
          7'b011_0111: zpn_operator_o = ZPN_KSLRAW;
          7'b011_1111: zpn_operator_o = ZPN_KSLRAWu;
          
          // Pack ops
          7'b000_0111: zpn_operator_o = ZPN_PKBB16;
          7'b000_1111: zpn_operator_o = ZPN_PKBT16;
          7'b001_0111: zpn_operator_o = ZPN_PKTT16;
          7'b001_1111: zpn_operator_o = ZPN_PKTB16;


          // Multiplication
          // 32x32 multiplication
          7'b010_0000: zpn_operator_o = ZPN_SMMUL;
          7'b010_1000: zpn_operator_o = ZPN_SMMULu;
          7'b011_0000: zpn_operator_o = ZPN_KMMAC;
          7'b011_1000: zpn_operator_o = ZPN_KMMACu;
          7'b010_0001: zpn_operator_o = ZPN_KMMSB;
          7'b010_1001: zpn_operator_o = ZPN_KMMSBu;
          7'b011_0001: zpn_operator_o = ZPN_KWMMUL;
          7'b011_1001: zpn_operator_o = ZPN_KWMMULu;
          7'b110_0010: zpn_operator_o = ZPN_MADDR32;
          7'b110_0011: zpn_operator_o = ZPN_MSUBR32;

          // 32x16 multiplication
          7'b010_0010: zpn_operator_o = ZPN_SMMWB;
          7'b010_1010: zpn_operator_o = ZPN_SMMWBu;
          7'b011_0010: zpn_operator_o = ZPN_SMMWT;
          7'b011_1010: zpn_operator_o = ZPN_SMMWTu;
          7'b010_0011: zpn_operator_o = ZPN_KMMAWB;
          7'b010_1011: zpn_operator_o = ZPN_KMMAWBu;
          7'b011_0011: zpn_operator_o = ZPN_KMMAWT;
          7'b011_1011: zpn_operator_o = ZPN_KMMAWTu;
          7'b100_0111: zpn_operator_o = ZPN_KMMWB2;
          7'b100_1111: zpn_operator_o = ZPN_KMMWB2u;
          7'b101_0111: zpn_operator_o = ZPN_KMMWT2;
          7'b101_1111: zpn_operator_o = ZPN_KMMWT2u;
          7'b110_0111: zpn_operator_o = ZPN_KMMAWB2;
          7'b110_1111: zpn_operator_o = ZPN_KMMAWB2u;
          7'b111_0111: zpn_operator_o = ZPN_KMMAWT2;
          7'b111_1111: zpn_operator_o = ZPN_KMMAWT2u;

          // 16x16 multiplication
          7'b000_0100: zpn_operator_o = ZPN_SMBB16;
          7'b000_1100: zpn_operator_o = ZPN_SMBT16;
          7'b001_0100: zpn_operator_o = ZPN_SMTT16;
          7'b001_1100: zpn_operator_o = ZPN_KMDA;
          7'b010_0100: zpn_operator_o = ZPN_KMADA;
          7'b010_1100: zpn_operator_o = ZPN_SMDS;
          7'b011_0100: zpn_operator_o = ZPN_SMDRS;
          7'b011_1100: zpn_operator_o = ZPN_SMXDS;
          7'b001_1101: zpn_operator_o = ZPN_KMXDA;
          7'b010_0101: zpn_operator_o = ZPN_KMAXDA;
          7'b010_1101: zpn_operator_o = ZPN_KMABB;
          7'b011_0101: zpn_operator_o = ZPN_KMABT;
          7'b011_1101: zpn_operator_o = ZPN_KMATT;
          7'b010_0110: zpn_operator_o = ZPN_KMSDA;
          7'b010_1110: zpn_operator_o = ZPN_KMADS;
          7'b011_0110: zpn_operator_o = ZPN_KMADRS;
          7'b011_1110: zpn_operator_o = ZPN_KMAXDS;
          7'b010_0111: zpn_operator_o = ZPN_KMSXDA;
          7'b110_1001: zpn_operator_o = ZPN_KDMABB;
          7'b111_0001: zpn_operator_o = ZPN_KDMABT;
          7'b111_1001: zpn_operator_o = ZPN_KDMATT;
          7'b000_0101: zpn_operator_o = ZPN_KDMBB;
          7'b000_1101: zpn_operator_o = ZPN_KDMBT;
          7'b001_0101: zpn_operator_o = ZPN_KDMTT;
          7'b000_0110: zpn_operator_o = ZPN_KHMBB;
          7'b000_1110: zpn_operator_o = ZPN_KHMBT;
          7'b001_0110: zpn_operator_o = ZPN_KHMTT;

          default: ;
        endcase
      end

      3'b010: begin
        unique case (funct7)
          // Straight Add/Sub 
          7'b101_1010: zpn_operator_o = ZPN_RSTAS16;
          7'b110_0010: zpn_operator_o = ZPN_KSTAS16;
          7'b110_1010: zpn_operator_o = ZPN_URSTAS16;
          7'b111_0010: zpn_operator_o = ZPN_UKSTAS16;
          7'b111_1010: zpn_operator_o = ZPN_STAS16;

          // Straight Sub/Add
          7'b101_1011: zpn_operator_o = ZPN_RSTSA16;
          7'b110_0011: zpn_operator_o = ZPN_KSTSA16;
          7'b110_1011: zpn_operator_o = ZPN_URSTSA16;
          7'b111_0011: zpn_operator_o = ZPN_UKSTSA16;
          7'b111_1011: zpn_operator_o = ZPN_STSA16;
          
          default: ;
        endcase
      end

      default: zpn_illegal_insn_o = 1'b1;
    endcase
  end

  // Not all bits of instruction are used
  logic[16:0] unused_bits = {instr[19:15], instr[11:0]};

endmodule
