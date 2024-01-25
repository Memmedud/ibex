// Copyright lowRISC contributors.
// Copyright 2018 ETH Zurich and University of Bologna, see also CREDITS.md.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0


/**
 * P-ext instruction decoder
 */
module ibex_decoder_pext #(
  
) (
  input  logic[31:0]        instr_rdata_i,

  output ibex_pkg_pext::zpn_op_e  zpn_operator_o,
  output ibex_pkg_pext::signed_type_e signed_operands

  //output logic                    imm_o // TODO: Implement this
); 
  import ibex_pkg_pext::*;



logic[31:0] instr;
assign instr = instr_rdata_i;

  // Decode instruction width
  always_comb begin
    unique case (zpn_operator_o)
      // TODO: Fix this!!!
      ZPN_RADD16,   ZPN_KADD16,
      ZPN_RSUB16,   ZPN_KSUB16,
      ZPN_SMIN16,   ZPN_SMAX16,   
      ZPN_SCMPLT16, ZPN_SCMPLE16: signed_operands = S16;

      ZPN_UKADD16,  
      ZPN_UKSUB16,  ZPN_SUB16, 
      ZPN_URSUB16,  ZPN_CMPEQ16,  
      ZPN_UCMPLT16, ZPN_UCMPLE16, 
      ZPN_UMIN16,   ZPN_UMAX16:   signed_operands = U16;   
      
      ZPN_RSUB8,    ZPN_KSUB8,
      ZPN_SMIN8,    ZPN_SMAX8,
      ZPN_SCMPLT8,  ZPN_SCMPLE8:  signed_operands = S8;

      ZPN_UKSUB8,   ZPN_SUB8,
      ZPN_URSUB8,   ZPN_CMPEQ8,   
      ZPN_UCMPLT8,  ZPN_UCMPLE8,
      ZPN_UMIN8,    ZPN_UMAX8:    signed_operands = U8;

      default: signed_operands = U16;   // TODO: Fix this hack
    endcase
  end


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


          // Multiplication (More mult instructions in funct3 = 001)
          // 16-bit multipliction
          7'b101_0000: zpn_operator_o = ZPN_SMUL16;
          7'b101_0001: zpn_operator_o = ZPN_SMULX16;
          7'b101_1000: zpn_operator_o = ZPN_UMUL16;
          7'b101_1001: zpn_operator_o = ZPN_UMULX16;
          7'b100_0011: zpn_operator_o = ZPN_KHM16;
          7'b100_1011: zpn_operator_o = ZPN_KHMX16;

          // 8-bit multiplication
          7'b101_0100: zpn_operator_o = ZPN_SMUL8;
          7'b101_0101: zpn_operator_o = ZPN_SMULX8;
          7'b101_1100: zpn_operator_o = ZPN_UMUL8;
          7'b101_1101: zpn_operator_o = ZPN_UMULX8;
          7'b100_0111: zpn_operator_o = ZPN_KHM8;
          7'b100_1111: zpn_operator_o = ZPN_KHMX8;


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
          7'b010_0001: zpn_operator_o = ZPN_SMAX16;
          7'b100_1000: zpn_operator_o = ZPN_UMIN16;
          7'b100_1001: zpn_operator_o = ZPN_UMAX16;
          7'b100_0100: zpn_operator_o = ZPN_SMIN8;
          7'b010_0101: zpn_operator_o = ZPN_SMAX8;
          7'b100_1100: zpn_operator_o = ZPN_UMIN8;
          7'b100_1101: zpn_operator_o = ZPN_UMAX8;


          // Shift
          // 16-bit shift instructions
          7'b010_1000: zpn_operator_o = ZPN_SRA16;
          7'b011_1000: zpn_operator_o = ZPN_SRAI16;
          7'b010_1001: zpn_operator_o = ZPN_SRL16;
          7'b011_1001: zpn_operator_o = ZPN_SRLI16;
          7'b010_1010: zpn_operator_o = ZPN_SLL16;
          7'b011_1010: zpn_operator_o = ZPN_SLLI16; // NOTE: Rounding is determined in immediate value...
          // TODO: Maybe add the other shift instructions
      
          // 8-bit shift instructions
          7'b010_1100: zpn_operator_o = ZPN_SRA16;
          7'b011_1100: zpn_operator_o = ZPN_SRAI16;
          7'b010_1101: zpn_operator_o = ZPN_SRL16;
          7'b011_1101: zpn_operator_o = ZPN_SRLI16;
          7'b010_1110: zpn_operator_o = ZPN_SLL16;
          7'b011_1110: zpn_operator_o = ZPN_SLLI16; // NOTE: Rounding is determined in immediate value...
          // TODO: Maybe add the other shift instructions


          // Oneop1 instructions
          7'b101_0110: begin
            unique case (subf5)
              // TODO: Add INSB

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

              // TODO: Add KABS8/16

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
            //5'b1_1000: zpn_operator_o = ZPN_CLRS32;
            //5'b1_1001: zpn_operator_o = ZPN_CLRZ32;

              default: ;
            endcase
          end

          default: ;
        endcase
      end

      3'b001: begin
        unique case (funct7)
          // TODO: Add instructions

          default: ;
        endcase
      end

      3'b010: begin
        unique case (funct7)
          // TODO: Add instructions

          default: ;
        endcase
      end

      default: ;
    endcase
  end

  // Not all bits of instruction are used
  logic[16:0] unused_bits = {instr[19:15], instr[11:0]};

endmodule
