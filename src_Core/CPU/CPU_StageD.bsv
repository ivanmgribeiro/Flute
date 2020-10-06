// Copyright (c) 2016-2019 Bluespec, Inc. All Rights Reserved

package CPU_StageD;

// ================================================================
// This is Stage D ("decode") of the "Flute_V3" CPU.

// ================================================================
// Exports

export
CPU_StageD_IFC (..),
mkCPU_StageD;

// ================================================================
// BSV library imports

import FIFOF        :: *;
import GetPut       :: *;
import ClientServer :: *;
import ConfigReg    :: *;

// ----------------
// BSV additional libs

import Cur_Cycle :: *;

// ================================================================
// Project imports

import ISA_Decls        :: *;
import CPU_Globals      :: *;
import Near_Mem_IFC     :: *;
`ifdef NEW_BYPASS
import GPR_RegFile      :: *;
`endif

`ifdef ISA_C
// 'C' extension (16b compressed instructions)
import CPU_Decode_C     :: *;
`endif

// ================================================================
// Interface

interface CPU_StageD_IFC;
   // ---- Reset
   interface Server #(Token, Token) server_reset;

   // ---- Output
   (* always_ready *)
   method Output_StageD out;

   (* always_ready *)
   method Action deq;

   // ---- Input
   (* always_ready *)
   method Action enq (Data_StageF_to_StageD  data_stageF_to_stageD);

   (* always_ready *)
   method Action set_full (Bool full);
endinterface

// ================================================================
// Implementation module

`ifdef SYNTHESIZE_MODULES
(* synthesize *)
`endif
module mkCPU_StageD #(Bit #(4)  verbosity,
                      MISA misa,
                      Bit #(1) pcc_cap_mode_bit,
                      Bit #(1) fresh_pcc_cap_mode_bit)
                    (CPU_StageD_IFC);

   FIFOF #(Token)  f_reset_reqs <- mkFIFOF;
   FIFOF #(Token)  f_reset_rsps <- mkFIFOF;

   Reg #(Bool)                   rg_full <- mkReg (False);
   Reg #(Data_StageF_to_StageD)  rg_data <- mkRegU;

   Bit #(2) xl = ((xlen == 32) ? misa_mxl_32 : misa_mxl_64);

   Instr instr = rg_data.instr;

   // If we are using NEW_BYPASS, the instruction decompression happens in StageF
   // if we are using NEW_BYPASS and DELAY_REGFILE_READ, decompression happens here
`ifdef ISA_C
`ifdef NEW_BYPASS
`ifdef DELAY_REGFILE_READ
   Instr_C instr_C = instr [15:0];
   let decode_c_wrapper <- mkDecode_C;
   let instr_decomp = decode_c_wrapper.decode_c_out (misa, xl, instr_C);
   if (! rg_data.is_i32_not_i16) begin
      //instr = fv_decode_C (misa, xl, instr_C);
      instr = instr_decomp;
   end
`endif
`else
   Instr_C instr_C = instr [15:0];
   let decode_c_wrapper <- mkDecode_C;
   let instr_decomp = decode_c_wrapper.decode_c_out (misa, xl, instr_C);
   if (! rg_data.is_i32_not_i16) begin
      //instr = fv_decode_C (misa, xl, instr_C);
      instr = instr_decomp;
   end
`endif
`endif

   // ----------------------------------------------------------------
   // BEHAVIOR

   rule rl_reset;
      f_reset_reqs.deq;
      rg_full <= False;
      f_reset_rsps.enq (?);
   endrule

   // ----------------
   // Combinational output function

   let decode_wrapper = mkDecode;

   Bit #(1) cap_mode_bit = rg_data.refresh_pcc ? fresh_pcc_cap_mode_bit
                                               : pcc_cap_mode_bit;
   let decoded_instr = fv_decode (instr, cap_mode_bit);
   function Output_StageD fv_out;
      Output_StageD  output_stageD = ?;

      // This stage is empty
      if (! rg_full) begin
	 output_stageD.ostatus = OSTATUS_EMPTY;
      end
      else begin
	 output_stageD.ostatus        = OSTATUS_PIPE;
	 output_stageD.data_to_stage1 = Data_StageD_to_Stage1 {
                                                               fetch_addr:     rg_data.fetch_addr,
`ifdef ISA_CHERI
                                                               refresh_pcc:    rg_data.refresh_pcc,
`endif
`ifdef RVFI_DII
                                                               instr_seq:      rg_data.instr_seq,
`endif
							       priv:           rg_data.priv,
							       epoch:          rg_data.epoch,
							       is_i32_not_i16: rg_data.is_i32_not_i16,
							       exc:            rg_data.exc,
							       exc_code:       rg_data.exc_code,
							       tval:           rg_data.tval,
							       instr:          instr,
`ifdef NEW_BYPASS
`ifndef DELAY_REGFILE_READ
                                                               rs1_val: rs1_val,
                                                               rs2_val: rs2_val,
`endif
`endif
`ifdef ISA_C
`ifdef NEW_BYPASS
							       instr_C:        ?,
`else
							       instr_C:        instr_C,
`endif
`endif
							       pred_fetch_addr:rg_data.pred_fetch_addr,
							       decoded_instr:  decoded_instr};
      end

      return output_stageD;
   endfunction: fv_out

   // ================================================================
   // INTERFACE

   // ---- Reset
   interface server_reset = toGPServer (f_reset_reqs, f_reset_rsps);

   // ---- Output
   method Output_StageD out;
      return fv_out;
   endmethod

   method Action deq ();
      noAction;
   endmethod

   // ---- Input
   method Action enq (Data_StageF_to_StageD  data);
      rg_data <= data;
      if (verbosity > 1)
	 $display ("    CPU_StageD.enq (Data_StageF_to_StageD)");
   endmethod

   method Action set_full (Bool full);
      rg_full <= full;
   endmethod
endmodule

// ================================================================

endpackage
