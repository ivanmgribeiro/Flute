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

`ifdef NEW_BYPASS
module mkCPU_StageD #(Bit #(4)  verbosity
		     , GPR_RegFile_IFC  gpr_regfile
                     , MISA misa)
                    (CPU_StageD_IFC);
`else
module mkCPU_StageD #(Bit #(4)  verbosity, MISA misa)
                    (CPU_StageD_IFC);
`endif

   FIFOF #(Token)  f_reset_reqs <- mkFIFOF;
   FIFOF #(Token)  f_reset_rsps <- mkFIFOF;

   Reg #(Bool)                   rg_full <- mkReg (False);
   Reg #(Data_StageF_to_StageD)  rg_data <- mkRegU;

   Bit #(2) xl = ((xlen == 32) ? misa_mxl_32 : misa_mxl_64);

   Instr instr = rg_data.instr;

   // If we are using NEW_BYPASS, the instruction decompression happens in StageF
`ifndef NEW_BYPASS
`ifdef ISA_C
   Instr_C instr_C = instr [15:0];

   let decode_c_wrapper <- mkDecodeC;
   rule assign_decode_c_inputs;
      decode_c_wrapper.put_inputs(misa, xl, instr_C);
   endrule

   if (! rg_data.is_i32_not_i16)
      instr = decode_c_wrapper.get_outputs;
`endif
`endif

   let decode_wrapper <- mkDecode;
   rule assign_decode_inputs;
      decode_wrapper.put_inputs(instr);
   endrule

   // ----------------------------------------------------------------
   // BEHAVIOR

   rule rl_reset;
      f_reset_reqs.deq;
      rg_full <= False;
      f_reset_rsps.enq (?);
   endrule

`ifdef NEW_BYPASS
   let rs1 = rg_data.rs1;
   let rs2 = rg_data.rs2;

   let rs1_val = gpr_regfile.read_rs1 (rs1);
   let rs2_val = gpr_regfile.read_rs2 (rs2);
`endif

   // ----------------
   // Combinational output function

   function Output_StageD fv_out;
      let decoded_instr = decode_wrapper.get_outputs;

      Output_StageD  output_stageD = ?;

      // This stage is empty
      if (! rg_full) begin
	 output_stageD.ostatus = OSTATUS_EMPTY;
      end
      else begin
	 output_stageD.ostatus        = OSTATUS_PIPE;
	 output_stageD.data_to_stage1 = Data_StageD_to_Stage1 {pc:             rg_data.pc,
`ifdef RVFI_DII
							       instr_seq: rg_data.instr_seq,
`endif
							       priv:           rg_data.priv,
							       epoch:          rg_data.epoch,
							       is_i32_not_i16: rg_data.is_i32_not_i16,
							       exc:            rg_data.exc,
							       exc_code:       rg_data.exc_code,
							       tval:           rg_data.tval,
							       instr:          instr,
`ifdef NEW_BYPASS
                                                               rs1_val: rs1_val,
                                                               rs2_val: rs2_val,
`endif
`ifdef ISA_C
`ifdef NEW_BYPASS
							       instr_C:        ?,
`else
							       instr_C:        instr_C,
`endif
`endif
							       pred_pc:        rg_data.pred_pc,
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
