// Copyright (c) 2016-2019 Bluespec, Inc. All Rights Reserved

package CPU_StageF;

// ================================================================
// This is Stage F ("fetch") of the "Flute_V3" CPU.

// ================================================================
// Exports

export
CPU_StageF_IFC (..),
mkCPU_StageF;

// ================================================================
// BSV library imports

import FIFOF        :: *;
import GetPut       :: *;
import ClientServer :: *;
import DReg         :: *;

// ----------------
// BSV additional libs

import Cur_Cycle :: *;

// ================================================================
// Project imports

import ISA_Decls         :: *;
import CPU_Globals       :: *;
import Near_Mem_IFC      :: *;
import Branch_Predictor  :: *;

`ifdef RVFI_DII
import RVFI_DII          :: *;
`endif

`ifdef NEW_REG
import ISA_Decls :: *;
import CPU_Decode_C :: *;
import Forwarding_RegFile :: *;
`endif

// ================================================================
// Interface

interface CPU_StageF_IFC;
   // ---- Reset
   interface Server #(Token, Token) server_reset;

   // ---- Output
   (* always_ready *)
   method Output_StageF out;

   (* always_ready *)
   method Action deq;

   // ---- Input
   (* always_ready *)
   method Action enq (Epoch            epoch,
		      WordXL           pc,
		      Priv_Mode        priv,
`ifdef RVFI_DII
                      Dii_Id           next_seq,
`endif
		      Bit #(1)         sstatus_SUM,
		      Bit #(1)         mstatus_MXR,
		      WordXL           satp);

   (* always_ready *)
   method Action bp_train (WordXL   pc,
			   Bool     is_i32_not_i16,
			   Instr    instr,
			   CF_Info  cf_info);

   (* always_ready *)
   method Action set_full (Bool full);

   (* always_ready *)
   method Action invalidate (Bool invalid);
endinterface

// ================================================================
// Implementation module

module mkCPU_StageF #(Bit #(4)  verbosity,
`ifdef NEW_REG
                      ForwardingPipelinedRegFileIFC #(Word, RegName, 4) gpr_regfile,
                      MISA misa,
`endif
		      IMem_IFC  imem)
                    (CPU_StageF_IFC);

   FIFOF #(Token)  f_reset_reqs <- mkFIFOF;
   FIFOF #(Token)  f_reset_rsps <- mkFIFOF;

   Wire #(Bool)      dw_redirecting <- mkDWire (False);
`ifdef NEW_PIPE_LOGIC
   FIFOF #(void)     f_invalidated <- mkUGFIFOF1;
   //Reg #(Bool)      rg_invalidated[2]  <- mkCReg (2, False);
`endif

   Reg #(Bool)       rg_full  <- mkReg (False);
   Reg #(Epoch)      rg_epoch <- mkReg (0);               // Toggles on redirections
   Reg #(Priv_Mode)  rg_priv  <- mkRegU;

   //Branch_Predictor_IFC branch_predictor <- mkBranch_Predictor;

   // ----------------------------------------------------------------
   // BEHAVIOR

   rule rl_reset;
      f_reset_reqs.deq;
      rg_full  <= False;
      rg_epoch <= 0;
      f_reset_rsps.enq (?);
   endrule

`ifdef NEW_REG
   let decode_c_wrapper <- mkDecodeC;
   Bit #(2) xl = ((xlen == 32) ? misa_mxl_32 : misa_mxl_64);
   rule assign_decode_c_inputs;
`ifdef RVFI_DII
      decode_c_wrapper.put_inputs(misa, xl, tpl_1(imem.instr)[15:0]);
`else
      decode_c_wrapper.put_inputs(misa, xl, imem.instr[15:0]);

`endif
   endrule

   let decode_wrapper <- mkDecode;
   rule assign_decode_inputs;
`ifdef RVFI_DII
      decode_wrapper.put_inputs(tpl_1(imem.instr));
`else
      decode_wrapper.put_inputs(imem.instr);
`endif
   endrule

   let instr_decoded = decode_wrapper.get_outputs;
   rule rl_stagef_regfile_behaviour;
      let instr_decomp = decode_c_wrapper.get_outputs;
`ifdef RVFI_DII
      let instr = imem.is_i32_not_i16 ? tpl_1(imem.instr) : instr_decomp;
`else
      let instr = imem.is_i32_not_i16 ? imem.instr : instr_decomp;
`endif

      
      if (imem.valid) begin
      end
   endrule
`endif // NEW_REG

   // ----------------
   // Combinational output function

   function Output_StageF fv_out;
`ifdef RVFI_DII
      let imem_instr = tpl_1(imem.instr);
`else
      let imem_instr = imem.instr;
`endif

      //let pred_pc = branch_predictor.predict_rsp (imem.is_i32_not_i16, imem_instr);
      let pred_pc = imem.pc + (imem.is_i32_not_i16 ? 4 : 2);
      let d = Data_StageF_to_StageD {pc:              imem.pc,
				     epoch:           rg_epoch,
				     priv:            rg_priv,
				     is_i32_not_i16:  imem.is_i32_not_i16,
				     exc:             imem.exc,
				     exc_code:        imem.exc_code,
				     tval:            imem.tval,
				     instr:           imem_instr,
`ifdef NEW_PIPE_LOGIC
                                     invalid:         f_invalidated.notEmpty,
`endif
`ifdef RVFI_DII
                                     instr_seq:       tpl_2(imem.instr),
`endif
				     pred_pc:         pred_pc};

      let ostatus = ((! rg_full) ? OSTATUS_EMPTY
`ifdef NEW_PIPE_LOGIC
                     : (f_invalidated.notEmpty) ? OSTATUS_NOP
`endif
		     : (  (! imem.valid) ? OSTATUS_BUSY
			: OSTATUS_PIPE));                    // instr or exception

      let output_stageF = Output_StageF {ostatus: ostatus, data_to_stageD: d};

      return output_stageF;
   endfunction: fv_out

   // ================================================================
   // INTERFACE

   // ---- Reset
   interface server_reset = toGPServer (f_reset_reqs, f_reset_rsps);

   // ---- Output
   method Output_StageF out;
      return fv_out;
   endmethod

// TODO deal with floating-point ops
// TODO deal with A extension ops
   method Action deq ();
`ifdef NEW_REG
      // TODO do we actually need to check imem.valid?
      if (imem.valid
`ifdef NEW_PIPE_LOGIC
          && !f_invalidated.notEmpty
`endif
         ) begin
`ifdef RVFI_DII
         $display ("instr: 0x%0h", tpl_1(imem.instr));
`else
         $display ("instr: 0x%0h", imem.instr);
`endif
         $display ("making a register file request to addresses x%0d and x%0d",
                   instr_decoded.rs1,
                   instr_decoded.rs2);
         $display ("write address: x%0d", instr_decoded.rd);
         WriteType writetype;
         if (f_invalidated.notEmpty) begin
            writetype = None;
         end else
         if (  (instr_decoded.opcode == op_JAL)
            || (instr_decoded.opcode == op_JALR)
            || (instr_decoded.opcode == op_OP && !f7_is_OP_MUL_DIV_REM (instr_decoded.funct7))
`ifdef RV64
            || (instr_decoded.opcode == op_OP_32 && !f7_is_OP_MUL_DIV_REM (instr_decoded.funct7))
`endif
            || (instr_decoded.opcode == op_OP_IMM)
`ifdef RV64
            || (instr_decoded.opcode == op_OP_IMM_32)
`endif
            || (instr_decoded.opcode == op_LUI)
            || (instr_decoded.opcode == op_AUIPC)
            || (instr_decoded.opcode == op_SYSTEM && f3_is_CSRR_W (instr_decoded.funct3))
            || (instr_decoded.opcode == op_SYSTEM && f3_is_CSRR_S_or_C (instr_decoded.funct3))
            ) begin
            writetype = Simple;
         end else if (  (instr_decoded.opcode == op_LOAD)
                     || (instr_decoded.opcode == op_OP && f7_is_OP_MUL_DIV_REM (instr_decoded.funct7))
`ifdef RV64
                     || (instr_decoded.opcode == op_OP_32 && f7_is_OP_MUL_DIV_REM (instr_decoded.funct7))
`endif
                     ) begin
            writetype = Pending;
         end else if (  (instr_decoded.opcode == op_BRANCH)
                     || (instr_decoded.opcode == op_STORE)
                     || (instr_decoded.opcode == op_MISC_MEM)
                     ) begin
            writetype = None;
         end else begin
            $display("unrecognized instruction encountered; telling regfile that there will be no write");
            writetype = None;
         end


         gpr_regfile.reqRegs(ReadReq {
            //epoch: ((instr_decoded.opcode == op_JAL || instr_decoded.opcode == op_JALR) ? rg_epoch : rg_epoch+1),
            //epoch: rg_epoch,
            epoch: 0,
            a: instr_decoded.rs1,
            b: instr_decoded.rs2,
            // TODO make this accurate for stuff
            write: writetype,
            dest: instr_decoded.rd,
            // TODO might have to do debug stuff later
            fromDebug: False,
            rawReq: False
         });
      end
`endif

`ifdef NEW_PIPE_LOGIC
      if (f_invalidated.notEmpty) begin
         f_invalidated.deq;
      end
`endif
   endmethod

   // ---- Input
   method Action enq (Epoch            epoch,
		      WordXL           pc,
		      Priv_Mode        priv,
`ifdef RVFI_DII
                      Dii_Id           next_seq,
`endif
		      Bit #(1)         sstatus_SUM,
		      Bit #(1)         mstatus_MXR,
		      WordXL           satp);
      if (verbosity > 1) begin
	 $write ("    %m.enq:  pc:0x%0h  epoch:%0d  priv:%0d",     pc, epoch, priv);
	 $write ("  sstatus_SUM:%0d  mstatus_MXR:%0d  satp:0x%0h",
		 sstatus_SUM, mstatus_MXR, satp);
	 $display ("");
      end

      imem.req (f3_LW, pc, priv, sstatus_SUM, mstatus_MXR, satp
`ifdef RVFI_DII
                                                               , next_seq
`endif
                                                               );
      //branch_predictor.predict_req (pc);    // TODO: ASID.VA vs PA?

      rg_epoch <= epoch;
      rg_priv  <= priv;
      //rg_invalidated[0] <= False;
   endmethod

   method Action bp_train (WordXL   pc,
			   Bool     is_i32_not_i16,
			   Instr    instr,
			   CF_Info  cf_info);
      //branch_predictor.bp_train (pc, is_i32_not_i16, instr, cf_info);
   endmethod

   method Action set_full (Bool full);
      rg_full <= full;
   endmethod

`ifdef NEW_PIPE_LOGIC
   method Action invalidate (Bool invalid);
      f_invalidated.enq (?);
   endmethod
`endif
endmodule

// ================================================================

endpackage
