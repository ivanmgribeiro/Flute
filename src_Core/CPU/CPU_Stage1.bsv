// Copyright (c) 2016-2019 Bluespec, Inc. All Rights Reserved

package CPU_Stage1;

// ================================================================
// This is Stage 1 of the "Flute" CPU.
// It contains the EX functionality.
// EX: "Execute"

// ================================================================
// Exports

export
CPU_Stage1_IFC (..),
mkCPU_Stage1;

// ================================================================
// BSV library imports

import FIFOF        :: *;
import GetPut       :: *;
import ClientServer :: *;
import ConfigReg    :: *;
import DReg         :: *;

// ----------------
// BSV additional libs

import Cur_Cycle :: *;

// ================================================================
// Project imports

import ISA_Decls        :: *;
import CPU_Globals      :: *;
import Near_Mem_IFC     :: *;
import GPR_RegFile      :: *;
`ifdef ISA_F
import FPR_RegFile      :: *;
`endif
import CSR_RegFile      :: *;
import EX_ALU_functions :: *;
`ifdef NEW_REG
import Forwarding_RegFile :: *;
`endif

`ifdef ISA_C
// 'C' extension (16b compressed instructions)
import CPU_Decode_C     :: *;
`endif

import CPU_Stage1_syn :: *;

// ================================================================
// Interface

interface CPU_Stage1_IFC;
   // ---- Reset
   interface Server #(Token, Token) server_reset;

   // ---- Output
   (* always_ready *)
   method Output_Stage1 out;

   (* always_ready *)
   method Action deq;

   // ---- Input
   (* always_ready *)
   method Action enq (Data_StageD_to_Stage1  data);

   (* always_ready *)
   method Action set_full (Bool full);

   (* always_ready *)
   method Action invalidate (Bool invalid);
endinterface

// ================================================================
// Implementation module

(* synthesize *)
module mkRegUSynth_Dto1 (Reg#(Data_StageD_to_Stage1));
    let rg <- mkRegU;
    return rg;
endmodule


module mkCPU_Stage1 #(Bit #(4)         verbosity,
`ifdef NEW_REG
                      ForwardingPipelinedRegFileIFC #(Word, RegName, 4) gpr_regfile,
`else
		      GPR_RegFile_IFC  gpr_regfile,
`endif
		      Bypass           bypass_from_stage2,
		      Bypass           bypass_from_stage3,
`ifdef ISA_F
		      FPR_RegFile_IFC  fpr_regfile,
		      FBypass          fbypass_from_stage2,
		      FBypass          fbypass_from_stage3,
`endif
		      CSR_RegFile_IFC  csr_regfile,
		      Epoch            cur_epoch,
		      Priv_Mode        cur_priv)
                    (CPU_Stage1_IFC);

   FIFOF #(Token) f_reset_reqs <- mkFIFOF;
   FIFOF #(Token) f_reset_rsps <- mkFIFOF;

   Reg #(Bool)                  rg_full        <- mkReg (False);
   Reg #(Data_StageD_to_Stage1) rg_stage_input <- mkRegUSynth_Dto1;

   MISA misa   = csr_regfile.read_misa;
   Bit #(2) xl = ((xlen == 32) ? misa_mxl_32 : misa_mxl_64);

`ifdef NEW_PIPE_LOGIC
   FIFOF #(Bool)          f_invalidated <- mkUGFIFOF1;
`endif

`ifdef NEW_REG
   Wire #(Output_Stage1) dw_out <- mkDWire (?);
`endif

   // ----------------------------------------------------------------
   // BEHAVIOR

   rule rl_reset;
      f_reset_reqs.deq;
      rg_full <= False;
      $display("stage1 resetting");
      f_reset_rsps.enq (?);
   endrule

   // ----------------
   // ALU

   let decoded_instr  = rg_stage_input.decoded_instr;
   let funct3         = decoded_instr.funct3;

`ifdef NEW_REG
   Wire #(Bool) dw_reg_is_ready <- mkDWire (False);
   Wire #(Word) dw_rs1_val_bypassed <- mkDWire (?); 
   Wire #(Word) dw_rs2_val_bypassed <- mkDWire (?); 

   /*
   rule rl_stage1_debug;
      $display("full? ", fshow(rg_full));
      $display(fshow(rg_stage_input));
   endrule
   */

   rule rl_stage1_read_gpr;
      $display("reading gpr values");
      dw_reg_is_ready <= gpr_regfile.reg_is_ready;
      if (rg_stage_input.decoded_instr.rs1 != 0) begin
         dw_rs1_val_bypassed <= gpr_regfile.readRegs.regA;
      end else begin
         dw_rs1_val_bypassed <= 0;
      end
      if (rg_stage_input.decoded_instr.rs2 != 0) begin
         dw_rs2_val_bypassed <= gpr_regfile.readRegs.regB;
      end else begin
         dw_rs2_val_bypassed <= 0;
      end
   endrule


   //Wire #(ALU_Inputs) dw_alu_inputs <- mkDWire (?);

   let alu_wrapper <- mkALU;
   let stage1_wrapper <- mkCPU_Stage1_syn;

   //rule rl_stage1_reg_is_ready;
   //   dw_reg_is_ready <= gpr_regfile.reg_is_ready;
   //endrule
   //(* no_implicit_conditions *)
   //rule rl_stage1_read_gpr;
   //   dw_reg_is_ready <= gpr_regfile.reg_is_ready;
   //   $display("current instruction: 0x%0h", rg_stage_input.instr);
   //   $display("is regfile ready?: ", gpr_regfile.reg_is_ready);
   //   if (rg_full && gpr_regfile.reg_is_ready) begin
   //      ReadRegs #(Word) read_regs = gpr_regfile.readRegs();
   //      if (rg_stage_input.decoded_instr.rs1 != 0) begin
   //      end
   //      if (rg_stage_input.decoded_instr.rs2 != 0) begin
   //         dw_rs1_val_bypassed <= read_regs.regA;
   //         dw_rs2_val_bypassed <= read_regs.regB;
   //      end
   //      $display("read in bypassed value for reg 1: 0x%0h", read_regs.regA);
   //      $display("read in bypassed value for reg 2: 0x%0h", read_regs.regB);
   //   end
   //endrule

   rule assign_alu_inputs;
      // ALU function
      let alu_inputs = ALU_Inputs {cur_priv       : cur_priv,
				   pc             : rg_stage_input.pc,
				   fallthru_pc    : rg_stage_input.pred_pc,
				   is_i32_not_i16 : rg_stage_input.is_i32_not_i16,
				   instr          : rg_stage_input.instr,
`ifdef INCLUDE_TANDEM_VERIF
`ifdef ISA_C
				   instr_C        : rg_stage_input.instr_C,
`endif
`endif
				   decoded_instr  : rg_stage_input.decoded_instr,
				   rs1_val        : dw_rs1_val_bypassed,
				   rs2_val        : dw_rs2_val_bypassed,
`ifdef ISA_F
				   frs1_val       : frs1_val_bypassed,
				   frs2_val       : frs2_val_bypassed,
				   frs3_val       : frs3_val_bypassed,
				   frm            : csr_regfile.read_frm,
`ifdef INCLUDE_TANDEM_VERIF
                                   fflags         : csr_regfile.read_fflags,
`endif
`endif
				   mstatus        : csr_regfile.read_mstatus,
				   misa           : csr_regfile.read_misa };
      //dw_alu_inputs <= alu_inputs;
      alu_wrapper.put_inputs(alu_inputs);
   endrule

   rule assign_stage1_inputs;
      $display("rl stage1_inputs: ", fshow(rg_stage_input));
      stage1_wrapper.put_inputs(rg_full,
`ifdef NEW_PIPE_LOGIC
                                f_invalidated.notEmpty,
`endif
                                rg_stage_input,
                                cur_epoch,
                                //!gpr_regfile.reg_is_ready,
                                !dw_reg_is_ready,
                                dw_rs1_val_bypassed,
                                //!gpr_regfile.reg_is_ready,
                                !dw_reg_is_ready,
                                dw_rs2_val_bypassed,
`ifdef ISA_F
                                frs1_busy,
                                frs2_busy,
                                frs3_busy,
`endif
                                alu_wrapper.get_outputs,
                                cur_priv);
   endrule



   let stage1_outputs = stage1_wrapper.get_outputs;
   rule rl_stage1_behaviour;
      dw_out <= stage1_outputs;
   endrule


   // TODO Word -> WordXL when other stuff gets updated as well
`else // end ifdef NEW_REG
   // Register rs1 read and bypass
   let rs1 = decoded_instr.rs1;
   let rs1_val = gpr_regfile.read_rs1 (rs1);
   match { .busy1a, .rs1a } = fn_gpr_bypass (bypass_from_stage3, rs1, rs1_val);
   match { .busy1b, .rs1b } = fn_gpr_bypass (bypass_from_stage2, rs1, rs1a);
   Bool rs1_busy = (busy1a || busy1b);
   Word rs1_val_bypassed = ((rs1 == 0) ? 0 : rs1b);

   // Register rs2 read and bypass
   let rs2 = decoded_instr.rs2;
   let rs2_val = gpr_regfile.read_rs2 (rs2);
   match { .busy2a, .rs2a } = fn_gpr_bypass (bypass_from_stage3, rs2, rs2_val);
   match { .busy2b, .rs2b } = fn_gpr_bypass (bypass_from_stage2, rs2, rs2a);
   Bool rs2_busy = (busy2a || busy2b);
   Word rs2_val_bypassed = ((rs2 == 0) ? 0 : rs2b);

`ifdef ISA_F
   // FP Register rs1 read and bypass
   let frs1_val = fpr_regfile.read_rs1 (rs1);
   match { .fbusy1a, .frs1a } = fn_fpr_bypass (fbypass_from_stage3, rs1, frs1_val);
   match { .fbusy1b, .frs1b } = fn_fpr_bypass (fbypass_from_stage2, rs1, frs1a);
   Bool frs1_busy = (fbusy1a || fbusy1b);
   WordFL frs1_val_bypassed = frs1b;

   // FP Register rs2 read and bypass
   let frs2_val = fpr_regfile.read_rs2 (rs2);
   match { .fbusy2a, .frs2a } = fn_fpr_bypass (fbypass_from_stage3, rs2, frs2_val);
   match { .fbusy2b, .frs2b } = fn_fpr_bypass (fbypass_from_stage2, rs2, frs2a);
   Bool frs2_busy = (fbusy2a || fbusy2b);
   WordFL frs2_val_bypassed = frs2b;

   // FP Register rs3 read and bypass
   let rs3 = decoded_instr.rs3;
   let frs3_val = fpr_regfile.read_rs3 (rs3);
   match { .fbusy3a, .frs3a } = fn_fpr_bypass (fbypass_from_stage3, rs3, frs3_val);
   match { .fbusy3b, .frs3b } = fn_fpr_bypass (fbypass_from_stage2, rs3, frs3a);
   Bool frs3_busy = (fbusy3a || fbusy3b);
   WordFL frs3_val_bypassed = frs3b;
`endif

   // ALU function
   let alu_inputs = ALU_Inputs {cur_priv       : cur_priv,
				pc             : rg_stage_input.pc,
				fallthru_pc        : rg_stage_input.pred_pc,
				is_i32_not_i16 : rg_stage_input.is_i32_not_i16,
				instr          : rg_stage_input.instr,
`ifdef INCLUDE_TANDEM_VERIF
`ifdef ISA_C
				instr_C        : rg_stage_input.instr_C,
`endif
`endif
				decoded_instr  : rg_stage_input.decoded_instr,
				rs1_val        : rs1_val_bypassed,
				rs2_val        : rs2_val_bypassed,
`ifdef ISA_F
				frs1_val       : frs1_val_bypassed,
				frs2_val       : frs2_val_bypassed,
				frs3_val       : frs3_val_bypassed,
				frm            : csr_regfile.read_frm,
`ifdef INCLUDE_TANDEM_VERIF
                                fflags         : csr_regfile.read_fflags,
`endif
`endif
				mstatus        : csr_regfile.read_mstatus,
				misa           : csr_regfile.read_misa };

   ALU_IFC alu_wrapper <- mkALU;
   //let alu_outputs = fv_ALU (alu_inputs);
   //ALU_Outputs alu_outputs <- alu_unique_wrapper.func(alu_inputs);
   let alu_outputs = alu_wrapper.get_outputs;

   rule assign_alu_inputs;
      alu_wrapper.put_inputs(alu_inputs);
   endrule


   // ----------------
   // Combinational output function

   let stage1_wrapper <- mkCPU_Stage1_syn;

   rule assign_stage1_inputs;
      stage1_wrapper.put_inputs(rg_full,
`ifdef NEW_PIPE_LOGIC
                                f_invalidated.notEmpty,
`endif
                                rg_stage_input,
                                cur_epoch,
                                rs1_busy,
                                rs1_val_bypassed,
                                rs2_busy,
                                rs2_val_bypassed,
`ifdef ISA_F
                                frs1_busy,
                                frs2_busy,
                                frs3_busy,
`endif
                                alu_outputs,
                                cur_priv);
   endrule

   let fv_out = stage1_wrapper.get_outputs;
`endif // end `else clause of ifdef NEW_REG


   // ================================================================
   // INTERFACE

   // ---- Reset
   interface server_reset = toGPServer (f_reset_reqs, f_reset_rsps);

   // ---- Output
   method Output_Stage1 out;
`ifdef NEW_REG
      return dw_out;
`else
      return fv_out;
`endif
   endmethod

   method Action deq ();
`ifdef NEW_REG
      //if (gpr_regfile.reg_is_ready) begin
      $display("stage1 deq: dw_reg_is_ready: ", fshow(dw_reg_is_ready));
      if (dw_reg_is_ready && stage1_outputs.ostatus != OSTATUS_NONPIPE) begin
         if (verbosity > 1) begin
            $display("writeRegSpeculative: addr x%0d, val 0x%0h, instruction 0x%0h",
                      rg_stage_input.decoded_instr.rd,
                      stage1_outputs.data_to_stage2.val1,
                      rg_stage_input.instr);
         end
         gpr_regfile.writeRegSpeculative(stage1_outputs.data_to_stage2.val1, ?);
      end
`endif
   endmethod

   // ---- Input
   method Action enq (Data_StageD_to_Stage1  data);
      rg_stage_input <= data;
`ifdef NEW_PIPE_LOGIC
      if (f_invalidated.notEmpty) begin
         f_invalidated.deq;
      end
`endif
      if (verbosity > 1)
	 $display ("    CPU_Stage1.enq: 0x%08h", data.pc);
   endmethod

   method Action set_full (Bool full);
      if (verbosity > 1)
         $display ("stage1 setfull to ", fshow(full));
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
