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
endinterface

// ================================================================
// Implementation module

(* synthesize *)
module mkRegUSynth_Dto1 (Reg#(Data_StageD_to_Stage1));
    let rg <- mkRegU;
    return rg;
endmodule


module mkCPU_Stage1 #(Bit #(4)         verbosity,
		      GPR_RegFile_IFC  gpr_regfile,
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
`ifdef NEW_BYPASS
   Reg #(WordXL) rg_rs1_val <- mkRegU;
   Reg #(WordXL) rg_rs2_val <- mkRegU;
   Reg #(Bool) rg_rs1_busy <- mkReg (False);
   Reg #(Bool) rg_rs2_busy <- mkReg (False);

   Wire #(RegName) dw_rs1 <- mkDWire (0);
   Wire #(RegName) dw_rs2 <- mkDWire (0);
`endif

   MISA misa   = csr_regfile.read_misa;
   Bit #(2) xl = ((xlen == 32) ? misa_mxl_32 : misa_mxl_64);

   // ----------------------------------------------------------------
   // BEHAVIOR

   rule rl_reset;
      f_reset_reqs.deq;
      rg_full <= False;
      f_reset_rsps.enq (?);
   endrule

   // ----------------
   // ALU

   let decoded_instr  = rg_stage_input.decoded_instr;
   let funct3         = decoded_instr.funct3;

`ifdef NEW_BYPASS
   Bool rs1_busy = rg_rs1_busy;
   Word rs1_val_bypassed = rg_rs1_val;

   Bool rs2_busy = rg_rs2_busy;
   Word rs2_val_bypassed = rg_rs2_val;
`else
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
`endif


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
`ifdef ISA_C
				instr_C        : rg_stage_input.instr_C,
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

`ifdef NEW_BYPASS
   rule rl_stage1_forwarding (rg_rs1_busy || rg_rs2_busy);
      let decoded_instr = rg_stage_input.decoded_instr;
      let rs1 = rg_stage_input.decoded_instr.rs1;
      let rs2 = rg_stage_input.decoded_instr.rs2;

      // TODO this might not be right, since the values we read from the
      // GPR on enq might get overwritten by bypass logic
      // however, it should be right
      let rs1_val = rg_rs1_val;
      let rs2_val = rg_rs2_val;

      // TODO this bypassing logic will be replicated
      match { .busy1a, .rs1a } = fn_gpr_bypass (bypass_from_stage3, rs1, rs1_val);
      match { .busy1b, .rs1b } = fn_gpr_bypass (bypass_from_stage2, rs1, rs1a);

      match { .busy2a, .rs2a } = fn_gpr_bypass (bypass_from_stage3, rs2, rs2_val);
      match { .busy2b, .rs2b } = fn_gpr_bypass (bypass_from_stage2, rs2, rs2a);

      rg_rs1_val <= (rs1 != 0) ? rs1b : 0;
      rg_rs2_val <= (rs2 != 0) ? rs2b : 0;
      rg_rs1_busy <= busy1a || busy1b;
      rg_rs2_busy <= busy2a || busy2b;
      if (verbosity > 1) begin
         $display ("    CPU_Stage1 rl_stage1_forwarding: pc: 0x%08h, instr: 0x%0h", rg_stage_input.pc, rg_stage_input.instr);
         $display ("      rs1: %0d", rs1);
         $display ("      rs1a: %0h", rs1a);
         $display ("      rg_rs1_val write: %0h", (rs1 != 0) ? rs1b : 0);
         $display ("      rg_rs1_busy write: ", fshow(busy1a || busy1b));
         $display ("      rs2: %0d", rs2);
         $display ("      rs2a: %0h", rs2a);
         $display ("      rg_rs2_val write: %0h", (rs2 != 0) ? rs2b : 0);
         $display ("      rg_rs2_busy write: ", fshow(busy2a || busy2b));
         $display ("      rd: %0d", decoded_instr.rd);
      end
   endrule
`endif


   // ----------------
   // Combinational output function

   let stage1_wrapper <- mkCPU_Stage1_syn;

   rule assign_stage1_inputs;
   stage1_wrapper.put_inputs(rg_full,
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

   // ================================================================
   // INTERFACE

   // ---- Reset
   interface server_reset = toGPServer (f_reset_reqs, f_reset_rsps);

   // ---- Output
   method Output_Stage1 out;
      return fv_out;
   endmethod

   method Action deq ();
   endmethod

   // ---- Input
   method Action enq (Data_StageD_to_Stage1  data) if (!(rg_rs1_busy || rg_rs2_busy));
`ifdef NEW_BYPASS
      let decoded_instr = data.decoded_instr;
      let rs1 = data.decoded_instr.rs1;
      let rs2 = data.decoded_instr.rs2;

      let rs1_val = gpr_regfile.read_rs1 (rs1);
      let rs2_val = gpr_regfile.read_rs2 (rs2);

      match { .busy1a, .rs1a } = fn_gpr_bypass (bypass_from_stage3, rs1, rs1_val);
      match { .busy1b, .rs1b } = fn_gpr_bypass (bypass_from_stage2, rs1, rs1a);

      match { .busy2a, .rs2a } = fn_gpr_bypass (bypass_from_stage3, rs2, rs2_val);
      match { .busy2b, .rs2b } = fn_gpr_bypass (bypass_from_stage2, rs2, rs2a);

      let rs1c = rs1b;
      let rs2c = rs2b;
      let busy1c = False;
      let busy2c = False;
      if (rg_full && fv_out.ostatus == OSTATUS_PIPE) begin
         if (fv_out.data_to_stage2.op_stage2 == OP_Stage2_ST) begin

         end
         else if (fv_out.data_to_stage2.op_stage2 == OP_Stage2_ALU) begin
            //if (rs1 == rg_stage_input.decoded_instr.rd) begin
            if (rs1 == fv_out.data_to_stage2.rd) begin
               rs1c = fv_out.data_to_stage2.val1;
            end
            //if (rs2 == rg_stage_input.decoded_instr.rd) begin
            if (rs2 == fv_out.data_to_stage2.rd) begin
               rs2c = fv_out.data_to_stage2.val1;
            end
         end
         else begin
            if (rs1 == rg_stage_input.decoded_instr.rd) begin
               busy1c = True;
            end
            if (rs2 == rg_stage_input.decoded_instr.rd) begin
               busy2c = True;
            end
         end
      end

      rg_rs1_val <= (rs1 != 0) ? rs1c : 0;
      rg_rs2_val <= (rs2 != 0) ? rs2c : 0;
      rg_rs1_busy <= busy1a || busy1b || busy1c;
      rg_rs2_busy <= busy2a || busy2b || busy2c;
`endif

      rg_stage_input <= data;
`ifdef NEW_BYPASS
      if (verbosity > 1) begin
         $display ("    CPU_Stage1.enq: pc: 0x%08h, instr: 0x%0h", data.pc, data.instr);
         $display ("      rs1: %0d", rs1);
         $display ("      rg_rs1_val write: %0h", (rs1 != 0) ? rs1c : 0);
         $display ("      rg_rs1_busy write: ", fshow(busy1a || busy1b || busy1c));
         $display ("      rs2: %0d", rs2);
         $display ("      rg_rs2_val write: %0h", (rs2 != 0) ? rs2c : 0);
         $display ("      rg_rs2_busy write: ", fshow(busy2a || busy2b || busy2c));
         $display ("      rd: %0d", decoded_instr.rd);
      end
`endif
   endmethod

   method Action set_full (Bool full);
      rg_full <= full;
   endmethod
endmodule

// ================================================================

endpackage
