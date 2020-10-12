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

`ifdef ISA_CHERI
import CHERICap :: *;
import CHERICC_Fat :: *;
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

module mkCPU_Stage1 #(Bit #(4)         verbosity,
		      GPR_RegFile_IFC  gpr_regfile,
		      Bypass           bypass_from_stage2,
		      Bypass           bypass_from_stage3,
`ifdef ISA_CHERI
                      PCC_T            fresh_pcc,
                      CapPipe          ddc,
`endif
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

`ifdef ISA_CHERI
   Reg #(PCC_T) rg_pcc <- mkRegU;
   RWire#(PCC_T) rw_next_pcc <- mkRWire;
   RWire#(PCC_T) rw_fresh_pcc <- mkRWire;
`endif

   Reg #(Bool)                  rg_full        <- mkReg (False);
   Reg #(Data_StageD_to_Stage1) rg_stage_input <- mkRegU;
`ifdef NEW_BYPASS
`ifdef ISA_CHERI
   Reg #(CapPipe) rg_rs1_val <- mkConfigRegU;
   Reg #(CapPipe) rg_rs2_val <- mkConfigRegU;
`else
   Reg #(WordXL) rg_rs1_val <- mkConfigRegU;
   Reg #(WordXL) rg_rs2_val <- mkConfigRegU;
`endif // ISA_CHERI
   Reg #(Bool) rg_read_rs1_from_regfile <- mkConfigReg (False);
   Reg #(Bool) rg_read_rs2_from_regfile <- mkConfigReg (False);
   Reg #(Bool) rg_rs1_busy <- mkConfigReg (False);
   Reg #(Bool) rg_rs2_busy <- mkConfigReg (False);

   Wire #(RegName) dw_rs1 <- mkDWire (0);
   Wire #(RegName) dw_rs2 <- mkDWire (0);
`endif // NEW_BYPASS

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
   let rs1 = decoded_instr.rs1;
   let rs1_val_from_regfile = gpr_regfile.read_rs1 (rs1);
   Bool rs1_busy = rg_rs1_busy;
   let rs1_val_bypassed = rg_read_rs1_from_regfile ? rs1_val_from_regfile : rg_rs1_val;

   let rs2 = decoded_instr.rs2;
   let rs2_val_from_regfile = gpr_regfile.read_rs2 (rs2);
   Bool rs2_busy = rg_rs2_busy;
   let rs2_val_bypassed = rg_read_rs2_from_regfile ? rs2_val_from_regfile : rg_rs2_val;
`else // not NEW_BYPASS
   // Register rs1 read and bypass
   let rs1 = decoded_instr.rs1;
   let rs1_val = gpr_regfile.read_rs1 (rs1);
   match { .busy1a, .rs1a } = fn_gpr_bypass (bypass_from_stage3, rs1, rs1_val);
   match { .busy1b, .rs1b } = fn_gpr_bypass (bypass_from_stage2, rs1, rs1a);
   Bool rs1_busy = (busy1a || busy1b);
`ifdef ISA_CHERI
   CapPipe rs1_val_bypassed = ((rs1 == 0) ? nullCap : rs1b);
`else
   Word rs1_val_bypassed = ((rs1 == 0) ? 0 : rs1b);
`endif

   // Register rs2 read and bypass
   let rs2 = decoded_instr.rs2;
   let rs2_val = gpr_regfile.read_rs2 (rs2);
   match { .busy2a, .rs2a } = fn_gpr_bypass (bypass_from_stage3, rs2, rs2_val);
   match { .busy2b, .rs2b } = fn_gpr_bypass (bypass_from_stage2, rs2, rs2a);
   Bool rs2_busy = (busy2a || busy2b);
`ifdef ISA_CHERI
   CapPipe rs2_val_bypassed = ((rs2 == 0) ? nullCap : rs2b);
`else
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
`endif // not NEW_BYPASS

   // ALU function
   let alu_inputs = ALU_Inputs {cur_priv       : cur_priv,
`ifdef ISA_CHERI
				pcc            : rg_pcc,
				ddc            : ddc,
`else
				pc             : rg_stage_input.pc,
`endif
				is_i32_not_i16 : rg_stage_input.is_i32_not_i16,
				instr          : rg_stage_input.instr,
`ifdef ISA_C
				instr_C        : rg_stage_input.instr_C,
`endif
				decoded_instr  : rg_stage_input.decoded_instr,
`ifdef ISA_CHERI
				cap_rs1_val    : rs1_val_bypassed,
				cap_rs2_val    : rs2_val_bypassed,
				rs1_idx        : rs1,
				rs2_idx        : rs2,
				rs1_val        : getAddr(rs1_val_bypassed),
				rs2_val        : getAddr(rs2_val_bypassed),
`else
				rs1_val        : rs1_val_bypassed,
				rs2_val        : rs2_val_bypassed,
`endif
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

   let alu_syn <- mk_ALU (alu_inputs);
   let alu_outputs = alu_syn.alu_outputs;

`ifdef NEW_BYPASS
`ifdef DEDUPLICATE_BYPASS
   let bypass_wrapper_1a <- mkUniqueWrapper3(fn_gpr_bypass);
   let bypass_wrapper_2a <- mkUniqueWrapper3(fn_gpr_bypass);
   let bypass_wrapper_1b <- mkUniqueWrapper3(fn_gpr_bypass);
   let bypass_wrapper_2b <- mkUniqueWrapper3(fn_gpr_bypass);
`endif

   Reg #(Int #(64)) stalls <- mkReg (0);
   rule rl_stage1_forwarding (rg_rs1_busy || rg_rs2_busy);
      if (verbosity > 0) begin
         $display("stage1 stalled ", fshow(stalls));
         stalls <= stalls + 1;
      end
      let decoded_instr = rg_stage_input.decoded_instr;
      let rs1 = rg_stage_input.decoded_instr.rs1;
      let rs2 = rg_stage_input.decoded_instr.rs2;

`ifdef DELAY_REGFILE_READ
      let rs1_val = rs1_val_from_regfile;
      let rs2_val = rs2_val_from_regfile;
`else
      let rs1_val = rg_rs1_val;
      let rs2_val = rg_rs2_val;
`endif

`ifdef DEDUPLICATE_BYPASS
      match { .busy1a, .rs1a } <- bypass_wrapper_1a.func (bypass_from_stage3, rs1, rs1_val);
      match { .busy1b, .rs1b } <- bypass_wrapper_1b.func (bypass_from_stage2, rs1, rs1a);

      match { .busy2a, .rs2a } <- bypass_wrapper_2a.func (bypass_from_stage3, rs2, rs2_val);
      match { .busy2b, .rs2b } <- bypass_wrapper_2b.func (bypass_from_stage2, rs2, rs2a);
`else
      match { .busy1a, .rs1a } = fn_gpr_bypass (bypass_from_stage3, rs1, rs1_val);
      match { .busy1b, .rs1b } = fn_gpr_bypass (bypass_from_stage2, rs1, rs1a);

      match { .busy2a, .rs2a } = fn_gpr_bypass (bypass_from_stage3, rs2, rs2_val);
      match { .busy2b, .rs2b } = fn_gpr_bypass (bypass_from_stage2, rs2, rs2a);
`endif

`ifdef ISA_CHERI
      rg_rs1_val <= (rs1 != 0) ? rs1b : nullCap;
      rg_rs2_val <= (rs2 != 0) ? rs2b : nullCap;
`else
      rg_rs1_val <= (rs1 != 0) ? rs1b : 0;
      rg_rs2_val <= (rs2 != 0) ? rs2b : 0;
`endif
      rg_rs1_busy <= busy1a || busy1b;
      rg_rs2_busy <= busy2a || busy2b;
   endrule
`endif



   let stage1_syn <- mkCPU_Stage1_syn;
   let stage1_outputs = stage1_syn.stage1_outputs (
                                                   rg_full,
                                                   cur_epoch,
                                                   cur_priv,
                                                   rg_stage_input,
                                                   rg_pcc,
`ifdef RVFI
                                                   rs1_val_bypassed,
                                                   rs1_val_bypassed,
`endif
                                                   rs1_busy,
                                                   rs2_busy,
`ifdef ISA_F
                                                   frs1_busy,
                                                   frs2_busy,
                                                   frs3_busy,
`endif
                                                   alu_outputs
                                                  );

   // ----------------
   // Combinational output function

   // replaced with code above instantiating stage1_syn

   (* fire_when_enabled, no_implicit_conditions *)
   rule commit_pcc;
      let new_pcc = fromMaybe(fromMaybe(rg_pcc, rw_next_pcc.wget), rw_fresh_pcc.wget);
      rg_pcc <= new_pcc;
      if (verbosity > 1)
         $display ("    CPU_Stage1 PC: 0x%08h", new_pcc);
   endrule

   // ================================================================
   // INTERFACE

   // ---- Reset
   interface server_reset = toGPServer (f_reset_reqs, f_reset_rsps);

   // ---- Output
   method Output_Stage1 out;
      //return fv_out;
      return stage1_outputs;
   endmethod

   method Action deq ();
      let next_pcc_local = stage1_outputs.next_pcc;
      rw_next_pcc.wset(next_pcc_local);
   endmethod

   // ---- Input
   //method Action enq (Data_StageD_to_Stage1  data) if (!(rg_rs1_busy || rg_rs1_busy));
   method Action enq (Data_StageD_to_Stage1  data);
      if (verbosity > 1) begin
         $display ("stage1 enq");
         $display ("data: ", fshow(data));
      end

      if (data.refresh_pcc) begin
         rw_fresh_pcc.wset(fresh_pcc);
      end

`ifdef ISA_CHERI
      // add DDC address to immediate field when the decode stage tells us to
      Bool add_ddc_to_imm = tpl_4 (data.decoded_instr.cheri_info).alu_add_ddc_addr_to_imm;
      Bool add_pcc_a_to_imm = tpl_4 (data.decoded_instr.cheri_info).alu_add_pcc_addr_to_imm;
      Bool add_pcc_b_to_imm = tpl_4 (data.decoded_instr.cheri_info).alu_add_pcc_base_to_imm;
      PCC_T pcc_to_use = data.refresh_pcc ? fresh_pcc : stage1_outputs.next_pcc;
      if (add_ddc_to_imm || add_pcc_a_to_imm || add_pcc_b_to_imm) begin
         data.decoded_instr.imm = data.decoded_instr.imm + ( add_ddc_to_imm   ? getAddr (ddc)
                                                           : add_pcc_a_to_imm ? getPCCAddr (pcc_to_use)
                                                           : getPCCBase (pcc_to_use));
         if (verbosity > 1) begin
            $display ("immediate updated to: ", fshow(data.decoded_instr.imm));
         end
      end
`endif

      rg_stage_input <= data;
`ifdef NEW_BYPASS
      let decoded_instr = data.decoded_instr;
      let rs1 = data.decoded_instr.rs1;
      let rs2 = data.decoded_instr.rs2;

`ifdef DELAY_REGFILE_READ
      let rs1_val = ?;
      let rs2_val = ?;
`else
      let rs1_val = data.rs1_val;
      let rs2_val = data.rs2_val;
`endif

`ifdef DELAY_REGFILE_READ
      // explicitly bypass stuff here, since we need to know explicitly whether w
      // forwarded rs1 and rs2 values

      // register rs1
      let busy1a = False;
      let busy1b = False;
      let rs1a = rs1_val;
      let read_rs1_from_regfile = True;
      if (rs1 == bypass_from_stage3.rd) begin
         if (bypass_from_stage3.bypass_state == BYPASS_RD) begin
            busy1a = True;
            read_rs1_from_regfile = False;
         end else if (bypass_from_stage3.bypass_state == BYPASS_RD_RDVAL) begin
            rs1a = bypass_from_stage3.rd_val;
            read_rs1_from_regfile = False;
         end
      end

      let rs1b = rs1a;
      if (rs1 == bypass_from_stage2.rd) begin
         if (bypass_from_stage2.bypass_state == BYPASS_RD) begin
            busy1b = True;
            read_rs1_from_regfile = False;
         end else if (bypass_from_stage2.bypass_state == BYPASS_RD_RDVAL) begin
            rs1b = bypass_from_stage2.rd_val;
            read_rs1_from_regfile = False;
         end
      end

      if (rs1 == 0) begin
         read_rs1_from_regfile = False;
      end

      // register rs2
      let busy2a = False;
      let busy2b = False;
      let rs2a = rs2_val;
      let read_rs2_from_regfile = True;
      if (rs2 == bypass_from_stage3.rd) begin
         if (bypass_from_stage3.bypass_state == BYPASS_RD) begin
            busy2a = True;
            read_rs2_from_regfile = False;
         end else if (bypass_from_stage3.bypass_state == BYPASS_RD_RDVAL) begin
            rs2a = bypass_from_stage3.rd_val;
            read_rs2_from_regfile = False;
         end
      end

      let rs2b = rs2a;
      if (rs2 == bypass_from_stage2.rd) begin
         if (bypass_from_stage2.bypass_state == BYPASS_RD) begin
            busy2b = True;
            read_rs2_from_regfile = False;
         end else if (bypass_from_stage2.bypass_state == BYPASS_RD_RDVAL) begin
            rs2b = bypass_from_stage2.rd_val;
            read_rs2_from_regfile = False;
         end
      end

      if (rs2 == 0) begin
         read_rs2_from_regfile = False;
      end
`else
`ifdef DEDUPLICATE_BYPASS
      match { .busy1a, .rs1a } <- bypass_wrapper_1a.func (bypass_from_stage3, rs1, rs1_val);
      match { .busy1b, .rs1b } <- bypass_wrapper_1b.func (bypass_from_stage2, rs1, rs1a);

      match { .busy2a, .rs2a } <- bypass_wrapper_2a.func (bypass_from_stage3, rs2, rs2_val);
      match { .busy2b, .rs2b } <- bypass_wrapper_2b.func (bypass_from_stage2, rs2, rs2a);
`else
      match { .busy1a, .rs1a } = fn_gpr_bypass (bypass_from_stage3, rs1, rs1_val);
      match { .busy1b, .rs1b } = fn_gpr_bypass (bypass_from_stage2, rs1, rs1a);

      match { .busy2a, .rs2a } = fn_gpr_bypass (bypass_from_stage3, rs2, rs2_val);
      match { .busy2b, .rs2b } = fn_gpr_bypass (bypass_from_stage2, rs2, rs2a);
`endif
`endif

      let rs1c = rs1b;
      let rs2c = rs2b;
      let busy1c = False;
      let busy2c = False;
      if (rg_full && stage1_outputs.ostatus == OSTATUS_PIPE) begin
         if (stage1_outputs.data_to_stage2.op_stage2 == OP_Stage2_ST) begin

         end
         else if (stage1_outputs.data_to_stage2.op_stage2 == OP_Stage2_ALU) begin
            //if (rs1 == rg_stage_input.decoded_instr.rd) begin
            if (rs1 == stage1_outputs.data_to_stage2.rd) begin
               rs1c = stage1_outputs.data_to_stage2.val1.val;
`ifdef DELAY_REGFILE_READ
               read_rs1_from_regfile = False;
`endif
            end
            //if (rs2 == rg_stage_input.decoded_instr.rd) begin
            if (rs2 == stage1_outputs.data_to_stage2.rd) begin
               rs2c = stage1_outputs.data_to_stage2.val1.val;
`ifdef DELAY_REGFILE_READ
               read_rs2_from_regfile = False;
`endif
            end
         end
         else begin
            if (rs1 == rg_stage_input.decoded_instr.rd) begin
               busy1c = True;
`ifdef DELAY_REGFILE_READ
               read_rs1_from_regfile = False;
`endif
            end
            if (rs2 == rg_stage_input.decoded_instr.rd) begin
               busy2c = True;
`ifdef DELAY_REGFILE_READ
               read_rs2_from_regfile = False;
`endif
            end
         end
      end

`ifdef ISA_CHERI
      rg_rs1_val <= (rs1 != 0) ? rs1c : nullCap;
      rg_rs2_val <= (rs2 != 0) ? rs2c : nullCap;
`else
      rg_rs1_val <= (rs1 != 0) ? rs1c : 0;
      rg_rs2_val <= (rs2 != 0) ? rs2c : 0;
`endif
      rg_rs1_busy <= busy1a || busy1b || busy1c;
      rg_rs2_busy <= busy2a || busy2b || busy2c;
`ifdef DELAY_REGFILE_READ
      rg_read_rs1_from_regfile <= read_rs1_from_regfile;
      rg_read_rs2_from_regfile <= read_rs2_from_regfile;
`endif
`endif // NEW_BYPASS
   endmethod

   method Action set_full (Bool full);
      rg_full <= full;
   endmethod
endmodule

// ================================================================

endpackage
