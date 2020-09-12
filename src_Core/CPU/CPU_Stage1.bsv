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

   // ALU function
   let alu_inputs = ALU_Inputs {cur_priv       : cur_priv,
`ifdef ISA_CHERI
				pcc            : rg_pcc,
				ddc            : ddc,
				pc             : getPC(rg_pcc),
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

   let fall_through_pc = alu_outputs.cf_info.fallthru_PC;



`ifdef ISA_CHERI
   let next_pcc_local = stage1_outputs.next_pcc;
`endif


`ifdef RVFI
   CapReg tmp_val2 = cast(alu_outputs.cap_val2);
   CapMem cap_val2 = cast(tmp_val2);
   let info_RVFI = Data_RVFI_Stage1 {
                       instr:          rg_stage_input.instr,
                       rs1_addr:       rs1,
                       rs2_addr:       rs2,
`ifdef ISA_CHERI
                       rs1_data:       getAddr(rs1_val_bypassed),
                       rs2_data:       getAddr(rs2_val_bypassed),
`else
                       rs1_data:       rs1_val_bypassed,
                       rs2_data:       rs2_val_bypassed,
`endif
                       pc_rdata:       getPC(rg_pcc),
                       pc_wdata:       getPC(next_pcc_local),
`ifdef ISA_F
                       mem_wdata:      alu_outputs.rs_frm_fpr ? alu_outputs.fval2 : truncate(cap_val2),
`else
                       mem_wdata:      truncate(cap_val2),
`endif
                       rd_addr:        alu_outputs.rd,
                       rd_alu:         (alu_outputs.op_stage2 == OP_Stage2_ALU),
                       rd_wdata_alu:   alu_outputs.val1,
                       mem_addr:       ((alu_outputs.op_stage2 == OP_Stage2_LD) || (alu_outputs.op_stage2 == OP_Stage2_ST)
`ifdef ISA_A
                                     || (alu_outputs.op_stage2 == OP_Stage2_AMO)
`endif
                                       ) ? alu_outputs.addr : 0};
`endif

   let data_to_stage2 = Data_Stage1_to_Stage2 {
`ifdef ISA_CHERI
                                               pcc:       rg_pcc,
`else
                                               pc:        rg_stage_input.pc,
`endif
					       instr         : rg_stage_input.instr,
`ifdef RVFI_DII
                                               instr_seq     : rg_stage_input.instr_seq,
`endif
					       op_stage2     : alu_outputs.op_stage2,
					       rd            : alu_outputs.rd,
					       addr          : alu_outputs.addr,
                                               mem_width_code: alu_outputs.mem_width_code,
                                               mem_unsigned  : alu_outputs.mem_unsigned,
`ifdef ISA_CHERI
                                               mem_allow_cap : alu_outputs.mem_allow_cap,
                                               val1          : alu_outputs.val1_cap_not_int ? embed_cap(alu_outputs.cap_val1): embed_int(alu_outputs.val1),
                                               val2          : alu_outputs.val2_cap_not_int ? embed_cap(alu_outputs.cap_val2): embed_int(alu_outputs.val2),
`else
                                               val1          : alu_outputs.val1,
                                               val2          : alu_outputs.val2,
`endif
                                               val1_fast     : alu_outputs.val1_fast,
                                               val2_fast     : alu_outputs.val2_fast,
`ifdef ISA_F
					       fval1         : alu_outputs.fval1,
					       fval2         : alu_outputs.fval2,
					       fval3         : alu_outputs.fval3,
					       rd_in_fpr     : alu_outputs.rd_in_fpr,
					       rs_frm_fpr    : alu_outputs.rs_frm_fpr,
					       val1_frm_gpr  : alu_outputs.val1_frm_gpr,
					       rounding_mode : alu_outputs.rm,
`endif
`ifdef ISA_CHERI
                                               check_enable       : alu_outputs.check_enable,
                                               check_inclusive    : alu_outputs.check_inclusive,
                                               check_authority    : alu_outputs.check_authority,
                                               check_authority_idx: alu_outputs.check_authority_idx,
                                               check_address_low  : alu_outputs.check_address_low,
                                               authority_base     : alu_outputs.authority_base,
                                               check_address_high : alu_outputs.check_address_high,
                                               authority_top      : alu_outputs.authority_top,
                                               check_exact_enable : alu_outputs.check_exact_enable,
                                               check_exact_success: alu_outputs.check_exact_success,
`endif
`ifdef INCLUDE_TANDEM_VERIF
					       trace_data    : alu_outputs.trace_data,
`endif
`ifdef RVFI
                                               info_RVFI_s1  : info_RVFI,
`endif
					       priv          : cur_priv };

`ifdef ISA_CHERI
   let fetch_exc = checkValid(rg_pcc, getTop(toCapPipe(rg_pcc)), rg_stage_input.is_i32_not_i16);
`endif

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
      return stage1_outputs;
   endmethod

   method Action deq ();
      rw_next_pcc.wset(next_pcc_local);
   endmethod

   // ---- Input
   method Action enq (Data_StageD_to_Stage1  data);
      if (data.refresh_pcc) begin
         rw_fresh_pcc.wset(fresh_pcc);
      end
      rg_stage_input <= data;
   endmethod

   method Action set_full (Bool full);
      rg_full <= full;
   endmethod
endmodule

// ================================================================

endpackage
