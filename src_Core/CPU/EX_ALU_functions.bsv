// Copyright (c) 2016-2019 Bluespec, Inc. All Rights Reserved

//-
// RVFI_DII + CHERI modifications:
//     Copyright (c) 2018 Jack Deeley (RVFI_DII)
//     Copyright (c) 2018 Peter Rugg (RVFI_DII + CHERI)
//     All rights reserved.
//
//     This software was developed by SRI International and the University of
//     Cambridge Computer Laboratory (Department of Computer Science and
//     Technology) under DARPA contract HR0011-18-C-0016 ("ECATS"), as part of the
//     DARPA SSITH research programme.
//-

package EX_ALU_functions;

// ================================================================
// These are the "ALU" functions in the EX stage of the "Piccolo" CPU.
// EX stands for "Execution".

// ================================================================
// Exports

export
ALU_Inputs (..),
ALU_Outputs (..),
Output_Select,
mk_ALU,
ALU_IFC (..);

// ================================================================
// BSV library imports

import Vector :: *;
import UniqueWrappers :: *;

// ----------------
// BSV additional libs

// None

// ================================================================
// Project imports

import ISA_Decls   :: *;
import CPU_Globals :: *;
import TV_Info     :: *;
`ifdef ISA_CHERI
import CHERICap :: *;
import CHERICC_Fat :: *;
`endif

// ================================================================
// ALU inputs

typedef struct {
   Priv_Mode      cur_priv;
`ifdef ISA_CHERI
   PCC_T          pcc;
   CapPipe        ddc;
   Bit#(5)        rs1_idx;
   Bit#(5)        rs2_idx;
`endif
   Addr           pc;
   Bool           is_i32_not_i16;
   Instr          instr;
`ifdef ISA_C
   Instr_C        instr_C;
`endif
   Decoded_Instr  decoded_instr;
   WordXL         rs1_val;
   WordXL         rs2_val;
   WordXL         mstatus;
`ifdef ISA_F
   Bit #(3)       frm;
   WordFL         frs1_val;
   WordFL         frs2_val;
   WordFL         frs3_val;
`ifdef INCLUDE_TANDEM_VERIF
   Bit #(5)       fflags;
`endif
`endif
`ifdef ISA_CHERI
   CapPipe        cap_rs1_val;
   CapPipe        cap_rs2_val;
`endif
   MISA           misa;
   } ALU_Inputs
deriving (Bits, FShow);

// ----------------
// These functions pick the instruction size and instruction bits to
// be sent in the trace to a tandem verifier

function ISize  fv_trace_isize (ALU_Inputs  inputs);
   return (inputs.is_i32_not_i16 ? ISIZE32BIT : ISIZE16BIT);
endfunction

function Bit #(32)  fv_trace_instr (ALU_Inputs  inputs);
   Bit #(32) result = inputs.instr;
`ifdef ISA_C
   if (! inputs.is_i32_not_i16)
      result = zeroExtend (inputs.instr_C);
`endif
   return result;
endfunction

// ================================================================
// ALU outputs

`ifdef ISA_CHERI
typedef enum {
  LITERAL,
  SET_OFFSET,
  SET_BOUNDS,
  SET_ADDR,
  GET_PRECISION
  } Output_Select deriving (Bits, FShow, Eq);
`endif

typedef struct {
   Control    control;
   Exc_Code   exc_code;        // Relevant if control == CONTROL_TRAP
`ifdef ISA_CHERI
   CHERI_Exc_Code cheri_exc_code; //Relevant if control == CONTROL_TRAP && exc_code == exc_code_CHERI
   Bit#(6)        cheri_exc_reg;
`endif

   Op_Stage2  op_stage2;
   RegName    rd;
   Addr       addr;           // Branch, jump: newPC
		              // Mem ops and AMOs: mem addr
   WordXL     val1;           // OP_Stage2_ALU: result for Rd (ALU ops: result, JAL/JALR: return PC)
                              // CSRRx: rs1_val
                              // OP_Stage2_M: arg1
                              // OP_Stage2_AMO: funct7

   WordXL     val2;           // Branch: branch target (for Tandem Verification)
		              // OP_Stage2_ST: store-val
                              // OP_Stage2_M: arg2
   WordXL     val1_fast;
   WordXL     val2_fast;

`ifdef ISA_F
   WordFL     fval1;          // OP_Stage2_FD: arg1
   WordFL     fval2;          // OP_Stage2_FD: arg2
   WordFL     fval3;          // OP_Stage2_FD: arg3
   Bool       rd_in_fpr;      // result to be written to fpr
   Bool       rs_frm_fpr;     // src register is in fpr (for stores)
   Bool       val1_frm_gpr;   // first operand is in gpr (for some FP instrns)
   Bit #(3)   rm;             // rounding mode
`endif

   Bit#(3) mem_width_code;
   Bool    mem_unsigned;

`ifdef ISA_CHERI
   Bool    mem_allow_cap; //Whether load/store is allowed to preserve cap tag

   PCC_T   pcc;
`endif

`ifdef ISA_CHERI
   CapPipe    cap_val1;
   CapPipe    cap_val2;
   Bool       val1_cap_not_int;
   Bool       val2_cap_not_int;

   Bool       internal_offset_inc_not_set;
   Bool       internal_bounds_exact;
   Bool       internal_crrl_not_cram;
   Bool       internal_seal_entry;
   CapPipe    internal_op1;
   WordXL     internal_op2;
   Output_Select val1_source;

   Bool                check_enable;
   CapPipe             check_authority;
   Bit #(6)            check_authority_idx;
   Bit#(XLEN)          check_address_low;
   Bit #(XLEN)         authority_base;
   Bit#(TAdd#(XLEN,1)) check_address_high;
   Bit#(TAdd#(XLEN,1)) authority_top;
   Bool                check_inclusive;
   Bool                check_exact_enable;
   Bool                check_exact_success;
`endif

   CF_Info    cf_info;        // For redirection and branch predictor

`ifdef INCLUDE_TANDEM_VERIF
   Trace_Data trace_data;
`endif
   } ALU_Outputs
deriving (Bits, FShow);

typedef Bit #(TAdd #(1, XLEN)) ALUInt;

interface ALU_IFC;
   (* always_enabled *)
   method ALU_Outputs alu_outputs;
endinterface

`ifdef SYNTHESIZE_MODULES
(* synthesize *)
`endif
module mk_ALU #(ALU_Inputs inputs) (ALU_IFC);

CF_Info cf_info_base = CF_Info {cf_op       : CF_None,
				from_PC     : ?,
				taken       : ?,
				fallthru_PC : ?,
				taken_PC    : ?};

ALU_Outputs alu_outputs_base
= ALU_Outputs {control   : CONTROL_STRAIGHT,
	       exc_code  : exc_code_ILLEGAL_INSTRUCTION,
`ifdef ISA_CHERI
               cheri_exc_code: exc_code_CHERI_None,
               cheri_exc_reg:  ?,
`endif
               op_stage2 : OP_Stage2_ALU,
               rd        : ?,
               addr      : ?,
               val1      : ?,
               val2      : ?,
	       val1_fast : ?,
	       val2_fast : ?,
`ifdef ISA_F
               fval1       : ?,
               fval2       : ?,
               fval3       : ?,
               rd_in_fpr   : False,
               rs_frm_fpr  : False,
               val1_frm_gpr: False,
               rm          : ?,
`endif
`ifdef ISA_CHERI
               cap_val1  : ?,
               cap_val2  : ?,
               val1_cap_not_int: False,
               val2_cap_not_int: False,

               internal_offset_inc_not_set : ?,
               internal_bounds_exact       : ?,
               internal_crrl_not_cram      : ?,
               internal_seal_entry         : False,
               internal_op1 : ?,
               internal_op2 : ?,
               val1_source : LITERAL,

               pcc : ?,

               check_enable       : False,
               check_authority    : ?,
               check_authority_idx : ?,
               check_address_low  : ?,
               authority_base     : ?,
               check_address_high : ?,
               authority_top      : ?,
               check_inclusive    : ?,
               check_exact_enable : False,
               check_exact_success : ?,

               mem_allow_cap      : False,
`endif

               mem_width_code     : ?,
               mem_unsigned       : False,

               cf_info     : cf_info_base

`ifdef INCLUDE_TANDEM_VERIF
             , trace_data: ?
`endif
                            };

// ================================================================
// The fall-through PC is PC+4 for normal 32b instructions,
// and PC+2 for 'C' (16b compressed) instructions.

function Addr fall_through_pc_inc (ALU_Inputs inputs);
   Addr inc = 4;
`ifdef ISA_C
   if (! inputs.is_i32_not_i16)
      inc = 2;
`endif
   return inc;
endfunction

function Addr fall_through_pc (ALU_Inputs  inputs);
`ifdef ISA_CHERI
   return getAddr (toCapPipe (inputs.pcc)) + fall_through_pc_inc (inputs);
`else
   return inputs.pc + fall_through_pc_inc (inputs);
`endif
endfunction

// ================================================================
// Alternate implementation of shifts using multiplication in DSPs

// ----------------------------------------------------------------
/* TODO: DELETE? 'factor' RegFile for shift ops

// ----------------------------------------------------------------
// The following is a lookup table of multiplication factors used by the "shift" ops
RegFile #(Bit #(TLog #(XLEN)), Bit #(XLEN))  rf_sh_factors <- mkRegFileFull;
// The following is used during reset to initialize rf_sh_factors
Reg #(Bool)                                  rg_resetting  <- mkReg (False);
Reg #(Bit #(TAdd #(1, TLog #(XLEN))))        rg_j          <- mkRegU;
Reg #(WordXL)                                rg_factor     <- mkRegU;
*/

// ----------------------------------------------------------------
// The following functions implement the 'shift' operators SHL, SHRL and SHRA
// using multiplication instead of actual shifts,
// thus using DSPs (multiplication) and LUTRAMs (rf_sh_factors) instead of LUTs

// Shift-left
// Instead of '>>' operator, uses '*', using DSPs instead of LUTs.
// To SHL(n), do a multiplication by 2^n.
// The 2^n factor is looked up in a RegFile (used as a ROM), which uses a LUTRAM instead of LUTs
function WordXL fn_shl (WordXL x, Bit #(TLog #(XLEN)) shamt);
   IntXL  x_signed = unpack (x);

   // IntXL y_signed = unpack (rf_sh_factors.sub (shamt));
   IntXL  y_signed = unpack ('b1 << shamt);

   IntXL  z_signed = x_signed * y_signed;
   WordXL z        = pack (z_signed);
   return z;
endfunction

// Shift-right-arithmetic
// Instead of '>>' operator, uses '*', using DSPs instead of LUTs
// To SHR(n), do a 2*XLEN-wide multiplication by 2^(32-n), and take upper XLEN bits
// The 2^(32-n) factor is looked up in a RegFile (used as a ROM), which uses a LUTRAM instead of LUTs
function WordXL fn_shra (WordXL x, Bit #(TLog #(XLEN)) shamt);
   // Bit #(TAdd #(1, XLEN)) y = { reverseBits (rf_sh_factors.sub (shamt)), 1'b0 };
   Bit #(TAdd #(1, XLEN)) y = { reverseBits ('b1 << shamt), 1'b0 };

   Int #(XLEN_2) xx_signed = extend (unpack (x));
   Int #(XLEN_2) yy_signed = unpack (extend (y));
   Int #(XLEN_2) zz_signed = xx_signed * yy_signed;
   Bit #(XLEN_2) zz        = pack (zz_signed);
   WordXL        z         = truncateLSB (zz);
   return z;
endfunction

// Shift-right-logical
// Instead of '>>' operator, uses '*', using DSPs instead of LUTs
// To SHR(n), do a 2*XLEN-wide multiplication by 2^(32-n), and take upper XLEN bits
// The 2^(32-n) factor is looked up in a RegFile (used as a ROM), which uses a LUTRAM instead of LUTs
function WordXL fn_shrl (WordXL x, Bit #(TLog #(XLEN)) shamt);
   // Bit #(TAdd #(1, XLEN)) y = { reverseBits (rf_sh_factors.sub (shamt)), 1'b0 };
   Bit #(TAdd #(1, XLEN)) y = { reverseBits ('b1 << shamt), 1'b0 };

   Bit #(XLEN_2) xx = extend (x);
   Bit #(XLEN_2) yy = extend (y);
   Bit #(XLEN_2) zz = xx * yy;
   WordXL        z  = truncateLSB (zz);
   return z;
endfunction


// ----------------------------------------------------------------
// CHERI
// Capability operations

`ifdef ISA_CHERI

function ALU_Outputs fv_CHERI_exc(ALU_Outputs outputs, Bit#(6) regIdx, CHERI_Exc_Code exc_code);
  outputs.exc_code = exc_code_CHERI;
  outputs.cheri_exc_code = exc_code;
  outputs.cheri_exc_reg = regIdx;
  outputs.control = CONTROL_TRAP;
  return outputs;
endfunction

function ALU_Outputs checkValidDereference(ALU_Outputs alu_outputs, CapPipe authority, Bit#(6) authIdx, WordXL base, Bit#(3) widthCode, Bool isStore, Bool isLoad, CapPipe data);
   if (!isValidCap(authority)) begin
       alu_outputs = fv_CHERI_exc(alu_outputs, authIdx, exc_code_CHERI_Tag);
   end else if (getKind(authority) != UNSEALED) begin
       alu_outputs = fv_CHERI_exc(alu_outputs, authIdx, exc_code_CHERI_Seal);
   end else if (isLoad && !getHardPerms(authority).permitLoad) begin
       alu_outputs = fv_CHERI_exc(alu_outputs, authIdx, exc_code_CHERI_RPerm);
   end else if (isStore && !getHardPerms(authority).permitStore) begin
       alu_outputs = fv_CHERI_exc(alu_outputs, authIdx, exc_code_CHERI_WPerm);
   end else if (isStore && widthCode == w_SIZE_CAP && isValidCap(data) && !getHardPerms(authority).permitStoreCap) begin
       alu_outputs = fv_CHERI_exc(alu_outputs, authIdx, exc_code_CHERI_SCPerm);
   end else if (isStore && widthCode == w_SIZE_CAP && isValidCap(data) && !getHardPerms(data).global && !getHardPerms(authority).permitStoreLocalCap) begin
       alu_outputs = fv_CHERI_exc(alu_outputs, authIdx, exc_code_CHERI_SCLocalPerm);
   end
   alu_outputs.check_enable = True;
   alu_outputs.check_authority = authority;
   alu_outputs.check_authority_idx = authIdx;
   alu_outputs.check_address_low = base;
   alu_outputs.check_address_high = zeroExtend(base) + (1 << widthCode);
   alu_outputs.check_inclusive = True;

   //TODO check alignment?
   if (widthCode == w_SIZE_CAP && isLoad && getHardPerms(authority).permitLoadCap) begin
       alu_outputs.mem_allow_cap = True;
   end
   return alu_outputs;
endfunction

function ALU_Outputs checkValidJump(ALU_Outputs alu_outputs, Bool branchTaken, CapPipe authority, WordXL authority_base, Bit#(6) authIdx, WordXL target);
   //Note that we only check the first two bytes of the target instruction are in bounds in the jump.
`ifdef ISA_C
   Bool misaligned_target = authority_base[0] != 1'b0;
`else
   Bool misaligned_target = (target [1] == 1'b1) || (authority_base[1:0] != 2'b0);
`endif
   if (misaligned_target && branchTaken) begin
       alu_outputs.control = CONTROL_TRAP;
       alu_outputs.exc_code = exc_code_INSTR_ADDR_MISALIGNED;
   end
   alu_outputs.check_enable = branchTaken;
   alu_outputs.check_authority = authority;
   alu_outputs.check_authority_idx = authIdx;
   alu_outputs.check_address_low = target;
   alu_outputs.check_address_high = zeroExtend(target) + 2;
   alu_outputs.check_inclusive = True;
   return alu_outputs;
endfunction

function ALU_Outputs memCommon(ALU_Outputs alu_outputs, Bool isStoreNotLoad, Bool isUnsignedNotSigned, Bool useDDC, Bit#(3) widthCode, CapPipe ddc, CapPipe addr, Bit#(5) addrIdx, CapPipe data, Bool is_amo, Bit#(7) amo_funct7);
   let eaddr = getAddr(addr) + (useDDC ? getAddr(ddc) : 0);
   let op_stage2 = isStoreNotLoad ? OP_Stage2_ST : OP_Stage2_LD;
`ifdef ISA_A
   if (is_amo) op_stage2 = OP_Stage2_AMO;
`endif

   //width code must be checked externally

   alu_outputs.op_stage2      = op_stage2;
   alu_outputs.addr           = eaddr;
   alu_outputs.mem_width_code = widthCode;
   alu_outputs.mem_unsigned   = isStoreNotLoad ? False : isUnsignedNotSigned;
   alu_outputs.val1           = zeroExtend(amo_funct7);
   alu_outputs.val2           = zeroExtend(getAddr(data)); //for stores
   alu_outputs.cap_val2       = data;
   alu_outputs.val2_cap_not_int = widthCode == w_SIZE_CAP;

   let authority = useDDC ? ddc : addr;
   let authorityIdx = useDDC ? {1,scr_addr_DDC} : {0,addrIdx};

   alu_outputs = checkValidDereference(alu_outputs, authority, authorityIdx, eaddr, widthCode, isStoreNotLoad, !isStoreNotLoad, data);

   return alu_outputs;
endfunction












// ================================================================
// BRANCH

function ALU_Outputs fv_BRANCH (ALU_Inputs inputs);
   let rs1_val = inputs.rs1_val;
   let rs2_val = inputs.rs2_val;

   // Signed versions of rs1_val and rs2_val
   IntXL s_rs1_val = unpack (inputs.rs1_val);
   IntXL s_rs2_val = unpack (inputs.rs2_val);

   IntXL offset        = extend (unpack (inputs.decoded_instr.imm13_SB));
   Addr  branch_target = pack (unpack (inputs.pc) + offset);
   Bool  branch_taken  = False;
   Bool  trap          = False;

   let funct3 = inputs.decoded_instr.funct3;
   if      (funct3 == f3_BEQ)  branch_taken = (rs1_val  == rs2_val);
   else if (funct3 == f3_BNE)  branch_taken = (rs1_val  != rs2_val);
   else if (funct3 == f3_BLT)  branch_taken = (s_rs1_val <  s_rs2_val);
   else if (funct3 == f3_BGE)  branch_taken = (s_rs1_val >= s_rs2_val);
   else if (funct3 == f3_BLTU) branch_taken = (rs1_val  <  rs2_val);
   else if (funct3 == f3_BGEU) branch_taken = (rs1_val  >= rs2_val);
   else                        trap = True;

   Bool misaligned_target = (branch_target [1] == 1'b1);
`ifdef ISA_C
   misaligned_target = False;
`endif

   Exc_Code exc_code = exc_code_ILLEGAL_INSTRUCTION;
   if ((! trap) && branch_taken && misaligned_target) begin
      trap = True;
      exc_code = exc_code_INSTR_ADDR_MISALIGNED;
   end

`ifdef ISA_CHERI
   let pcc_addr = getAddr(toCapPipe(inputs.pcc));
   let cf_info   = CF_Info {cf_op       : CF_BR,
			    from_PC     : pcc_addr,
			    taken       : branch_taken,
			    fallthru_PC : pcc_addr + fall_through_pc_inc(inputs),
			    taken_PC    : pack(unpack(pcc_addr) + offset) };
`else
   let cf_info   = CF_Info {cf_op       : CF_BR,
			    from_PC     : inputs.pc,
			    taken       : branch_taken,
			    fallthru_PC : fall_through_pc (inputs),
			    taken_PC    : branch_target };
`endif

   let alu_outputs = alu_outputs_base;
   let next_pc     = (branch_taken ? branch_target : fall_through_pc (inputs));
   alu_outputs.control   = (trap ? CONTROL_TRAP : (branch_taken ? CONTROL_BRANCH : CONTROL_STRAIGHT));
   alu_outputs.exc_code  = exc_code;
   alu_outputs.op_stage2 = OP_Stage2_ALU;
   alu_outputs.rd        = 0;
   // Gives a defined value when in verification mode.
   `ifdef RVFI
   alu_outputs.val1      = 0;
   `endif
   alu_outputs.addr      = next_pc;
   alu_outputs.val2      = extend (branch_target);    // For tandem verifier only

`ifdef ISA_CHERI
   alu_outputs = checkValidJump(alu_outputs, branch_taken, toCapPipe(inputs.pcc), getPCCBase(inputs.pcc), {1,scr_addr_PCC}, getPCCBase(inputs.pcc) + next_pc);
`endif

   alu_outputs.cf_info   = cf_info;
`ifdef INCLUDE_TANDEM_VERIF
   // Normal trace output (if no trap)
   alu_outputs.trace_data = mkTrace_OTHER (next_pc,
					   fv_trace_isize (inputs),
					   fv_trace_instr (inputs));
`endif
   return alu_outputs;
endactionvalue
endfunction

// ----------------------------------------------------------------
// JAL

function ALU_Outputs fv_JAL (ALU_Inputs inputs);
   IntXL offset  = extend (unpack (inputs.decoded_instr.imm21_UJ));
   Addr  next_pc = pack (unpack (inputs.pc) + offset);
   Addr  ret_pc  = fall_through_pc (inputs);

   Bool misaligned_target = (next_pc [1] == 1'b1);
`ifdef ISA_C
   misaligned_target = False;
`endif

`ifdef ISA_CHERI
   let pcc_addr = getAddr(toCapPipe(inputs.pcc));
   let cf_info   = CF_Info {cf_op       : CF_JAL,
			    from_PC     : pcc_addr,
			    taken       : True,
			    fallthru_PC : pcc_addr + fall_through_pc_inc(inputs),
			    taken_PC    : pack(unpack(pcc_addr) + offset) };
`else
   let cf_info   = CF_Info {cf_op       : CF_JAL,
			    from_PC     : inputs.pc,
			    taken       : True,
			    fallthru_PC : ret_pc,
			    taken_PC    : next_pc };
`endif

   let alu_outputs = alu_outputs_base;
   alu_outputs.control   = (misaligned_target ? CONTROL_TRAP : CONTROL_BRANCH);
   alu_outputs.exc_code  = exc_code_INSTR_ADDR_MISALIGNED;
   alu_outputs.op_stage2 = OP_Stage2_ALU;
   alu_outputs.rd        = inputs.decoded_instr.rd;
   alu_outputs.addr      = next_pc;
   alu_outputs.val1      = extend (ret_pc);
   alu_outputs.cf_info   = cf_info;

`ifdef ISA_CHERI
   alu_outputs = checkValidJump(alu_outputs, True, toCapPipe(inputs.pcc), getPCCBase(inputs.pcc), {1,scr_addr_PCC}, getPCCBase(inputs.pcc) + next_pc);
`endif

`ifdef INCLUDE_TANDEM_VERIF
   // Normal trace output (if no trap)
   alu_outputs.trace_data = mkTrace_I_RD (next_pc,
					  fv_trace_isize (inputs),
					  fv_trace_instr (inputs),
					  inputs.decoded_instr.rd,
					  ret_pc);
`endif
   return alu_outputs;
endfunction

// ----------------------------------------------------------------
// JALR

function ALU_Outputs fv_JALR (ALU_Inputs inputs);
   let rs1_val = inputs.rs1_val;
   let rs2_val = inputs.rs2_val;

   // Signed versions of rs1_val and rs2_val
   IntXL s_rs1_val = unpack (rs1_val);
   IntXL s_rs2_val = unpack (rs2_val);
   IntXL offset    = extend (unpack (inputs.decoded_instr.imm12_I));
   Addr  next_pc   = pack (s_rs1_val + offset);
   Addr  ret_pc    = fall_through_pc (inputs);

   // next_pc [0] should be cleared
   next_pc [0] = 1'b0;

   Bool misaligned_target = (next_pc [1] == 1'b1);
`ifdef ISA_C
   misaligned_target = False;
`endif

`ifdef ISA_CHERI
   let pcc_addr = getAddr(toCapPipe(inputs.pcc));
   let target_addr = getPCCBase(inputs.pcc) + next_pc;
   let cf_info   = CF_Info {cf_op       : CF_JALR,
			    from_PC     : pcc_addr,
			    taken       : True,
			    fallthru_PC : pcc_addr + fall_through_pc_inc(inputs),
			    taken_PC    : target_addr };
`else
   let cf_info   = CF_Info {cf_op       : CF_JALR,
			    from_PC     : inputs.pc,
			    taken       : True,
			    fallthru_PC : ret_pc,
			    taken_PC    : next_pc };
`endif

   let alu_outputs = alu_outputs_base;
   alu_outputs.control   = (misaligned_target ? CONTROL_TRAP : CONTROL_BRANCH);
   alu_outputs.exc_code  = exc_code_INSTR_ADDR_MISALIGNED;
   alu_outputs.op_stage2 = OP_Stage2_ALU;
   alu_outputs.rd        = inputs.decoded_instr.rd;
   alu_outputs.addr      = next_pc;
   alu_outputs.val1      = extend (ret_pc);
   alu_outputs.cf_info   = cf_info;

`ifdef ISA_CHERI
   alu_outputs = checkValidJump(alu_outputs, True, toCapPipe(inputs.pcc), getPCCBase(inputs.pcc), {1,scr_addr_PCC}, target_addr);
`endif

`ifdef INCLUDE_TANDEM_VERIF
   // Normal trace output (if no trap)
   alu_outputs.trace_data = mkTrace_I_RD (next_pc,
					  fv_trace_isize (inputs),
					  fv_trace_instr (inputs),
					  inputs.decoded_instr.rd,
					  ret_pc);
`endif
   return alu_outputs;
endfunction

// ----------------------------------------------------------------
// Integer Register-Register and Register-Immediate Instructions

// ----------------
// Shifts (funct3 == f3_SLLI/ f3_SRLI/ f3_SRAI)

function ALU_Outputs fv_OP_and_OP_IMM_shifts (ALU_Inputs inputs);
   let rs1_val = inputs.rs1_val;
   let rs2_val = inputs.rs2_val;

   IntXL s_rs1_val = unpack (rs1_val);    // Signed version of rs1, for SRA

   Bit #(TLog #(XLEN)) shamt = (  (inputs.decoded_instr.opcode == op_OP_IMM)
				? truncate (inputs.decoded_instr.imm12_I)
				: truncate (rs2_val));
   WordXL   rd_val    = ?;
   let      funct3    = inputs.decoded_instr.funct3;
   Bit #(1) instr_b30 = inputs.instr [30];

`ifdef SHIFT_BARREL
   // Shifts implemented by Verilog synthesis,
   // mapping to barrel shifters
   if (funct3 == f3_SLLI)
      rd_val = (rs1_val << shamt);
   else begin // assert: (funct3 == f3_SRxI)
      if (instr_b30 == 1'b0)
	 // SRL/SRLI
	 rd_val = (rs1_val >> shamt);
      else
	 // SRA/SRAI
	 rd_val = pack (s_rs1_val >> shamt);
   end
`endif

`ifdef SHIFT_MULT
   // Shifts implemented using multiplication by 2^shamt,
   // mapping to DSPs in FPGA
   if (funct3 == f3_SLLI)
      rd_val = fn_shl (rs1_val, shamt);  // in LUTRAMs/DSPs
   else begin // assert: (funct3 == f3_SRxI)
      if (instr_b30 == 1'b0) begin
	 // SRL/SRLI
	 rd_val = fn_shrl (rs1_val, shamt);  // in LUTRAMs/DSPs
      else
	 // SRA/SRAI
	 rd_val = fn_shra (rs1_val, shamt);     // in LUTRAMs/DSPs
   end
`endif

   // Trap in RV32 if shamt > 31, i.e., if imm12_I [5] is 1
   Bool trap = ((rv_version == RV32) && (inputs.decoded_instr.imm12_I [5] == 1));

   let alu_outputs       = alu_outputs_base;
   alu_outputs.control   = (trap ? CONTROL_TRAP : CONTROL_STRAIGHT);
   alu_outputs.rd        = inputs.decoded_instr.rd;

`ifndef SHIFT_SERIAL
   alu_outputs.op_stage2 = OP_Stage2_ALU;
   alu_outputs.val1      = rd_val;
`else
   // Will be executed in serial Shifter_Box later
   alu_outputs.op_stage2 = OP_Stage2_SH;
   alu_outputs.val1      = rs1_val;
   // Encode 'arith-shift' in bit [7] of val2
   WordXL val2 = extend (shamt);
   val2 = (val2 | { 0, instr_b30, 7'b0});
   alu_outputs.val2 = val2;
   alu_outputs.val1_fast = alu_outputs.val1;
   alu_outputs.val2_fast = alu_outputs.val2;
`endif

`ifdef INCLUDE_TANDEM_VERIF
   // Normal trace output (if no trap)
   alu_outputs.trace_data = mkTrace_I_RD (fall_through_pc (inputs),
					  fv_trace_isize (inputs),
					  fv_trace_instr (inputs),
					  inputs.decoded_instr.rd,
					  rd_val);
`endif
   return alu_outputs;
endfunction: fv_OP_and_OP_IMM_shifts

// ----------------
// Remaining OP and OP_IMM (excluding shifts, M ops MUL/DIV/REM)

function ALU_Outputs fv_OP_and_OP_IMM (ALU_Inputs inputs);
   let rs1_val = inputs.rs1_val;
   let rs2_val = inputs.rs2_val;

   // Signed versions of rs1_val and rs2_val
   IntXL  s_rs1_val = unpack (rs1_val);
   IntXL  s_rs2_val = unpack (rs2_val);

   IntXL  s_rs2_val_local = s_rs2_val;
   WordXL rs2_val_local   = rs2_val;

   Bit #(1) instr_b30  = inputs.instr [30];
   Bool     subtract   = ((inputs.decoded_instr.opcode == op_OP) && (instr_b30 == 1'b1));

   if (inputs.decoded_instr.opcode == op_OP_IMM) begin
      s_rs2_val_local = extend (unpack (inputs.decoded_instr.imm12_I));
      rs2_val_local   = pack (s_rs2_val_local);
   end

   let  funct3 = inputs.decoded_instr.funct3;
   Bool trap   = False;
   WordXL rd_val = ?;

   if      ((funct3 == f3_ADDI) && (! subtract)) rd_val = pack (s_rs1_val + s_rs2_val_local);
   else if ((funct3 == f3_ADDI) && (subtract))   rd_val = pack (s_rs1_val - s_rs2_val_local);

   else if (funct3 == f3_SLTI)  rd_val = ((s_rs1_val < s_rs2_val_local) ? 1 : 0);
   else if (funct3 == f3_SLTIU) rd_val = ((rs1_val  < rs2_val_local)  ? 1 : 0);
   else if (funct3 == f3_XORI)  rd_val = pack (s_rs1_val ^ s_rs2_val_local);
   else if (funct3 == f3_ORI)   rd_val = pack (s_rs1_val | s_rs2_val_local);
   else if (funct3 == f3_ANDI)  rd_val = pack (s_rs1_val & s_rs2_val_local);
   else
      trap = True;

   let alu_outputs       = alu_outputs_base;
   alu_outputs.control   = (trap ? CONTROL_TRAP : CONTROL_STRAIGHT);
   alu_outputs.op_stage2 = OP_Stage2_ALU;
   alu_outputs.rd        = inputs.decoded_instr.rd;
   alu_outputs.val1      = rd_val;

`ifdef INCLUDE_TANDEM_VERIF
   // Normal trace output (if no trap)
   alu_outputs.trace_data = mkTrace_I_RD (fall_through_pc (inputs),
					  fv_trace_isize (inputs),
					  fv_trace_instr (inputs),
					  inputs.decoded_instr.rd,
					  rd_val);
`endif
   return alu_outputs;
endfunction: fv_OP_and_OP_IMM

// ----------------
// OP_IMM_32 (ADDIW, SLLIW, SRxIW)

function ALU_Outputs fv_OP_IMM_32 (ALU_Inputs inputs);
   WordXL   rs1_val     = inputs.rs1_val;
   IntXL    s_rs1_val   = unpack (rs1_val);

   Bit #(5) shamt       = truncate (inputs.decoded_instr.imm12_I);
   Bool     shamt5_is_0 = (inputs.instr [25] == 1'b0);

   let    funct3 = inputs.decoded_instr.funct3;
   Bool   trap   = False;
   WordXL rd_val = ?;

   if (funct3 == f3_ADDIW) begin
      IntXL  s_rs2_val = extend (unpack (inputs.decoded_instr.imm12_I));
      IntXL  sum       = s_rs1_val + s_rs2_val;
      WordXL tmp       = pack (sum);
      rd_val           = signExtend (tmp [31:0]);
   end
   else if ((funct3 == f3_SLLIW) && shamt5_is_0) begin
      Bit #(32) tmp = truncate (rs1_val);
      rd_val = signExtend (tmp << shamt);
   end
   else if ((funct3 == f3_SRxIW) && shamt5_is_0) begin
      Bit #(1) instr_b30 = inputs.instr [30];
      if (instr_b30 == 1'b0) begin
	 // SRLIW
	 Bit #(32) tmp = truncate (rs1_val);
	 rd_val = signExtend (tmp >> shamt);
      end
      else begin
	 // SRAIW
	 Int #(32) s_tmp = unpack (rs1_val [31:0]);
	 Bit #(32) tmp   = pack (s_tmp >> shamt);
	 rd_val = signExtend (tmp);
      end
   end
   else
      trap = True;

   let alu_outputs       = alu_outputs_base;
   alu_outputs.control   = (trap ? CONTROL_TRAP : CONTROL_STRAIGHT);
   alu_outputs.op_stage2 = OP_Stage2_ALU;
   alu_outputs.rd        = inputs.decoded_instr.rd;
   alu_outputs.val1      = rd_val;

`ifdef INCLUDE_TANDEM_VERIF
   // Normal trace output (if no trap)
   alu_outputs.trace_data = mkTrace_I_RD (fall_through_pc (inputs),
					  fv_trace_isize (inputs),
					  fv_trace_instr (inputs),
					  inputs.decoded_instr.rd,
					  rd_val);
`endif
   return alu_outputs;
endfunction: fv_OP_IMM_32

// ----------------
// OP_32 (excluding 'M' ops: MULW/ DIVW/ DIVUW/ REMW/ REMUW)

function ALU_Outputs fv_OP_32 (ALU_Inputs inputs);
   Bit #(32) rs1_val = inputs.rs1_val [31:0];
   Bit #(32) rs2_val = inputs.rs2_val [31:0];

   // Signed version of rs1_val and rs2_val
   Int #(32) s_rs1_val = unpack (rs1_val);
   Int #(32) s_rs2_val = unpack (rs2_val);

   let    funct10 = inputs.decoded_instr.funct10;
   Bool   trap   = False;
   WordXL rd_val = ?;

   if      (funct10 == f10_ADDW) begin
      rd_val = pack (signExtend (s_rs1_val + s_rs2_val));
   end
   else if (funct10 == f10_SUBW) begin
      rd_val = pack (signExtend (s_rs1_val - s_rs2_val));
   end
   else if (funct10 == f10_SLLW) begin
      rd_val = pack (signExtend (rs1_val << (rs2_val [4:0])));
   end
   else if (funct10 == f10_SRLW) begin
      rd_val = pack (signExtend (rs1_val >> (rs2_val [4:0])));
   end
   else if (funct10 == f10_SRAW) begin
      rd_val = pack (signExtend (s_rs1_val >> (rs2_val [4:0])));
   end
   else
      trap = True;

   let alu_outputs       = alu_outputs_base;
   alu_outputs.control   = (trap ? CONTROL_TRAP : CONTROL_STRAIGHT);
   alu_outputs.op_stage2 = OP_Stage2_ALU;
   alu_outputs.rd        = inputs.decoded_instr.rd;
   alu_outputs.val1      = rd_val;

`ifdef INCLUDE_TANDEM_VERIF
   // Normal trace output (if no trap)
   alu_outputs.trace_data = mkTrace_I_RD (fall_through_pc (inputs),
					  fv_trace_isize (inputs),
					  fv_trace_instr (inputs),
					  inputs.decoded_instr.rd,
					  rd_val);
`endif
   return alu_outputs;
endfunction: fv_OP_32

// ----------------------------------------------------------------
// Upper Immediates

function ALU_Outputs fv_LUI (ALU_Inputs inputs);
   Bit #(32)  v32    = { inputs.decoded_instr.imm20_U, 12'h0 };
   IntXL      iv     = extend (unpack (v32));
   let        rd_val = pack (iv);

   let alu_outputs       = alu_outputs_base;
   alu_outputs.op_stage2 = OP_Stage2_ALU;
   alu_outputs.rd        = inputs.decoded_instr.rd;
   alu_outputs.val1      = rd_val;

`ifdef INCLUDE_TANDEM_VERIF
   // Normal trace output (if no trap)
   alu_outputs.trace_data = mkTrace_I_RD (fall_through_pc (inputs),
					  fv_trace_isize (inputs),
					  fv_trace_instr (inputs),
					  inputs.decoded_instr.rd,
					  rd_val);
`endif
   return alu_outputs;
endfunction

function ALU_Outputs fv_AUIPC (ALU_Inputs inputs);
   IntXL  iv     = extend (unpack ({ inputs.decoded_instr.imm20_U, 12'b0}));
   IntXL  pc_s   = unpack (inputs.pc);
   WordXL rd_val = pack (pc_s + iv);

   let alu_outputs       = alu_outputs_base;
   alu_outputs.op_stage2 = OP_Stage2_ALU;
   alu_outputs.rd        = inputs.decoded_instr.rd;
`ifdef ISA_CHERI
   if (getFlags(toCapPipe(inputs.pcc))[0] == 1'b1) begin
       alu_outputs.val1_source = SET_OFFSET;
       alu_outputs.internal_op1 = toCapPipe(inputs.pcc);
       alu_outputs.internal_op2 = pack(iv);
       alu_outputs.internal_offset_inc_not_set = True;
   end else
`endif
   begin
       alu_outputs.val1      = rd_val;
   end

`ifdef INCLUDE_TANDEM_VERIF
   // Normal trace output (if no trap)
   alu_outputs.trace_data = mkTrace_I_RD (fall_through_pc (inputs),
					  fv_trace_isize (inputs),
					  fv_trace_instr (inputs),
					  inputs.decoded_instr.rd,
					  rd_val);
`endif
   return alu_outputs;
endfunction

// ----------------------------------------------------------------
// LOAD

function ALU_Outputs fv_LD (ALU_Inputs inputs, Maybe#(Bit#(3)) size);
   // Signed versions of rs1_val and rs2_val
   let opcode = inputs.decoded_instr.opcode;
   IntXL s_rs1_val = unpack (inputs.rs1_val);
   IntXL s_rs2_val = unpack (inputs.rs2_val);

   IntXL  imm_s = extend (unpack (inputs.decoded_instr.imm12_I));
`ifdef ISA_CHERI
   if (valueOf(XLEN) == 32 && inputs.decoded_instr.funct3 == f3_LD) size = Valid(w_SIZE_D);

   let authority = getFlags(toCapPipe(inputs.pcc))[0] == 1'b0 ? inputs.ddc : inputs.cap_rs1_val;
   let authorityIdx = getFlags(toCapPipe(inputs.pcc))[0] == 1'b0 ? {1,scr_addr_DDC} : {0,inputs.rs1_idx};
   WordXL eaddr = getFlags(toCapPipe(inputs.pcc))[0] == 1'b0 ? getAddr(inputs.ddc) + inputs.rs1_val + pack(imm_s) : getAddr(inputs.cap_rs1_val) + pack(imm_s);
`else
   WordXL eaddr = pack (s_rs1_val + imm_s);
`endif

   let funct3 = inputs.decoded_instr.funct3;

   Bool legal_LD = (
           isValid(size)
        || (funct3 == f3_LB) || (funct3 == f3_LBU)
		    || (funct3 == f3_LH) || (funct3 == f3_LHU)
		    || (funct3 == f3_LW)
`ifdef RV64
		    || (funct3 == f3_LWU)
		    || (funct3 == f3_LD)
`endif
`ifdef ISA_F
		    || (funct3 == f3_FLW)
`endif
`ifdef ISA_D
		    || (funct3 == f3_FLD)
`endif
		    );

   // FP loads are not legal unless the MSTATUS.FS bit is set
   Bool legal_FP_LD = True;
`ifdef ISA_F
   if (opcode == op_LOAD_FP)
      legal_FP_LD = (fv_mstatus_fs (inputs.mstatus) != fs_xs_off);
`endif

   let alu_outputs = alu_outputs_base;

   let width_code = fromMaybe({0,funct3[1:0]}, size);

   alu_outputs.control   = ((legal_LD && legal_FP_LD) ? CONTROL_STRAIGHT
                                                      : CONTROL_TRAP);
   alu_outputs.op_stage2 = OP_Stage2_LD;
   alu_outputs.rd        = inputs.decoded_instr.rd;
   alu_outputs.addr      = eaddr;
   alu_outputs.mem_width_code = width_code;
   alu_outputs.mem_unsigned = unpack(funct3[2]);
`ifdef ISA_F
   // note that the destination register for this load is in the FPR
   alu_outputs.rd_in_fpr = (opcode == op_LOAD_FP);
`endif

`ifdef ISA_CHERI
   alu_outputs = checkValidDereference(alu_outputs, authority, authorityIdx, eaddr, width_code, False, True, ?);
`endif

`ifdef INCLUDE_TANDEM_VERIF
   // Normal trace output (if no trap)
`ifdef ISA_F
   if (alu_outputs.rd_in_fpr)
      alu_outputs.trace_data = mkTrace_F_LOAD (fall_through_pc (inputs),
					       fv_trace_isize (inputs),
					       fv_trace_instr (inputs),
					       inputs.decoded_instr.rd,
					       ?,
					       eaddr,
                                               inputs.mstatus);
   else
`endif
      alu_outputs.trace_data = mkTrace_I_LOAD (fall_through_pc (inputs),
					       fv_trace_isize (inputs),
					       fv_trace_instr (inputs),
					       inputs.decoded_instr.rd,
					       ?,
					       eaddr);
`endif
   return alu_outputs;
endfunction

// ----------------------------------------------------------------
// STORE

function ALU_Outputs fv_ST (ALU_Inputs inputs);
   // Signed version of rs1_val
   IntXL  s_rs1_val = unpack (inputs.rs1_val);
   IntXL  imm_s     = extend (unpack (inputs.decoded_instr.imm12_S));
`ifdef ISA_CHERI
   let authority = getFlags(toCapPipe(inputs.pcc))[0] == 1'b0 ? inputs.ddc : inputs.cap_rs1_val;
   let authorityIdx = getFlags(toCapPipe(inputs.pcc))[0] == 1'b0 ? {1,scr_addr_DDC} : {0,inputs.rs1_idx};
   WordXL eaddr = getFlags(toCapPipe(inputs.pcc))[0] == 1'b0 ? getAddr(inputs.ddc) + inputs.rs1_val + pack(imm_s) : getAddr(inputs.cap_rs1_val) + pack(imm_s);
`else
   WordXL eaddr = pack (s_rs1_val + imm_s);
`endif

   let opcode = inputs.decoded_instr.opcode;
   let funct3 = inputs.decoded_instr.funct3;
   Bool legal_ST = (   (funct3 == f3_SB)
		    || (funct3 == f3_SH)
		    || (funct3 == f3_SW)
`ifdef ISA_CHERI
`ifdef RV64
        || (funct3 == f3_SQ)
`else
        || (funct3 == f3_SD)
`endif
`endif
`ifdef RV64
		    || (funct3 == f3_SD)
`endif
`ifdef ISA_F
		    || (funct3 == f3_FSW)
`endif
`ifdef ISA_D
		    || (funct3 == f3_FSD)
`endif
		    );

   let alu_outputs = alu_outputs_base;

   // FP stores are not legal unless the MSTATUS.FS bit is set
   Bool legal_FP_ST = True;
`ifdef ISA_F
   if (opcode == op_STORE_FP) begin
      legal_FP_ST = (fv_mstatus_fs (inputs.mstatus) != fs_xs_off);

      // note that the source data register for this store is in the FPR
      alu_outputs.rs_frm_fpr = True;
   end
`endif

   let width_code = funct3;

   alu_outputs.control   = ((legal_ST && legal_FP_ST) ? CONTROL_STRAIGHT
                                                      : CONTROL_TRAP);
   alu_outputs.op_stage2 = OP_Stage2_ST;
   alu_outputs.addr      = eaddr;
   alu_outputs.mem_width_code = width_code;
   alu_outputs.mem_unsigned = False;

`ifdef ISA_CHERI
   alu_outputs = checkValidDereference(alu_outputs, authority, authorityIdx, eaddr, width_code, True, False, inputs.cap_rs2_val);
`endif

   alu_outputs.val2      = inputs.rs2_val;

`ifdef ISA_CHERI
   alu_outputs.cap_val2      = inputs.cap_rs2_val;
   alu_outputs.val2_cap_not_int = width_code == w_SIZE_CAP;
`endif

`ifdef ISA_F
   alu_outputs.fval2     = inputs.frs2_val;
`endif

`ifdef INCLUDE_TANDEM_VERIF
   // Normal trace output (if no trap)
`ifdef ISA_F
   if (opcode == op_STORE_FP)
      alu_outputs.trace_data = mkTrace_F_STORE (fall_through_pc (inputs),
						funct3,
						fv_trace_isize (inputs),
						fv_trace_instr (inputs),
						alu_outputs.fval2,
						eaddr);
   else
`endif
      alu_outputs.trace_data = mkTrace_I_STORE (fall_through_pc (inputs),
						funct3,
						fv_trace_isize (inputs),
						fv_trace_instr (inputs),
						(alu_outputs.val2),
						eaddr);
`endif
   return alu_outputs;
endfunction

// ----------------------------------------------------------------
// MISC_MEM (FENCE and FENCE.I)
// No-ops, for now

function ALU_Outputs fv_MISC_MEM (ALU_Inputs inputs);
`ifdef ISA_CHERI
   if (valueOf(XLEN) == 64 && inputs.decoded_instr.funct3 == f3_LQ) begin
       return fv_LD(inputs, Valid(w_SIZE_Q));
   end else
`endif
   begin
       let alu_outputs = alu_outputs_base;
       alu_outputs.control  = (  (inputs.decoded_instr.funct3 == f3_FENCE_I)
			       ? CONTROL_FENCE_I
			       : (  (inputs.decoded_instr.funct3 == f3_FENCE)
			          ? CONTROL_FENCE
			          : CONTROL_TRAP));

`ifdef INCLUDE_TANDEM_VERIF
       // Normal trace output (if no trap)
       alu_outputs.trace_data = mkTrace_OTHER (fall_through_pc (inputs),
					       fv_trace_isize (inputs),
					       fv_trace_instr (inputs));
`endif
       return alu_outputs;
   end
endfunction

// ----------------------------------------------------------------
// System instructions

function ALU_Outputs fv_SYSTEM (ALU_Inputs inputs);
   let funct3      = inputs.decoded_instr.funct3;
   let alu_outputs = alu_outputs_base;

`ifdef INCLUDE_TANDEM_VERIF
   // Normal trace output (if no trap)
   alu_outputs.trace_data = mkTrace_OTHER (fall_through_pc (inputs),
					   fv_trace_isize (inputs),
					   fv_trace_instr (inputs));
`endif

   if (funct3  == f3_PRIV) begin
`ifdef ISA_PRIV_S
      // SFENCE.VMA instruction
      if (   (inputs.decoded_instr.rd  == 0)
	  && (   (inputs.cur_priv == m_Priv_Mode)
	      || (   (inputs.cur_priv == s_Priv_Mode)
		  && (inputs.mstatus [mstatus_tvm_bitpos] == 0)))
	  && (inputs.decoded_instr.funct7 == f7_SFENCE_VMA))
	 begin
	    alu_outputs.control = CONTROL_SFENCE_VMA;
	 end
      else
`endif
      if (   (inputs.decoded_instr.rd  == 0)
	  && (inputs.decoded_instr.rs1 == 0))
	 begin
	    // ECALL instructions
	    if (inputs.decoded_instr.imm12_I == f12_ECALL) begin
	       alu_outputs.control  = CONTROL_TRAP;
	       alu_outputs.exc_code = ((inputs.cur_priv == u_Priv_Mode)
				       ? exc_code_ECALL_FROM_U
				       : ((inputs.cur_priv == s_Priv_Mode)
					  ? exc_code_ECALL_FROM_S
					  : exc_code_ECALL_FROM_M));
	    end

	    // EBREAK instruction
	    else if (inputs.decoded_instr.imm12_I == f12_EBREAK) begin
	       alu_outputs.control  = CONTROL_TRAP;
	       alu_outputs.exc_code = exc_code_BREAKPOINT;
	    end

	    // MRET instruction
	    else if (   (inputs.cur_priv >= m_Priv_Mode)
		     && (inputs.decoded_instr.imm12_I == f12_MRET))
	       begin
                  if (getHardPerms(toCapPipe(inputs.pcc)).accessSysRegs) begin
                     alu_outputs.control = CONTROL_MRET;
                  end else begin
                     alu_outputs.control = CONTROL_TRAP;
                     alu_outputs.exc_code = exc_code_CHERI;
                     alu_outputs.cheri_exc_code = exc_code_CHERI_SysRegsPerm;
                     alu_outputs.cheri_exc_reg = {1'b1, scr_addr_PCC};
                  end
	       end

`ifdef ISA_PRIV_S
	    // SRET instruction
	    else if (   (   (inputs.cur_priv == m_Priv_Mode)
			 || (   (inputs.cur_priv == s_Priv_Mode)
			     && (inputs.mstatus [mstatus_tsr_bitpos] == 0)))
		     && (inputs.decoded_instr.imm12_I == f12_SRET))
	       begin
                  if (getHardPerms(toCapPipe(inputs.pcc)).accessSysRegs) begin
                     alu_outputs.control = CONTROL_SRET;
                  end else begin
                     alu_outputs.control = CONTROL_TRAP;
                     alu_outputs.exc_code = exc_code_CHERI;
                     alu_outputs.cheri_exc_code = exc_code_CHERI_SysRegsPerm;
                     alu_outputs.cheri_exc_reg = {1'b1, scr_addr_PCC};
                  end
	       end
`endif

	    /*
	    // URET instruction (future: Piccolo does not support 'N' extension)
	    else if (   (inputs.cur_priv >= u_Priv_Mode)
		     && (inputs.decoded_instr.imm12_I == f12_URET))
	       begin
		  alu_outputs.control = CONTROL_URET;
	       end
	    */

	    // WFI instruction
	    else if (   (   (inputs.cur_priv == m_Priv_Mode)
			 || (   (inputs.cur_priv == s_Priv_Mode)
			     && (inputs.mstatus [mstatus_tw_bitpos] == 0))
			 || (   (inputs.cur_priv == u_Priv_Mode)
			     && (inputs.misa.n == 1)))
		     && (inputs.decoded_instr.imm12_I == f12_WFI))
	       begin
		  alu_outputs.control = CONTROL_WFI;
	       end

	    else begin
	       alu_outputs.control = CONTROL_TRAP;
	    end
	 end

      else begin
	 alu_outputs.control = CONTROL_TRAP;
      end
   end    // funct3 is f3_PRIV

   // CSRRW, CSRRWI
   else if (f3_is_CSRR_W (funct3)) begin
      WordXL rs1_val = (  (funct3 [2] == 1)
			? extend (inputs.decoded_instr.rs1)    // Immediate zimm
			: inputs.rs1_val);                     // From rs1 reg

      alu_outputs.control   = CONTROL_CSRR_W;
      alu_outputs.val1      = rs1_val;
   end

   // CSRRS, CSRRSI, CSRRC, CSRRCI
   else if (f3_is_CSRR_S_or_C (funct3)) begin
      WordXL rs1_val = (  (funct3 [2] == 1)
			? extend (inputs.decoded_instr.rs1)    // Immediate zimm
			: inputs.rs1_val);                     // From rs1 reg

      alu_outputs.control   = CONTROL_CSRR_S_or_C;
      alu_outputs.val1      = rs1_val;
   end

   // funct3 is not f3_PRIV
   else begin // (funct3 == f3_SYSTEM_ILLEGAL)
      alu_outputs.control = CONTROL_TRAP;
   end

   return alu_outputs;
endfunction: fv_SYSTEM

// ----------------------------------------------------------------
// FP Ops
// Just pass through to the FP stage

`ifdef ISA_F
function ALU_Outputs fv_FP (ALU_Inputs inputs);
   let opcode = inputs.decoded_instr.opcode;
   let funct3 = inputs.decoded_instr.funct3;
   let funct7 = inputs.decoded_instr.funct7;
   let rs2    = inputs.decoded_instr.rs2;

   // Check instruction legality
   // Is the rounding mode legal
   match {.rm, .rm_is_legal} = fv_rmode_check  (funct3, inputs.frm);

   // Is the instruction legal -- if MSTATUS.FS = fs_xs_off, FP instructions
   // are always illegal
   let inst_is_legal = (  (fv_mstatus_fs (inputs.mstatus) == fs_xs_off)
			? False
			: fv_is_fp_instr_legal (funct7,
						rm,
						rs2,
						opcode));

   let alu_outputs         = alu_outputs_base;
   alu_outputs.control     = ((inst_is_legal && rm_is_legal) ? CONTROL_STRAIGHT
			                                     : CONTROL_TRAP);
   alu_outputs.op_stage2   = OP_Stage2_FD;
   alu_outputs.rd          = inputs.decoded_instr.rd;
   alu_outputs.rm          = rm;

   // Operand values
   // The first operand may be from the FPR or GPR
   alu_outputs.val1_frm_gpr= fv_fp_val1_from_gpr (opcode, funct7, rs2);

   // Just copy the rs1_val values from inputs to outputs this covers cases
   // whenever val1 is from GPR
   alu_outputs.val1     = inputs.rs1_val;
   alu_outputs.val1_fast = alu_outputs.val1;

   // Just copy the frs*_val values from inputs to outputs
   alu_outputs.fval1     = inputs.frs1_val;
   alu_outputs.fval2     = inputs.frs2_val;
   alu_outputs.fval3     = inputs.frs3_val;

   alu_outputs.rd_in_fpr = !fv_is_rd_in_GPR (funct7, rs2);

`ifdef INCLUDE_TANDEM_VERIF
   // Normal trace output (if no trap)
   if (alu_outputs.rd_in_fpr)
      alu_outputs.trace_data = mkTrace_F_FRD (fall_through_pc (inputs),
					      fv_trace_isize (inputs),
					      fv_trace_instr (inputs),
					      inputs.decoded_instr.rd,
					      ?,
					      inputs.fflags,
					      inputs.mstatus);
   else
      alu_outputs.trace_data = mkTrace_F_GRD (fall_through_pc (inputs),
					      fv_trace_isize (inputs),
					      fv_trace_instr (inputs),
					      inputs.decoded_instr.rd,
					      ?,
					      inputs.fflags,
					      inputs.mstatus);
`endif
   return alu_outputs;
endfunction
`endif

// ----------------------------------------------------------------
// AMO
// Just pass through to the memory stage

`ifdef ISA_A
function ALU_Outputs fv_AMO (ALU_Inputs inputs);
   IntXL  s_rs1_val = unpack (inputs.rs1_val);
`ifdef ISA_CHERI
   let authority = getFlags(toCapPipe(inputs.pcc))[0] == 1'b0 ? inputs.ddc : inputs.cap_rs1_val;
   let authorityIdx = getFlags(toCapPipe(inputs.pcc))[0] == 1'b0 ? {1,scr_addr_DDC} : {0,inputs.rs1_idx};
   WordXL eaddr = getFlags(toCapPipe(inputs.pcc))[0] == 1'b0 ? getAddr(inputs.ddc) + inputs.rs1_val : getAddr(inputs.cap_rs1_val);
`else
   WordXL eaddr = pack (s_rs1_val);
`endif

   let funct3 = inputs.decoded_instr.funct3;
   let funct5 = inputs.decoded_instr.funct5;
   let funct7 = inputs.decoded_instr.funct7;

   Bool legal_f5 = (   (funct5 == f5_AMO_LR)   || (funct5 == f5_AMO_SC)

		    || (funct5 == f5_AMO_ADD)
		    || (funct5 == f5_AMO_SWAP)

		    || (funct5 == f5_AMO_AND)  || (funct5 == f5_AMO_OR) || (funct5 == f5_AMO_XOR)

		    || (funct5 == f5_AMO_MIN)  || (funct5 == f5_AMO_MINU)
		    || (funct5 == f5_AMO_MAX)  || (funct5 == f5_AMO_MAXU));

   // TODO: Cap width
   Bool legal_width = (   (funct3 == f3_AMO_W)
`ifdef ISA_CHERI
                     || (((funct5 == f5_AMO_LR) || (funct5 == f5_AMO_SC) || (funct5 == f5_AMO_SWAP)) && (funct3 == f3_AMO_CAP))
                     || (((funct5 == f5_AMO_LR)   || (funct5 == f5_AMO_SC)) &&
                          (funct3 == f3_AMO_H
                       || (funct3 == f3_AMO_B)))
`endif
		       || ((xlen == 64) && (funct3 == f3_AMO_D)) );

   let alu_outputs = alu_outputs_base;

   let width_code = funct3;

   alu_outputs.control   = ((legal_f5 && legal_width) ? CONTROL_STRAIGHT : CONTROL_TRAP);
   alu_outputs.op_stage2 = OP_Stage2_AMO;
   alu_outputs.addr      = eaddr;
   alu_outputs.mem_width_code = width_code;
   alu_outputs.mem_unsigned = False;

   alu_outputs = checkValidDereference(alu_outputs, authority, authorityIdx, eaddr, width_code, funct5 != f5_AMO_LR, funct5 != f5_AMO_SC, inputs.cap_rs2_val);

   alu_outputs.val1      = zeroExtend (inputs.decoded_instr.funct7);

`ifdef ISA_CHERI
   alu_outputs.cap_val2      = inputs.cap_rs2_val;
   alu_outputs.val2_cap_not_int = width_code == w_SIZE_CAP;
`endif

   alu_outputs.val2      = inputs.rs2_val;

`ifdef INCLUDE_TANDEM_VERIF
   // Normal trace output (if no trap)
   alu_outputs.trace_data = mkTrace_AMO (fall_through_pc (inputs),
					 funct3,
					 fv_trace_isize (inputs),
					 fv_trace_instr (inputs),
					 inputs.decoded_instr.rd, ?,
					 inputs.rs2_val,
					 eaddr);
`endif
   return alu_outputs;
endfunction
`endif


function ALU_Outputs fv_CHERI (ALU_Inputs inputs, WordXL ddc_base);
    let funct3  = inputs.decoded_instr.funct3;
    let funct5rs2 = inputs.decoded_instr.funct5rs2;
    let funct5rd = inputs.decoded_instr.funct5rd;
    let funct7  = inputs.decoded_instr.funct7;

    let rs2_val = inputs.rs2_val;

    let cs1_val = inputs.cap_rs1_val;

    let cs1_base = getBase(cs1_val);
    let cs1_offset = getOffset(cs1_val);

    let cs2_val = inputs.cap_rs2_val;

    let cs2_base = getBase(cs2_val);
    let cs2_top = getTop(cs2_val);

    let alu_outputs = alu_outputs_base;
    alu_outputs.rd = inputs.decoded_instr.rd;
    alu_outputs.op_stage2 = OP_Stage2_ALU;

    let check_cs1_tagged              = False;
    let check_cs2_tagged              = False;
    let check_ddc_tagged              = False;
    let check_cs1_sealed_with_type    = False;
    let check_cs2_sealed_with_type    = False;
    let check_cs1_unsealed            = False;
    let check_cs1_unsealed_or_sentry  = False;
    let check_cs2_unsealed            = False;
    let check_ddc_unsealed            = False;
    let check_cs1_cs2_types_match     = False;
    let check_cs1_permit_ccall        = False;
    let check_cs2_permit_ccall        = False;
    let check_cs1_permit_x            = False;
    let check_cs2_no_permit_x         = False;
    let check_cs2_permit_unseal       = False;
    let check_cs2_permit_seal         = False;
    let check_cs2_points_to_cs1_type  = False;
    let check_cs2_addr_valid_type     = False;
    let check_cs2_perm_subset_cs1     = False;
    let check_cs2_perm_subset_ddc     = False;

    if (inputs.decoded_instr.opcode == op_AUIPC) begin
        alu_outputs = fv_AUIPC (inputs);
    end else begin
        case (funct3)
        f3_cap_CIncOffsetImmediate: begin
             check_cs1_unsealed = True;

             alu_outputs.val1_source = SET_OFFSET;
             alu_outputs.internal_op1 = cs1_val;
             alu_outputs.internal_op2 = signExtend(inputs.decoded_instr.imm12_I);
             alu_outputs.internal_offset_inc_not_set = True;
        end
        f3_cap_CSetBoundsImmediate: begin
            check_cs1_tagged = True;
            check_cs1_unsealed = True;

            alu_outputs.val1_source = SET_BOUNDS;
            alu_outputs.internal_op2 = zeroExtend(inputs.decoded_instr.imm12_I);
            alu_outputs.internal_bounds_exact = False;
            alu_outputs.check_authority_idx  = zeroExtend(inputs.rs1_idx);
        end
        f3_cap_ThreeOp: begin
            case (funct7)
            f7_cap_CSpecialRW: begin
                if (inputs.decoded_instr.rs2 == scr_addr_PCC && inputs.decoded_instr.rs1 == 0) begin
                    alu_outputs.cap_val1 = toCapPipe(inputs.pcc);
                    alu_outputs.val1_cap_not_int = True;
                end else if (inputs.decoded_instr.rs2 == scr_addr_DDC && inputs.decoded_instr.rs1 == 0) begin
                    alu_outputs.cap_val1 = inputs.ddc;
                    alu_outputs.val1_cap_not_int = True;
                end else begin
                    CapPipe rs1_val = inputs.cap_rs1_val;

                    alu_outputs.control   = CONTROL_SCR_W;
                    alu_outputs.cap_val1  = rs1_val;
                    alu_outputs.val1_cap_not_int = True;
                end
            end
            f7_cap_CSetBounds: begin
                check_cs1_tagged = True;
                check_cs1_unsealed = True;

                alu_outputs.val1_source = SET_BOUNDS;
                alu_outputs.internal_op2 = rs2_val;
                alu_outputs.internal_bounds_exact = False;
                alu_outputs.check_authority_idx  = zeroExtend(inputs.rs1_idx);
            end
            f7_cap_CSetBoundsExact: begin
                check_cs1_tagged = True;
                check_cs1_unsealed = True;

                alu_outputs.val1_source = SET_BOUNDS;
                alu_outputs.internal_op2 = rs2_val;
                alu_outputs.internal_bounds_exact = True;
                alu_outputs.check_authority_idx  = zeroExtend(inputs.rs1_idx);
            end
            f7_cap_CSetOffset: begin
                check_cs1_unsealed = True;

                alu_outputs.val1_source = SET_OFFSET;
                alu_outputs.internal_op1 = cs1_val;
                alu_outputs.internal_op2 = rs2_val;
                alu_outputs.internal_offset_inc_not_set = False;
            end
            f7_cap_CSetAddr: begin
                check_cs1_unsealed = True;

                alu_outputs.val1_source = SET_ADDR;
                alu_outputs.internal_op2 = rs2_val;
            end
            f7_cap_CIncOffset: begin
                check_cs1_unsealed = True;

                alu_outputs.val1_source = SET_OFFSET;
                alu_outputs.internal_op1 = cs1_val;
                alu_outputs.internal_op2 = rs2_val;
                alu_outputs.internal_offset_inc_not_set = True;
            end
            f7_cap_CSeal: begin
                check_cs1_tagged = True;
                check_cs2_tagged = True;
                check_cs1_unsealed = True;
                check_cs2_unsealed = True;
                check_cs2_permit_seal = True;
                check_cs2_addr_valid_type = True;

                alu_outputs.check_enable = True;
                alu_outputs.check_authority = cs2_val;
                alu_outputs.check_authority_idx = {0,inputs.rs2_idx};
                alu_outputs.check_address_low = getAddr(cs2_val);
                alu_outputs.check_address_high = zeroExtend(getAddr(cs2_val));
                alu_outputs.check_inclusive = False;

                alu_outputs.cap_val1 = setKind(cs1_val, SEALED_WITH_TYPE(truncate(getAddr(cs2_val))));
                alu_outputs.val1_cap_not_int = True;
            end
            f7_cap_CCSeal: begin
                check_cs1_tagged = True;

                alu_outputs.check_authority = cs2_val;
                alu_outputs.check_authority_idx = {0,inputs.rs2_idx};
                alu_outputs.check_address_low = getAddr(cs2_val);
                alu_outputs.check_address_high = zeroExtend(getAddr(cs2_val));
                alu_outputs.check_inclusive = False;

                if (   (! isValidCap(cs2_val))
                    || (getAddr(cs2_val) == otype_unsealed_ext)
                    || (getKind(cs1_val) != UNSEALED)) begin
                    alu_outputs.cap_val1 = cs1_val;
                    alu_outputs.val1_cap_not_int = True;
                end else begin
                    alu_outputs.check_enable = True;
                    check_cs1_unsealed = True;
                    check_cs2_unsealed = True;
                    check_cs2_addr_valid_type = True;
                    check_cs2_permit_seal = True;
                    alu_outputs.cap_val1 = setKind(cs1_val, SEALED_WITH_TYPE(truncate(getAddr(cs2_val))));
                    alu_outputs.val1_cap_not_int = True;
                end
            end
            f7_cap_TwoSrc: begin
                case (inputs.decoded_instr.rd)
                    rd_cap_CCall: begin
                        check_cs1_tagged = True;
                        check_cs2_tagged = True;
                        check_cs1_sealed_with_type = True;
                        check_cs2_sealed_with_type = True;
                        check_cs1_cs2_types_match = True;
                        check_cs1_permit_x = True;
                        check_cs2_no_permit_x = True;
                        check_cs1_permit_ccall = True;
                        check_cs2_permit_ccall = True;
                        alu_outputs.val1_cap_not_int = True;
                        alu_outputs.cap_val1 = setKind(cs2_val, UNSEALED);
                        alu_outputs.rd = cCallRD;
                        alu_outputs.pcc = fromCapPipe(maskAddr(setKind(cs1_val, UNSEALED), signExtend(2'b10)));
                        alu_outputs.control = CONTROL_CAPBRANCH;
                        let target = {truncateLSB(getAddr(cs1_val)), 1'b0};
                        alu_outputs = checkValidJump(alu_outputs, True, cs1_val, cs1_base, zeroExtend(inputs.rs1_idx), target);
                    end
                    default: alu_outputs.control = CONTROL_TRAP;
                endcase
            end
            f7_cap_CUnseal: begin
                check_cs1_tagged = True;
                check_cs2_tagged = True;
                check_cs1_sealed_with_type = True;
                check_cs2_unsealed = True;
                check_cs2_points_to_cs1_type = True;
                check_cs2_permit_unseal = True;

                alu_outputs.check_enable = True;
                alu_outputs.check_authority = cs2_val;
                alu_outputs.check_authority_idx = {0,inputs.rs2_idx};
                alu_outputs.check_address_low = getAddr(cs2_val);
                alu_outputs.check_address_high = zeroExtend(getAddr(cs2_val));
                alu_outputs.check_inclusive = False;

                alu_outputs.cap_val1 = setKind(cs1_val, UNSEALED);
                alu_outputs.val1_cap_not_int = True;
            end
            f7_cap_CTestSubset: begin
                let local_cs1_val = cs1_val;
                if (inputs.rs1_idx == 0) local_cs1_val = inputs.ddc;
                if (isValidCap(local_cs1_val) == isValidCap(cs2_val) &&
                    ((getPerms(cs2_val) & getPerms(local_cs1_val)) == getPerms(cs2_val)) ) begin
                    alu_outputs.check_enable = False; // We do not require the check to pass to avoid a trap
                    alu_outputs.check_authority = local_cs1_val;
                    alu_outputs.check_address_low = cs2_base;
                    alu_outputs.check_address_high = cs2_top;
                    alu_outputs.check_inclusive = True;
                    alu_outputs.op_stage2 = OP_Stage2_TestSubset;
                end else begin
                    alu_outputs.val1 = zeroExtend(pack(False));
                end
            end
            f7_cap_CCopyType: begin
                check_cs1_tagged = True;
                check_cs1_unsealed = True;
                case (getKind(cs2_val)) matches
                    tagged UNSEALED: begin
                        alu_outputs.val1 = otype_unsealed_ext;
                    end
                    tagged SENTRY: begin
                        alu_outputs.val1 = otype_sentry_ext;
                    end
                    tagged RES0: begin
                        alu_outputs.val1 = otype_res0_ext;
                    end
                    tagged RES1: begin
                        alu_outputs.val1 = otype_res1_ext;
                    end
                    tagged SEALED_WITH_TYPE .otype: begin
                        alu_outputs.val1_source = SET_ADDR;
                        alu_outputs.internal_op2 = zeroExtend(otype);

                        alu_outputs.check_enable = True;
                        alu_outputs.check_authority = cs1_val;
                        alu_outputs.check_authority_idx = {0,inputs.rs1_idx};
                        alu_outputs.check_address_low = zeroExtend(otype);
                        alu_outputs.check_address_high = zeroExtend(otype);
                        alu_outputs.check_inclusive = False;
                    end
                endcase
            end
            f7_cap_CAndPerm: begin
                check_cs1_tagged = True;
                check_cs1_unsealed = True;

                alu_outputs.cap_val1 = setPerms(cs1_val, pack(getPerms(cs1_val)) & truncate(rs2_val));
                alu_outputs.val1_cap_not_int = True;
            end
            f7_cap_CSetFlags: begin
                check_cs1_unsealed = True;

                alu_outputs.cap_val1 = setFlags(cs1_val, truncate(rs2_val));
                alu_outputs.val1_cap_not_int = True;
            end
            f7_cap_CToPtr: begin
                if (inputs.rs2_idx == 0) begin
                    check_ddc_tagged = True;
                end else begin
                    check_cs2_tagged = True;
                end
                check_cs1_unsealed = True;

                if (isValidCap(cs1_val)) begin
                    alu_outputs.val1 = zeroExtend(getAddr(cs1_val) - (inputs.rs2_idx == 0 ? ddc_base : cs2_base));
                end else begin
                    alu_outputs.val1 = 0;
                end
            end
            f7_cap_CFromPtr: begin
                if (rs2_val == 0) begin
                    alu_outputs.val1 = 0;
                end else begin
                    if (inputs.rs1_idx == 0) begin
                        check_ddc_tagged = True;
                        check_ddc_unsealed = True;
                    end else begin
                        check_cs1_tagged = True;
                        check_cs1_unsealed = True;
                    end

                    alu_outputs.val1_source = SET_OFFSET;
                    alu_outputs.internal_op1 = inputs.rs1_idx == 0 ? inputs.ddc : cs1_val;
                    alu_outputs.internal_op2 = rs2_val;
                    alu_outputs.internal_offset_inc_not_set = False;
                end
            end
            f7_cap_CSub: begin
                alu_outputs.val1 = zeroExtend(getAddr(cs1_val) - getAddr(cs2_val));
            end
            f7_cap_CBuildCap: begin
                let auth = cs1_val;
                let auth_idx = {1'b0, inputs.rs1_idx};
                if (inputs.rs1_idx == 0) begin
                    check_ddc_tagged = True;
                    check_ddc_unsealed = True;
                    check_cs2_perm_subset_ddc = True;
                    auth_idx = {1'b1, scr_addr_DDC};
                    auth = inputs.ddc;
                end else begin
                    check_cs1_tagged = True;
                    check_cs1_unsealed = True;
                    check_cs2_perm_subset_cs1 = True;
                end

                if (!isDerivable(cs2_val)) begin
                    alu_outputs = fv_CHERI_exc(alu_outputs, zeroExtend(inputs.rs2_idx), exc_code_CHERI_Length);
                end

                alu_outputs.check_enable = True;
                alu_outputs.check_authority = auth;
                alu_outputs.check_authority_idx = auth_idx;
                alu_outputs.check_address_low = cs2_base;
                alu_outputs.check_address_high = cs2_top;
                alu_outputs.check_inclusive = True;

                let result = setValidCap(cs2_val, True);
                alu_outputs.cap_val1 = setKind(result, getKind(cs2_val) == SENTRY ? SENTRY : UNSEALED); // Preserve sentries
                alu_outputs.val1_cap_not_int = True;
            end
            f7_cap_Loads: begin
                Bit#(3) widthCode = zeroExtend(funct5rs2[1:0]);
                Bool is_lr = False;
                Bool is_unsigned = funct5rs2[2] == cap_mem_unsigned && funct5rs2[4] == 1'b0;
                Bool illegal = False;
                if (funct5rs2[4] == 1'b1) begin
                    if (funct5rs2[2:0] == 3'b111) begin
                        widthCode = w_SIZE_Q;
                    end else begin
`ifdef ISA_A
                        is_lr = True;
                        widthCode = funct5rs2[2:0];
`else
                        illegal = True;
`endif
                    end
                end
                if ((widthCode > w_SIZE_MAX) || (is_unsigned && widthCode == w_SIZE_MAX)) illegal = True;
                if (illegal) begin
                    // exc_code defaults to exc_code_ILLEGAL_INSTRUCTION
                    alu_outputs.control = CONTROL_TRAP;
                end else begin
                    alu_outputs = memCommon(alu_outputs, False, is_unsigned, funct5rs2[3] == cap_mem_ddc, widthCode, inputs.ddc, cs1_val, inputs.rs1_idx, ?, is_lr, {f5_AMO_LR, 2'b0});
                end
            end
            f7_cap_Stores: begin
                let widthCode = funct5rd[2:0];
                Bool is_sc = funct5rd[4] == 1'b1;
                Bool illegal = False;
                if (is_sc) begin
`ifdef ISA_A
                    alu_outputs.rd = inputs.rs2_idx;
`else
                    illegal = True;
`endif
                end
                if (widthCode > w_SIZE_MAX) illegal = True;
                if (illegal) begin
                    // exc_code defaults to exc_code_ILLEGAL_INSTRUCTION
                    alu_outputs.control = CONTROL_TRAP;
                end else begin
                    alu_outputs = memCommon(alu_outputs, True, ?, funct5rd[3] == cap_mem_ddc, widthCode, inputs.ddc, cs1_val, inputs.rs1_idx, cs2_val, is_sc, {f5_AMO_SC, 2'b0});
                end
            end
            f7_cap_TwoOp: begin
                case (funct5rs2)
                f5rs2_cap_CGetLen: begin
                    Bit#(XLEN) length = truncate(getLength(cs1_val));
                    alu_outputs.val1 = zeroExtend(length);
                end
                f5rs2_cap_CGetBase: begin
                    alu_outputs.val1 = zeroExtend(cs1_base);
                end
                f5rs2_cap_CGetTag: begin
                    alu_outputs.val1 = zeroExtend(pack(isValidCap(cs1_val)));
                end
                f5rs2_cap_CGetSealed: begin
                    alu_outputs.val1 = zeroExtend(pack(getKind(cs1_val) != UNSEALED));
                end
                f5rs2_cap_CRRL: begin
                    alu_outputs.val1_source = GET_PRECISION;
                    alu_outputs.internal_crrl_not_cram = True;
                end
                f5rs2_cap_CRAM: begin
                    alu_outputs.val1_source = GET_PRECISION;
                    alu_outputs.internal_crrl_not_cram = False;
                end
                f5rs2_cap_CMove: begin
                    alu_outputs.cap_val1 = cs1_val;
                    alu_outputs.val1_cap_not_int = True;
                end
                f5rs2_cap_CClearTag: begin
                    alu_outputs.cap_val1 = setValidCap(cs1_val, False);
                    alu_outputs.val1_cap_not_int = True;
                end
                f5rs2_cap_CGetAddr: begin
                    alu_outputs.val1 = zeroExtend(getAddr(cs1_val));
                end
                f5rs2_cap_CSealEntry: begin
                    check_cs1_tagged = True;
                    check_cs1_unsealed = True;
                    check_cs1_permit_x = True;
                    alu_outputs.cap_val1 = setKind(cs1_val, SENTRY);
                    alu_outputs.val1_cap_not_int = True;
                end
                f5rs2_cap_CGetOffset: begin
                    alu_outputs.val1 = zeroExtend(cs1_offset);
                end
                f5rs2_cap_CGetFlags: begin
                    alu_outputs.val1 = zeroExtend(getFlags(cs1_val));
                end
                f5rs2_cap_CGetPerm: begin
                    alu_outputs.val1 = zeroExtend(getPerms(cs1_val));
                end
                f5rs2_cap_CJALR: begin
                    check_cs1_tagged = True;
                    check_cs1_unsealed_or_sentry = True;
                    check_cs1_permit_x = True;

                    Addr  next_pc   = cs1_offset;
                    Addr  ret_pc    = fall_through_pc (inputs);

                    let maskedTarget = maskAddr(cs1_val, signExtend(2'b10));

                    let pcc_addr = getAddr(toCapPipe(inputs.pcc));
                    let target_addr = getPCCBase(inputs.pcc) + next_pc;
                    let cf_info   = CF_Info {cf_op       : CF_JALR,
                                             from_PC     : pcc_addr,
                                             taken       : True,
                                             fallthru_PC : pcc_addr + fall_through_pc_inc(inputs),
                                             taken_PC    : getAddr(maskedTarget) };

                    next_pc[0] = 1'b0;

                    alu_outputs.control   = CONTROL_CAPBRANCH;
                    alu_outputs.cf_info   = cf_info;

                    alu_outputs.addr      = next_pc;
                    alu_outputs.pcc       = fromCapPipe(setKind(maskedTarget, UNSEALED));
                    alu_outputs.val1_source = SET_OFFSET;
                    alu_outputs.internal_op1 = toCapPipe(inputs.pcc);
                    alu_outputs.internal_op2 = fall_through_pc_inc(inputs);
                    alu_outputs.internal_offset_inc_not_set = True;
                    alu_outputs.internal_seal_entry = True;
                    alu_outputs = checkValidJump(alu_outputs, True, cs1_val, cs1_base, {0,inputs.rs1_idx}, getAddr(maskedTarget));
                end
                f5rs2_cap_CGetType: begin
                    case (getKind(cs1_val)) matches
                        tagged UNSEALED: begin
                            alu_outputs.val1 = otype_unsealed_ext;
                        end
                        tagged SENTRY: begin
                            alu_outputs.val1 = otype_sentry_ext;
                        end
                        tagged RES0: begin
                            alu_outputs.val1 = otype_res0_ext;
                        end
                        tagged RES1: begin
                            alu_outputs.val1 = otype_res1_ext;
                        end
                        tagged SEALED_WITH_TYPE .otype: begin
                            alu_outputs.val1 = zeroExtend(otype);
                        end
                    endcase
                end
                default: alu_outputs.control = CONTROL_TRAP;
                endcase
            end
            default: alu_outputs.control = CONTROL_TRAP;
            endcase
        end
        default: alu_outputs.control = CONTROL_TRAP;
        endcase
    end

    case(alu_outputs.val1_source)
    SET_OFFSET: begin
        let result = modifyOffset(alu_outputs.internal_op1, alu_outputs.internal_op2, alu_outputs.internal_offset_inc_not_set);
        if (alu_outputs.internal_seal_entry) begin
            result.value = setKind(result.value, SENTRY);
        end
        alu_outputs.cap_val1 = result.value;
        alu_outputs.val1_cap_not_int = True;
    end
    SET_BOUNDS: begin
        let result = setBounds(cs1_val, alu_outputs.internal_op2);
        alu_outputs.cap_val1 = result.value;
        alu_outputs.val1_cap_not_int = True;

        alu_outputs.check_enable = True;
        alu_outputs.check_authority = cs1_val;
        alu_outputs.check_inclusive = True;
        alu_outputs.check_address_low = getAddr(cs1_val);
        alu_outputs.check_address_high = zeroExtend(getAddr(cs1_val)) + zeroExtend(alu_outputs.internal_op2);
        alu_outputs.check_exact_enable = alu_outputs.internal_bounds_exact;
        alu_outputs.check_exact_success = result.exact;
    end
    GET_PRECISION: begin
        CapReg nullCapReg = nullCap;
        let result = getRepresentableAlignmentMask(nullCapReg, inputs.rs1_val);
        if (alu_outputs.internal_crrl_not_cram) begin
            result = (inputs.rs1_val + ~result) & result;
        end
        alu_outputs.val1 = result;
    end
    SET_ADDR: begin
        let result = setAddr(cs1_val, alu_outputs.internal_op2);
        alu_outputs.cap_val1 = result.value;
        alu_outputs.val1_cap_not_int = True;
    end
    endcase

    if      (check_cs1_tagged             && !isValidCap(cs1_val))
        alu_outputs = fv_CHERI_exc(alu_outputs, zeroExtend(inputs.rs1_idx), exc_code_CHERI_Tag);
    else if (check_cs2_tagged             && !isValidCap(cs2_val))
        alu_outputs = fv_CHERI_exc(alu_outputs, zeroExtend(inputs.rs2_idx), exc_code_CHERI_Tag);
    else if (check_ddc_tagged             && !isValidCap(inputs.ddc))
        alu_outputs = fv_CHERI_exc(alu_outputs, {1'b1, scr_addr_DDC}      , exc_code_CHERI_Tag);
    else if (check_cs1_sealed_with_type   && (getKind(cs1_val) matches tagged SEALED_WITH_TYPE ._ ? False : True))
        alu_outputs = fv_CHERI_exc(alu_outputs, zeroExtend(inputs.rs1_idx), exc_code_CHERI_Seal);
    else if (check_cs2_sealed_with_type   && (getKind(cs2_val) matches tagged SEALED_WITH_TYPE ._ ? False : True))
        alu_outputs = fv_CHERI_exc(alu_outputs, zeroExtend(inputs.rs2_idx), exc_code_CHERI_Seal);
    else if (check_cs1_unsealed           && isValidCap(cs1_val) && getKind(cs1_val) != UNSEALED)
        alu_outputs = fv_CHERI_exc(alu_outputs, zeroExtend(inputs.rs1_idx), exc_code_CHERI_Seal);
    else if (check_cs1_unsealed_or_sentry && isValidCap(cs1_val) && getKind(cs1_val) != UNSEALED && getKind(cs1_val) != SENTRY)
        alu_outputs = fv_CHERI_exc(alu_outputs, zeroExtend(inputs.rs1_idx), exc_code_CHERI_Seal);
    else if (check_cs2_unsealed           && isValidCap(cs2_val) && getKind(cs2_val) != UNSEALED)
        alu_outputs = fv_CHERI_exc(alu_outputs, zeroExtend(inputs.rs2_idx), exc_code_CHERI_Seal);
    else if (check_ddc_unsealed           && isValidCap(inputs.ddc) && getKind(inputs.ddc) != UNSEALED)
        alu_outputs = fv_CHERI_exc(alu_outputs, {1'b1, scr_addr_DDC}      , exc_code_CHERI_Seal);
    else if (check_cs1_cs2_types_match    && getKind(cs1_val).SEALED_WITH_TYPE != getKind(cs2_val).SEALED_WITH_TYPE) // Already checked SEALED_WITH_TYPE
        alu_outputs = fv_CHERI_exc(alu_outputs, zeroExtend(inputs.rs1_idx), exc_code_CHERI_Type);
    else if (check_cs1_permit_ccall       && !getHardPerms(cs1_val).permitCCall)
        alu_outputs = fv_CHERI_exc(alu_outputs, zeroExtend(inputs.rs1_idx), exc_code_CHERI_CCallPerm);
    else if (check_cs2_permit_ccall       && !getHardPerms(cs2_val).permitCCall)
        alu_outputs = fv_CHERI_exc(alu_outputs, zeroExtend(inputs.rs2_idx), exc_code_CHERI_CCallPerm);
    else if (check_cs1_permit_x           && !getHardPerms(cs1_val).permitExecute)
        alu_outputs = fv_CHERI_exc(alu_outputs, zeroExtend(inputs.rs1_idx), exc_code_CHERI_XPerm);
    else if (check_cs2_no_permit_x        && getHardPerms(cs2_val).permitExecute)
        alu_outputs = fv_CHERI_exc(alu_outputs, zeroExtend(inputs.rs2_idx), exc_code_CHERI_XPerm);
    else if (check_cs2_permit_unseal      && !getHardPerms(cs2_val).permitUnseal)
        alu_outputs = fv_CHERI_exc(alu_outputs, zeroExtend(inputs.rs2_idx), exc_code_CHERI_UnsealPerm);
    else if (check_cs2_permit_seal        && !getHardPerms(cs2_val).permitSeal)
        alu_outputs = fv_CHERI_exc(alu_outputs, zeroExtend(inputs.rs2_idx), exc_code_CHERI_SealPerm);
    else if (check_cs2_points_to_cs1_type && getAddr(cs2_val) != zeroExtend(getKind(cs1_val).SEALED_WITH_TYPE)) // Already checked SEALED_WITH_TYPE
        alu_outputs = fv_CHERI_exc(alu_outputs, zeroExtend(inputs.rs2_idx), exc_code_CHERI_Type);
    else if (check_cs2_addr_valid_type    && !validAsType(cs2_val, truncate(getAddr(cs2_val))))
        alu_outputs = fv_CHERI_exc(alu_outputs, zeroExtend(inputs.rs2_idx), exc_code_CHERI_Length);
    else if (check_cs2_perm_subset_cs1    && (getPerms(cs1_val) & getPerms(cs2_val)) != getPerms(cs2_val))
        alu_outputs = fv_CHERI_exc(alu_outputs, zeroExtend(inputs.rs2_idx), exc_code_CHERI_Software);
    else if (check_cs2_perm_subset_ddc    && (getPerms(inputs.ddc) & getPerms(cs2_val)) != getPerms(cs2_val))
        alu_outputs = fv_CHERI_exc(alu_outputs, zeroExtend(inputs.rs2_idx), exc_code_CHERI_Software);

    // Normal trace output (if no trap)
    //alu_outputs.trace_data = mkTrace_I_RD (fall_through_pc (inputs),
					//  fv_trace_isize (inputs),
					//  fv_trace_instr (inputs),
					//  inputs.decoded_instr.rd,
					//  getAddr(rd_val));
   return alu_outputs;
endfunction
`endif

// ----------------------------------------------------------------
// Top-level ALU function

function ALU_Outputs fv_ALU (ALU_Inputs inputs);
   let alu_outputs = alu_outputs_base;

   alu_outputs.val1_fast = inputs.rs1_val;
   alu_outputs.val2_fast = inputs.rs2_val;

   ALUInt addop1 = ?;
   ALUInt addop2 = ?;
   ALUInt shiftop = ?;

   ALUInt cmpop1 = ?;
   ALUInt cmpop2 = ?;

   let rs1_val = inputs.rs1_val;
   let rs2_val = inputs.rs2_val;

   IntXL s_rs1_val = unpack (rs1_val);
   IntXL s_rs2_val = unpack (rs2_val);

   Bit #(1) instr_b30 = inputs.instr [30];
   Bool subtract = ((inputs.decoded_instr.opcode == op_OP) && (instr_b30 == 1'b1));

   let funct3 = inputs.decoded_instr.funct3;
   let funct10 = inputs.decoded_instr.funct10;

   IntXL iv = extend (unpack ({inputs.decoded_instr.imm20_U, 12'b0}));
   IntXL pc_s = unpack (inputs.pc);

   IntXL imm_i_s = extend (unpack (inputs.decoded_instr.imm12_I));
   IntXL imm_s_s = extend (unpack (inputs.decoded_instr.imm12_S));

   Bit #(32) rs1_val_b32 = rs1_val [31:0];
   Bit #(32) rs2_val_b32 = rs2_val [31:0];

   Int #(32) s_rs1_val_b32 = unpack (rs1_val_b32);
   Int #(32) s_rs2_val_b32 = unpack (rs2_val_b32);

   Bit #(TLog #(XLEN)) shamt = (  (inputs.decoded_instr.opcode == op_OP_IMM)
                               || (inputs.decoded_instr.opcode == op_OP_IMM_32))
                                  ? truncate (inputs.decoded_instr.imm12_I)
                                  : truncate (rs2_val);

   Bool shamt5_is_0 = inputs.decoded_instr.imm12_I[5] == 0;
   Bool shift_left = ?;
   Bit #(1) shift_arith = ?;

   Bool trap = False;

   let fallthru_pc_inc = fall_through_pc_inc (inputs);
   let fallthru_pc = fall_through_pc (inputs);
`ifdef ISA_CHERI
   let pcc_addr = getAddr (toCapPipe (inputs.pcc));
   let fallthru_pcc_inc = fallthru_pc_inc;
   let fallthru_pcc_addr = fallthru_pc;


   // any time you set the authority, you should also set the authority_base
   // and the authority_top. authority_base and authority_top are the fields
   // that are actually used in stage 2 for checking.
   // In the majority of cases, these should all be set in the first wave of
   // `if` statements.
   // In some cases (for example when the _base or _top need values from the
   // adder, it is acceptable to set these in the second wave of `if` statements
   CapPipe authority = ?;
   Bit #(6) authorityIdx = ?;
   Bit #(XLEN) authority_base = ?;
   Bit #(TAdd #(XLEN, 1)) authority_top = ?;

   // When you need to perform an add to get authority_top (for example for branching)
   // you can make this signal True to signal that the output should be taken from the
   // sum
   Bool check_address_high_from_sum = False;
   Bit #(TAdd #(XLEN, 1)) check_address_high = ?;
   Bit #(XLEN) check_address_low = ?;

   Bool is_load = False;
   Bool is_store = False;
   WordXL mem_writedata = ?;
   Bit #(3) width_code = ?;

   CapPipe data = ?;

   let funct5rs2 = inputs.decoded_instr.funct5rs2;
   let funct5rd = inputs.decoded_instr.funct5rd;
   let funct7  = inputs.decoded_instr.funct7;

   let ddc_base = getBase (inputs.ddc);
   let ddc_top = getTop (inputs.ddc);

   // fake values (for checking how big these actually are)
   //let pcc_base = ddc_base;
   //let pcc_top  = ddc_top;
   let pcc_base = getBase (toCapPipe (inputs.pcc));
   let pcc_top = getTop (toCapPipe (inputs.pcc));

   let cs1_val = inputs.cap_rs1_val;
   // fake values (for checking how big these actually are)
   //let cs1_base = ddc_base;
   //let cs1_top  = ddc_top;
   let cs1_base = getBase(cs1_val);
   let cs1_top = getTop (cs1_val);
   let cs1_offset = getOffset(cs1_val);

   let cs2_val = inputs.cap_rs2_val;
   // fake values (for checking how big these actually are)
   //let cs2_base = ddc_base;
   //let cs2_top  = ddc_top;
   let cs2_base = getBase(cs2_val);
   let cs2_top = getTop(cs2_val);


   let check_cs1_tagged              = False;
   let check_cs2_tagged              = False;
   let check_ddc_tagged              = False;
   let check_cs1_sealed_with_type    = False;
   let check_cs2_sealed_with_type    = False;
   let check_cs1_unsealed            = False;
   let check_cs1_unsealed_or_sentry  = False;
   let check_cs2_unsealed            = False;
   let check_ddc_unsealed            = False;
   let check_cs1_cs2_types_match     = False;
   let check_cs1_permit_ccall        = False;
   let check_cs2_permit_ccall        = False;
   let check_cs1_permit_x            = False;
   let check_cs2_no_permit_x         = False;
   let check_cs2_permit_unseal       = False;
   let check_cs2_permit_seal         = False;
   let check_cs2_points_to_cs1_type  = False;
   let check_cs2_addr_valid_type     = False;
   let check_cs2_perm_subset_cs1     = False;
   let check_cs2_perm_subset_ddc     = False;

   let check_cs1_permit_load    = False;
   let check_cs2_permit_load    = False;
   let check_ddc_permit_load    = False;
   let check_cs1_permit_load_cap    = False;
   let check_cs2_permit_load_cap    = False;
   let check_ddc_permit_load_cap    = False;
   let check_cs1_permit_store   = False;
   let check_cs2_permit_store   = False;
   let check_ddc_permit_store   = False;
   let check_cs1_permit_store_cap   = False;
   let check_cs2_permit_store_cap   = False;
   let check_ddc_permit_store_cap   = False;

`endif

   let cf_info = CF_Info {cf_op       : ?,
                          from_PC     : inputs.pc,
                          taken       : ?,
                          fallthru_PC : fallthru_pc,
                          taken_PC    : ?};







   if (inputs.decoded_instr.opcode == op_BRANCH) begin
      //alu_outputs = fv_BRANCH (inputs);
      IntXL offset = extend (unpack (inputs.decoded_instr.imm13_SB));
`ifdef ISA_CHERI
      addop1 = {unpack ( pcc_addr), 1'b0};
`else
      addop1 = {unpack (inputs.pc), 1'b0};
`endif
      addop2 = {  pack (   offset), 1'b0};

      if (funct3 == f3_BEQ
       || funct3 == f3_BNE
       || funct3 == f3_BLTU
       || funct3 == f3_BGEU) begin
         cmpop1 = zeroExtend(rs1_val);
         cmpop2 = zeroExtend(rs2_val);
      end else if (funct3 == f3_BLT
                || funct3 == f3_BGE) begin
         cmpop1 = pack (signExtend (s_rs1_val));
         cmpop2 = pack (signExtend (s_rs2_val));
      end else begin
         trap = True;
      end

`ifdef ISA_CHERI
      authority = toCapPipe (inputs.pcc);
      authorityIdx = {1, scr_addr_PCC};
      authority_base = pcc_base;
      authority_top = pcc_top;
      alu_outputs.check_inclusive = True;
      width_code = 1;
`endif
   end

   else if (inputs.decoded_instr.opcode == op_JAL) begin
      IntXL offset = extend (unpack (inputs.decoded_instr.imm21_UJ));
`ifdef ISA_CHERI
      addop1 = {unpack ( pcc_addr), 1'b0};
`else
      addop1 = {unpack (inputs.pc), 1'b0};
`endif
      addop2 = {  pack (   offset), 1'b0};

`ifdef ISA_CHERI
      authority = toCapPipe (inputs.pcc);
      authorityIdx = {1, scr_addr_PCC};
      authority_base = pcc_base;
      authority_top = pcc_top;
      alu_outputs.check_inclusive = True;
      width_code = 1;
`endif
   end

   else if (inputs.decoded_instr.opcode == op_JALR) begin
      IntXL offset = extend (unpack (inputs.decoded_instr.imm12_I));
      addop1 = {  pack (s_rs1_val), 1'b0};
      addop2 = {  pack (   offset), 1'b0};
`ifdef ISA_CHERI
      authority = toCapPipe (inputs.pcc);
      authorityIdx = {1, scr_addr_PCC};
      authority_base = pcc_base;
      authority_top = pcc_top;
      alu_outputs.check_inclusive = True;
      width_code = 1;
`endif
   end

   else if (   (   (inputs.decoded_instr.opcode == op_OP_IMM)
		|| (inputs.decoded_instr.opcode == op_OP))
	    && (   (inputs.decoded_instr.funct3 == f3_SLLI)
		|| (inputs.decoded_instr.funct3 == f3_SRLI)
		|| (inputs.decoded_instr.funct3 == f3_SRAI))) begin
      if (funct3 == f3_SLLI) begin
         // SLLI
         shift_left = True;
         shift_arith = 0;
         shiftop = {shift_arith, reverseBits (rs1_val)};
      end else begin
         shift_left = False;
         shift_arith = instr_b30;
         if (shift_arith == 1) begin
            // SRA/SRAI
            shiftop = signExtend (rs1_val);
         end else begin
            // SRL/SRLI
            shiftop = zeroExtend (rs1_val);
         end
      end
      trap = (rv_version == RV32) && shamt5_is_0;
   end

   else if (   (inputs.decoded_instr.opcode == op_OP_IMM)
	    || (inputs.decoded_instr.opcode == op_OP)) begin
      //alu_outputs = fv_OP_and_OP_IMM (inputs);
      IntXL s_rs2_val_local = s_rs2_val;
      WordXL rs2_val_local = rs2_val;
      if (inputs.decoded_instr.opcode == op_OP_IMM) begin
         s_rs2_val_local = extend (unpack (inputs.decoded_instr.imm12_I));
         rs2_val_local   = pack (s_rs2_val_local);
      end

      if ((funct3 == f3_ADDI) && (!subtract)) begin
         addop1 = {pack (s_rs1_val), 1'b0};
         addop2 = {pack (rs2_val_local), 1'b0};
      end
      else if ((funct3 == f3_ADDI) && (subtract)) begin
         addop1 = {pack (s_rs1_val), 1'b1};
         addop2 = {~ (pack (rs2_val_local)), 1'b1};
      end
      else if (funct3 == f3_SLTI) begin
         cmpop1 = pack (signExtend (s_rs1_val));
         cmpop2 = pack (signExtend (s_rs2_val_local));
      end
      else if (funct3 == f3_SLTIU) begin
         cmpop1 = zeroExtend (rs1_val);
         cmpop2 = zeroExtend (rs2_val_local);
      end
      else if (  funct3 == f3_XORI
              || funct3 == f3_ORI
              || funct3 == f3_ANDI) begin
         // do nothing, but don't set trap = True
      end else begin
         trap = True;
      end
   end
`ifdef RV64
   else if (inputs.decoded_instr.opcode == op_OP_IMM_32) begin
      //alu_outputs = fv_OP_IMM_32 (inputs);
      if (funct3 == f3_ADDIW) begin
         IntXL s_rs2_val_local = extend (unpack (inputs.decoded_instr.imm12_I));
         addop1 = {pack       (s_rs1_val), 1'b0};
         addop2 = {pack (s_rs2_val_local), 1'b0};
      end
      else if ((funct3 == f3_SLLIW) && shamt5_is_0) begin
         shift_left = True;
         shift_arith = 0;
         shiftop = {shift_arith, reverseBits (extend (rs1_val_b32))};
      end
      else if ((funct3 == f3_SRxIW) && shamt5_is_0) begin
         shift_left = False;
         shift_arith = instr_b30;
         if (shift_arith == 1) begin
            shiftop = signExtend (rs1_val_b32);
         end
         else begin
            shiftop = extend (rs1_val_b32);
         end
      end
      else begin
         trap = True;
      end
   end

   // Remaining op_OP_32 (excluding 'M' ops)
   else if (inputs.decoded_instr.opcode == op_OP_32) begin
      //alu_outputs = fv_OP_32 (inputs);
      shamt = zeroExtend (shamt[4:0]);
      if (funct10 == f10_ADDW) begin
         addop1 = extend ({pack (s_rs1_val_b32), 1'b0});
         addop2 = extend ({pack (s_rs2_val_b32), 1'b0});
      end
      else if (funct10 == f10_SUBW) begin
         addop1 = extend ({ pack (s_rs1_val_b32), 1'b1});
         addop2 = extend ({~pack (s_rs2_val_b32), 1'b1});
      end
      else if (funct10 == f10_SLLW) begin
         shift_left = True;
         shift_arith = 0;
         shiftop = {shift_arith, reverseBits (signExtend (rs1_val_b32))};
      end
      else if (funct10 == f10_SRLW) begin
         shift_left = False;
         shift_arith = 0;
         shiftop = {shift_arith, shamt > 0 ? zeroExtend (rs1_val_b32) : signExtend (rs1_val_b32)};
      end
      else if (funct10 == f10_SRAW) begin
         shift_left = False;
         shift_arith = 1;
         shiftop = signExtend (rs1_val_b32);
      end
      else begin
         trap = True;
      end
   end
`endif
   // If we are in CHERI, we might need to do a setOffset for AUIPCC, so moved to fv_CHERI
   else if (inputs.decoded_instr.opcode == op_AUIPC) begin
      //alu_outputs = fv_AUIPC (inputs);
      addop1 = {pack (pcc_addr), 1'b0};
      addop2 = {pack (      iv), 1'b0};
      alu_outputs.op_stage2 = OP_Stage2_ALU;
      alu_outputs.rd        = inputs.decoded_instr.rd;
`ifdef ISA_CHERI
      if (getFlags(toCapPipe(inputs.pcc))[0] == 1'b1) begin
         alu_outputs.val1_source = SET_OFFSET;
         alu_outputs.internal_op1 = toCapPipe(inputs.pcc);
         alu_outputs.internal_op2 = pack(iv);
         alu_outputs.internal_offset_inc_not_set = True;
      end
`endif
      // TODO CHERI tests that are in fv_CHERI
   end
   else if (inputs.decoded_instr.opcode == op_LOAD) begin
      //alu_outputs = fv_LD (inputs, Invalid);
      alu_outputs.op_stage2 = OP_Stage2_LD;
      alu_outputs.rd        = inputs.decoded_instr.rd;
      alu_outputs.mem_unsigned   = unpack (funct3[2]);
      Maybe #(Bit #(3)) size = Invalid;
      Bool legal_LD = (  isValid (size)
                      || (funct3 == f3_LB)
                      || (funct3 == f3_LH) || (funct3 == f3_LHU)
                      || (funct3 == f3_LW)
`ifdef RV64
                      || (funct3 == f3_LWU)
                      || (funct3 == f3_LD)
`endif
`ifdef ISA_F
                      || (funct3 == f3_LFW)
`endif
`ifdef ISA_D
                      || (funct3 == f3_FLD)
`endif
                      );

      Bool legal_FP_LD = True;
      IntXL s_imm_i = extend (unpack (inputs.decoded_instr.imm12_I));
`ifdef ISA_F
      if (inputs.decoded_instr.opcode == op_LOAD_FP) begin
         trap = (fv_mstatus_fs (inputs.mstatus) != fs_xs_off);
      end
      alu_outputs.rd_in_fpr = (opcode == op_LOAD_FP);
`endif
      alu_outputs.control        = (trap ? CONTROL_TRAP
                                         : CONTROL_STRAIGHT);

`ifdef ISA_CHERI
      if (valueOf (XLEN) == 32 && inputs.decoded_instr.funct3 == f3_LD) size = Valid (w_SIZE_D);
      is_load = True;
      width_code = fromMaybe ({0, funct3[1:0]}, size);
      Bool useDDC = getFlags (toCapPipe (inputs.pcc))[0] == 1'b0;

      authority = useDDC ? inputs.ddc
                         : inputs.cap_rs1_val;
      authorityIdx = useDDC ? {1,   scr_addr_DDC}
                            : {0, inputs.rs1_idx};
      authority_base = useDDC ? ddc_base
                              : cs1_base;
      authority_top  = useDDC ? ddc_top
                              : cs1_top;

      alu_outputs.check_enable = True;
      alu_outputs.check_inclusive = True;
      // check_address_low and _high are set later when we have the eaddr
      if (useDDC) begin
         check_ddc_tagged = True;
         check_ddc_unsealed = True;
         check_ddc_permit_load = True;
         check_ddc_permit_load_cap = width_code == w_SIZE_CAP;
      end else begin
         check_cs1_tagged = True;
         check_cs1_unsealed = True;
         check_cs1_permit_load = True;
         check_cs1_permit_load_cap = width_code == w_SIZE_CAP;
      end
      addop1 = useDDC ? {pack (getAddr (inputs.ddc))        , 1'b0}
                      : {pack (getAddr (inputs.cap_rs1_val)), 1'b0};
      //addop2 = getFlags (toCapPipe (inputs.pcc))[0] == 1'b0
      //           ? {inputs.rs1_val + pack (s_imm_i), 1'b0}
      //           : {                 pack (s_imm_i), 1'b0};
      addop2 = {pack (s_imm_i) + (useDDC ? pack (inputs.rs1_val)
                                         :                    0), 1'b0};
`else
      addop1 = {pack (s_rs1_val), 1'b0};
      addop2 = {pack (  s_imm_i), 1'b0};
`endif

   end

   else if (inputs.decoded_instr.opcode == op_STORE) begin
      //alu_outputs = fv_ST (inputs);
      IntXL s_imm_s = extend (unpack (inputs.decoded_instr.imm12_S));
      alu_outputs.val2 = inputs.rs2_val;
      alu_outputs.op_stage2 = OP_Stage2_ST;
      alu_outputs.mem_unsigned = False;

      Bool legal_ST = (  (funct3 == f3_SB)
                      || (funct3 == f3_SH)
                      || (funct3 == f3_SW)
`ifdef ISA_CHERI
`ifdef RV64
                      || (funct3 == f3_SQ)
`else
                      || (funct3 == f3_SD)
`endif
`endif
`ifdef RV64
                      || (funct3 == f3_SD)
`endif
`ifdef ISA_F
                      || (funct3 == f3_FSW)
`endif
`ifdef ISA_D
                      || (funct3 == f3_FSD)
`endif
                      );

      Bool legal_FP_ST = True;
`ifdef ISA_F
      if (inputs.decoded_instr.opcode == op_STORE_FP) begin
         legal_FP_ST = (fv_mstatus_fs (inputs.mstatus) != fs_xs_off);

         // note that the source data register for this store is in the FPR
         alu_outputs.rs_frm_fpr = True;
      end
      alu_outputs.fval2 = inputs.frs2_val;
`endif
      trap = !(legal_ST && legal_FP_ST);
      alu_outputs.control = trap ? CONTROL_TRAP : CONTROL_STRAIGHT;

`ifdef ISA_CHERI
      is_store = True;
      width_code = funct3;

      alu_outputs.cap_val2 = inputs.cap_rs2_val;
      alu_outputs.val2_cap_not_int = width_code == w_SIZE_CAP;

      Bool useDDC = getFlags(toCapPipe (inputs.pcc))[0] == 1'b0;
      authority    = useDDC ? inputs.ddc
                            : inputs.cap_rs1_val;
      authorityIdx = useDDC ? {1,   scr_addr_DDC}
                            : {0, inputs.rs1_idx};
      authority_base = useDDC ? ddc_base
                              : cs1_base;
      authority_top  = useDDC ? ddc_top
                              : cs1_top;
      data = inputs.cap_rs2_val;

      alu_outputs.check_enable = True;
      alu_outputs.check_inclusive = True;
      // check_address_low and _high are set later when we have the eaddr
      if (useDDC) begin
         check_ddc_tagged = True;
         check_ddc_unsealed = True;
         check_ddc_permit_store = True;
         check_ddc_permit_store_cap = width_code == w_SIZE_CAP;
      end else begin
         check_cs1_tagged = True;
         check_cs1_unsealed = True;
         check_cs1_permit_store = True;
         check_cs1_permit_store_cap = width_code == w_SIZE_CAP;
      end

      addop1 = useDDC ? {pack (getAddr (             inputs.ddc)), 1'b0}
                      : {pack (getAddr (     inputs.cap_rs1_val)), 1'b0};
      //addop2 = getFlags(toCapPipe (inputs.pcc))[0] == 1'b0
      //         ? {pack (s_rs1_val + s_imm_s), 1'b0}
      //         : {pack (            s_imm_s), 1'b0};
      addop2 = {pack (s_imm_s) + (useDDC ? pack (s_rs1_val)
                                         :               0), 1'b0};
`else
      addop1 = {pack (s_rs1_val), 1'b0};
      addop2 = {pack (  s_imm_s), 1'b0};
`endif

   end


`ifdef ISA_CHERI
   else if ((inputs.decoded_instr.opcode == op_cap_Manip)) begin
      alu_outputs.rd = inputs.decoded_instr.rd;
      alu_outputs.op_stage2 = OP_Stage2_ALU;
      case (funct3)
      f3_cap_CIncOffsetImmediate: begin
         check_cs1_unsealed = True;

         alu_outputs.val1_source = SET_OFFSET;
         alu_outputs.internal_op1 = cs1_val;
         alu_outputs.internal_op2 = signExtend(inputs.decoded_instr.imm12_I);
         alu_outputs.internal_offset_inc_not_set = True;
      end
      f3_cap_CSetBoundsImmediate: begin
         check_cs1_tagged = True;
         check_cs1_unsealed = True;

         alu_outputs.val1_source = SET_BOUNDS;
         alu_outputs.internal_op2 = zeroExtend(inputs.decoded_instr.imm12_I);
         alu_outputs.internal_bounds_exact = False;
         //alu_outputs.check_authority_idx  = zeroExtend(inputs.rs1_idx);
         authorityIdx = zeroExtend (inputs.rs1_idx);
      end
      f3_cap_ThreeOp: begin
         case (funct7)
         f7_cap_CSpecialRW: begin
            if (inputs.decoded_instr.rs2 == scr_addr_PCC && inputs.decoded_instr.rs1 == 0) begin
               alu_outputs.cap_val1 = toCapPipe(inputs.pcc);
               alu_outputs.val1_cap_not_int = True;
            end else if (inputs.decoded_instr.rs2 == scr_addr_DDC && inputs.decoded_instr.rs1 == 0) begin
               alu_outputs.cap_val1 = inputs.ddc;
               alu_outputs.val1_cap_not_int = True;
            end else begin
               CapPipe rs1_val = inputs.cap_rs1_val;

               alu_outputs.control   = CONTROL_SCR_W;
               alu_outputs.cap_val1  = rs1_val;
               alu_outputs.val1_cap_not_int = True;
            end
         end
         f7_cap_CSetBounds: begin
            check_cs1_tagged = True;
            check_cs1_unsealed = True;

            alu_outputs.val1_source = SET_BOUNDS;
            alu_outputs.internal_op2 = rs2_val;
            alu_outputs.internal_bounds_exact = False;
            //alu_outputs.check_authority_idx  = zeroExtend(inputs.rs1_idx);
            authorityIdx = zeroExtend (inputs.rs1_idx);
         end
         f7_cap_CSetBoundsExact: begin
            check_cs1_tagged = True;
            check_cs1_unsealed = True;

            alu_outputs.val1_source = SET_BOUNDS;
            alu_outputs.internal_op2 = rs2_val;
            alu_outputs.internal_bounds_exact = True;
            //alu_outputs.check_authority_idx  = zeroExtend(inputs.rs1_idx);
            authorityIdx = zeroExtend (inputs.rs1_idx);
         end
         f7_cap_CSetOffset: begin
            check_cs1_unsealed = True;

            alu_outputs.val1_source = SET_OFFSET;
            alu_outputs.internal_op1 = cs1_val;
            alu_outputs.internal_op2 = rs2_val;
            alu_outputs.internal_offset_inc_not_set = False;
         end
         f7_cap_CSetAddr: begin
            check_cs1_unsealed = True;

            alu_outputs.val1_source = SET_ADDR;
            alu_outputs.internal_op2 = rs2_val;
         end
         f7_cap_CIncOffset: begin
            check_cs1_unsealed = True;

            alu_outputs.val1_source = SET_OFFSET;
            alu_outputs.internal_op1 = cs1_val;
            alu_outputs.internal_op2 = rs2_val;
            alu_outputs.internal_offset_inc_not_set = True;
         end
         f7_cap_CSeal: begin
            check_cs1_tagged = True;
            check_cs2_tagged = True;
            check_cs1_unsealed = True;
            check_cs2_unsealed = True;
            check_cs2_permit_seal = True;
            check_cs2_addr_valid_type = True;

            alu_outputs.check_enable = True;
            //alu_outputs.check_authority = cs2_val;
            //alu_outputs.check_authority_idx = {0,inputs.rs2_idx};
            authority = cs2_val;
            authorityIdx = {0,inputs.rs2_idx};
            authority_base = cs2_base;
            authority_top  = cs2_top;
            // TODO ALU_CHECK_ADDR
            check_address_low = getAddr(cs2_val);
            check_address_high = zeroExtend(getAddr(cs2_val));
            alu_outputs.check_inclusive = False;

            // TODO SHARE_SEAL
            // TODO maybe this can be moved later? could have a SEAL val1_source
            alu_outputs.cap_val1 = setKind(cs1_val, SEALED_WITH_TYPE(truncate(getAddr(cs2_val))));
            alu_outputs.val1_cap_not_int = True;
         end
         f7_cap_CCSeal: begin
            check_cs1_tagged = True;

            authority = cs2_val;
            authorityIdx = {0,inputs.rs2_idx};
            authority_base = cs2_base;
            authority_top  = cs2_top;
            // TODO ALU_CHECK_ADDR
            check_address_low = getAddr(cs2_val);
            check_address_high = zeroExtend(getAddr(cs2_val));
            alu_outputs.check_inclusive = False;

            if (  (! isValidCap(cs2_val))
               || (getAddr(cs2_val) == otype_unsealed_ext)
               || (getKind(cs1_val) != UNSEALED)
               ) begin
               alu_outputs.cap_val1 = cs1_val;
               alu_outputs.val1_cap_not_int = True;
            end else begin
               alu_outputs.check_enable = True;
               check_cs1_unsealed = True;
               check_cs2_unsealed = True;
               check_cs2_addr_valid_type = True;
               check_cs2_permit_seal = True;
               // TODO SHARE_SEAL
               // TODO maybe this can be moved later? could have a SEAL val1_source
               alu_outputs.cap_val1 = setKind(cs1_val, SEALED_WITH_TYPE(truncate(getAddr(cs2_val))));
               alu_outputs.val1_cap_not_int = True;
            end
         end
         f7_cap_TwoSrc: begin
            case (inputs.decoded_instr.rd)
               rd_cap_CCall: begin
                  check_cs1_tagged = True;
                  check_cs2_tagged = True;
                  check_cs1_sealed_with_type = True;
                  check_cs2_sealed_with_type = True;
                  check_cs1_cs2_types_match = True;
                  check_cs1_permit_x = True;
                  check_cs2_no_permit_x = True;
                  check_cs1_permit_ccall = True;
                  check_cs2_permit_ccall = True;
                  alu_outputs.val1_cap_not_int = True;
                  // TODO SHARE_SEAL
                  // TODO maybe this can be moved later? could have a SEAL val1_source
                  alu_outputs.cap_val1 = setKind(cs2_val, UNSEALED);
                  alu_outputs.rd = cCallRD;
                  alu_outputs.pcc = fromCapPipe(maskAddr(setKind(cs1_val, UNSEALED), signExtend(2'b10)));
                  alu_outputs.control = CONTROL_CAPBRANCH;
                  let target = {truncateLSB(getAddr(cs1_val)), 1'b0};
                  //alu_outputs = checkValidJump(alu_outputs, True, cs1_val, cs1_base, zeroExtend(inputs.rs1_idx), target);
                  alu_outputs.check_enable = True;
                  authority = cs1_val;
                  authority_base = cs1_base;
                  authority_top = cs1_top;
                  authorityIdx = {1'b0, inputs.rs1_idx};
                  check_address_low = target;
                  addop1 = {target, 1'b0};
                  addop2 = {     2, 1'b0};
                  check_address_high_from_sum = True;
               end
            default: alu_outputs.control = CONTROL_TRAP;
            endcase // inputs.decoded_instr.rd
         end
         f7_cap_CUnseal: begin
            check_cs1_tagged = True;
            check_cs2_tagged = True;
            check_cs1_sealed_with_type = True;
            check_cs2_unsealed = True;
            check_cs2_points_to_cs1_type = True;
            check_cs2_permit_unseal = True;

            alu_outputs.check_enable = True;
            authority = cs2_val;
            authorityIdx = {0,inputs.rs2_idx};
            authority_base = cs2_base;
            authority_top  = cs2_top;

            // TODO ALU_CHECK_ADDR
            check_address_low = getAddr(cs2_val);
            check_address_high = zeroExtend(getAddr(cs2_val));
            alu_outputs.check_inclusive = False;

            // TODO SHARE_SEAL
            // TODO maybe this can be moved later? could have a SEAL val1_source
            alu_outputs.cap_val1 = setKind(cs1_val, UNSEALED);
            alu_outputs.val1_cap_not_int = True;
         end
         f7_cap_CTestSubset: begin
            let local_cs1_val = cs1_val;
            Bool useDDC = inputs.rs1_idx == 0;
            if (useDDC) begin
               local_cs1_val = inputs.ddc;
            end

            if (  isValidCap(local_cs1_val) == isValidCap(cs2_val)
               && ((getPerms(cs2_val) & getPerms(local_cs1_val)) == getPerms(cs2_val))
               ) begin
               alu_outputs.check_enable = False; // We do not require the check to pass to avoid a trap
               authority = local_cs1_val;
               // don't need an authority ID
               authority_base = useDDC ? ddc_base : cs1_base;
               authority_top  = useDDC ? ddc_top  : cs2_top;
               // TODO ALU_CHECK_ADDR
               check_address_low = cs2_base;
               check_address_high = cs2_top;
               alu_outputs.check_inclusive = True;
               alu_outputs.op_stage2 = OP_Stage2_TestSubset;
            end else begin
               alu_outputs.val1 = zeroExtend(pack(False));
            end
         end
         f7_cap_CCopyType: begin
            check_cs1_tagged = True;
            check_cs1_unsealed = True;
            case (getKind(cs2_val)) matches
               tagged UNSEALED: begin
                  alu_outputs.val1 = otype_unsealed_ext;
               end
               tagged SENTRY: begin
                  alu_outputs.val1 = otype_sentry_ext;
               end
               tagged RES0: begin
                  alu_outputs.val1 = otype_res0_ext;
               end
               tagged RES1: begin
                  alu_outputs.val1 = otype_res1_ext;
               end
               tagged SEALED_WITH_TYPE .otype: begin
                  alu_outputs.val1_source = SET_ADDR;
                  alu_outputs.internal_op2 = zeroExtend(otype);

                  alu_outputs.check_enable = True;
                  authority = cs1_val;
                  authorityIdx = {0,inputs.rs1_idx};
                  authority_base = cs1_base;
                  authority_top  = cs1_top;

                  // TODO ALU_CHECK_ADDR
                  check_address_low = zeroExtend(otype);
                  check_address_high = zeroExtend(otype);
                  alu_outputs.check_inclusive = False;
               end
            endcase // getKind (cs2_val)
         end
         f7_cap_CAndPerm: begin
            check_cs1_tagged = True;
            check_cs1_unsealed = True;

            // TODO SHARE_SET_PERMS
            alu_outputs.cap_val1 = setPerms(cs1_val, pack(getPerms(cs1_val)) & truncate(rs2_val));
            alu_outputs.val1_cap_not_int = True;
         end
         f7_cap_CSetFlags: begin
            check_cs1_unsealed = True;

            // TODO SHARE_SET_FLAGS
            alu_outputs.cap_val1 = setFlags(cs1_val, truncate(rs2_val));
            alu_outputs.val1_cap_not_int = True;
         end
         f7_cap_CToPtr: begin
            Bool useDDC = inputs.rs2_idx == 0;
            if (useDDC) begin
               check_ddc_tagged = True;
            end else begin
               check_cs2_tagged = True;
            end
            check_cs1_unsealed = True;

            if (isValidCap(cs1_val)) begin
               //alu_outputs.val1 = zeroExtend(getAddr(cs1_val) - (inputs.rs2_idx == 0 ? ddc_base : cs2_base));
               // TODO set this below
               addop1 = {getAddr (cs1_val), 1'b1};
               addop2 = {~(useDDC ? ddc_base : cs2_base), 1'b1};
            end else begin
               alu_outputs.val1 = 0;
            end
         end
         f7_cap_CFromPtr: begin
            if (rs2_val == 0) begin
               alu_outputs.val1 = 0;
            end else begin
               if (inputs.rs1_idx == 0) begin
                  check_ddc_tagged = True;
                  check_ddc_unsealed = True;
               end else begin
                  check_cs1_tagged = True;
                  check_cs1_unsealed = True;
               end

               alu_outputs.val1_source = SET_OFFSET;
               alu_outputs.internal_op1 = inputs.rs1_idx == 0 ? inputs.ddc : cs1_val;
               alu_outputs.internal_op2 = rs2_val;
               alu_outputs.internal_offset_inc_not_set = False;
            end
         end
         f7_cap_CSub: begin
            //alu_outputs.val1 = zeroExtend(getAddr(cs1_val) - getAddr(cs2_val));
            addop1 = { (getAddr (cs1_val)), 1'b1};
            addop2 = {~(getAddr (cs2_val)), 1'b1};
         end
         f7_cap_CBuildCap: begin
            Bool useDDC = inputs.rs1_idx == 0;
            if (useDDC) begin
               check_ddc_tagged = True;
               check_ddc_unsealed = True;
               check_cs2_perm_subset_ddc = True;
               authority = inputs.ddc;
               authorityIdx = {1'b1, scr_addr_DDC};
               authority_base = ddc_base;
               authority_top  = ddc_top;
            end else begin
               authority = cs1_val;
               authorityIdx = {1'b0, inputs.rs1_idx};
               authority_base = cs1_base;
               authority_top  = cs1_top;
               check_cs1_tagged = True;
               check_cs1_unsealed = True;
               check_cs2_perm_subset_cs1 = True;
            end

            if (!isDerivable(cs2_val)) begin
               alu_outputs = fv_CHERI_exc(alu_outputs, zeroExtend(inputs.rs2_idx), exc_code_CHERI_Length);
            end

            alu_outputs.check_enable = True;

            // TODO ALU_CHECK_ADDR
            check_address_low = cs2_base;
            check_address_high = cs2_top;
            alu_outputs.check_inclusive = True;

            let result = setValidCap(cs2_val, True);
            alu_outputs.cap_val1 = setKind(result, getKind(cs2_val) == SENTRY ? SENTRY : UNSEALED); // Preserve sentries
            alu_outputs.val1_cap_not_int = True;
         end
         f7_cap_Loads: begin
            Bit#(3) widthCode = zeroExtend(funct5rs2[1:0]);
            Bool is_lr = False;
            Bool is_unsigned = funct5rs2[2] == cap_mem_unsigned && funct5rs2[4] == 1'b0;
            Bool illegal = False;
            if (funct5rs2[4] == 1'b1) begin
               if (funct5rs2[2:0] == 3'b111) begin
                  widthCode = w_SIZE_Q;
               end else begin
`ifdef ISA_A
                  is_lr = True;
                  widthCode = funct5rs2[2:0];
`else
                  illegal = True;
`endif
               end
            end
            if ((widthCode > w_SIZE_MAX) || (is_unsigned && widthCode == w_SIZE_MAX)) begin
               illegal = True;
            end

            if (illegal) begin
               // exc_code defaults to exc_code_ILLEGAL_INSTRUCTION
               alu_outputs.control = CONTROL_TRAP;
            end else begin
               //alu_outputs = memCommon(alu_outputs, False, is_unsigned, funct5rs2[3] == cap_mem_ddc, widthCode, inputs.ddc, cs1_val, inputs.rs1_idx, ?, is_lr, {f5_AMO_LR, 2'b0});
               //let eaddr = getAddr(addr) + (useDDC ? getAddr(ddc) : 0);
               Bool useDDC = funct5rs2[3] == cap_mem_ddc;
               addop1 = {         getAddr (   cs1_val)    , 1'b0};
               addop2 = {useDDC ? getAddr (inputs.ddc) : 0, 1'b0};
               let op_stage2 = False ? OP_Stage2_ST : OP_Stage2_LD;
`ifdef ISA_A
               if (is_amo) op_stage2 = OP_Stage2_AMO;
`endif

               //width code must be checked externally

               alu_outputs.op_stage2      = op_stage2;
               // TODO move this stuff below? need to decide what needs moved
               width_code = widthCode;
               alu_outputs.mem_unsigned   = False ? False : is_unsigned;
               alu_outputs.val1           = zeroExtend({f5_AMO_LR, 2'b0});
               alu_outputs.val2           = zeroExtend(getAddr(data)); //for stores
               alu_outputs.cap_val2       = data;
               alu_outputs.val2_cap_not_int = widthCode == w_SIZE_CAP;

               authority = useDDC ? inputs.ddc : cs1_val;
               authorityIdx = useDDC ? {1,scr_addr_DDC} : {0,inputs.rs1_idx};
               authority_top  = useDDC ? ddc_top  : cs1_top;
               authority_base = useDDC ? ddc_base : cs1_base;
               if (useDDC) begin
                  check_ddc_tagged = True;
                  check_ddc_unsealed = True;
                  check_ddc_permit_load = True;
                  check_ddc_permit_load_cap = widthCode == w_SIZE_CAP;
               end else begin
                  check_cs1_tagged = True;
                  check_cs1_unsealed = True;
                  check_cs1_permit_load = True;
                  check_cs1_permit_load_cap = widthCode == w_SIZE_CAP;
               end

               //// TODO inline this
               ////alu_outputs = checkValidDereference(alu_outputs, authority, authorityIdx, eaddr, widthCode, isStoreNotLoad, !isStoreNotLoad, data);
               alu_outputs.check_enable = True;
               alu_outputs.check_inclusive = True;
               if (widthCode == w_SIZE_CAP && getHardPerms(authority).permitLoadCap) begin
                   alu_outputs.mem_allow_cap = True;
               end
            end
         end
         f7_cap_Stores: begin
            let widthCode = funct5rd[2:0];
            Bool is_sc = funct5rd[4] == 1'b1;
            Bool illegal = False;
            if (is_sc) begin
`ifdef ISA_A
               alu_outputs.rd = inputs.rs2_idx;
`else
               illegal = True;
`endif
            end
            if (widthCode > w_SIZE_MAX) illegal = True;
            if (illegal) begin
               // exc_code defaults to exc_code_ILLEGAL_INSTRUCTION
               alu_outputs.control = CONTROL_TRAP;
            end else begin
               //alu_outputs = memCommon(alu_outputs, True, ?, funct5rd[3] == cap_mem_ddc, widthCode, inputs.ddc, cs1_val, inputs.rs1_idx, cs2_val, is_sc, {f5_AMO_SC, 2'b0});
               //let eaddr = getAddr(addr) + (useDDC ? getAddr(ddc) : 0);
               Bool useDDC = funct5rd[3] == cap_mem_ddc;
               addop1 = {         getAddr (cs1_val), 1'b0};
               addop2 = {useDDC ? getAddr (inputs.ddc) : 0, 1'b0};
               let op_stage2 = True ? OP_Stage2_ST : OP_Stage2_LD;
`ifdef ISA_A
               if (is_amo) op_stage2 = OP_Stage2_AMO;
`endif

               //width code must be checked externally

               alu_outputs.op_stage2      = op_stage2;
               // TODO move this stuff later
               width_code = widthCode;
               alu_outputs.mem_unsigned   = True ? False : ?;
               alu_outputs.val1           = zeroExtend({f5_AMO_SC, 2'b0});
               alu_outputs.val2           = zeroExtend(getAddr(data)); //for stores
               alu_outputs.cap_val2       = data;
               alu_outputs.val2_cap_not_int = widthCode == w_SIZE_CAP;

               authority = useDDC ? inputs.ddc : cs1_val;
               authorityIdx = useDDC ? {1, scr_addr_DDC} : {0, inputs.rs1_idx};
               authority_base = useDDC ? ddc_base : cs1_base;
               authority_top  = useDDC ? ddc_top  : cs1_top;
               if (useDDC) begin
                  check_ddc_tagged = True;
                  check_ddc_unsealed = True;
                  check_ddc_permit_store = True;
                  check_ddc_permit_store_cap = widthCode == w_SIZE_CAP;
               end else begin
                  check_cs1_tagged = True;
                  check_cs1_unsealed = True;
                  check_cs1_permit_store = True;
                  check_cs1_permit_store_cap = widthCode == w_SIZE_CAP;
               end

               // 
               //alu_outputs = checkValidDereference(alu_outputs, authority, authorityIdx, eaddr, widthCode, isStoreNotLoad, !isStoreNotLoad, data);
               alu_outputs.check_enable = True;
               alu_outputs.check_inclusive = True;
            end
         end
         f7_cap_TwoOp: begin
            case (funct5rs2)
            f5rs2_cap_CGetLen: begin
               Bit#(XLEN) length = truncate(getLength(cs1_val));
               alu_outputs.val1 = zeroExtend(length);
            end
            f5rs2_cap_CGetBase: begin
               alu_outputs.val1 = zeroExtend(cs1_base);
            end
            f5rs2_cap_CGetTag: begin
               alu_outputs.val1 = zeroExtend(pack(isValidCap(cs1_val)));
            end
            f5rs2_cap_CGetSealed: begin
               alu_outputs.val1 = zeroExtend(pack(getKind(cs1_val) != UNSEALED));
            end
            f5rs2_cap_CRRL: begin
               alu_outputs.val1_source = GET_PRECISION;
               alu_outputs.internal_crrl_not_cram = True;
            end
            f5rs2_cap_CRAM: begin
               alu_outputs.val1_source = GET_PRECISION;
               alu_outputs.internal_crrl_not_cram = False;
            end
            f5rs2_cap_CMove: begin
               alu_outputs.cap_val1 = cs1_val;
               alu_outputs.val1_cap_not_int = True;
            end
            f5rs2_cap_CClearTag: begin
               alu_outputs.cap_val1 = setValidCap(cs1_val, False);
               alu_outputs.val1_cap_not_int = True;
            end
            f5rs2_cap_CGetAddr: begin
               alu_outputs.val1 = zeroExtend(getAddr(cs1_val));
            end
            f5rs2_cap_CSealEntry: begin
               check_cs1_tagged = True;
               check_cs1_unsealed = True;
               check_cs1_permit_x = True;
               // TODO SHARE_SEAL
               alu_outputs.cap_val1 = setKind(cs1_val, SENTRY);
               alu_outputs.val1_cap_not_int = True;
            end
            f5rs2_cap_CGetOffset: begin
               alu_outputs.val1 = zeroExtend(cs1_offset);
            end
            f5rs2_cap_CGetFlags: begin
               alu_outputs.val1 = zeroExtend(getFlags(cs1_val));
            end
            f5rs2_cap_CGetPerm: begin
               alu_outputs.val1 = zeroExtend(getPerms(cs1_val));
            end
            f5rs2_cap_CJALR: begin
               check_cs1_tagged = True;
               check_cs1_unsealed_or_sentry = True;
               check_cs1_permit_x = True;

               Addr  next_pc   = cs1_offset;
               Addr  ret_pc    = fallthru_pc;

               let maskedTarget = maskAddr(cs1_val, signExtend(2'b10));

               let pcc_addr = getAddr(toCapPipe(inputs.pcc));
               //let target_addr = getPCCBase(inputs.pcc) + next_pc;
               addop1 = { pcc_base, 1'b0};
               addop2 = {  next_pc, 1'b0};
               // TODO move this stuff later
               let cf_info   = CF_Info {cf_op       : CF_JALR,
                                        from_PC     : pcc_addr,
                                        taken       : True,
                                        fallthru_PC : fallthru_pcc_addr,
                                        taken_PC    : getAddr(maskedTarget) };

               next_pc[0] = 1'b0;

               alu_outputs.control   = CONTROL_CAPBRANCH;
               alu_outputs.cf_info   = cf_info;

               alu_outputs.addr      = next_pc;
               alu_outputs.pcc       = fromCapPipe(setKind(maskedTarget, UNSEALED));
               alu_outputs.val1_source = SET_OFFSET;
               alu_outputs.internal_op1 = toCapPipe(inputs.pcc);
               alu_outputs.internal_op2 = fall_through_pc_inc(inputs);
               alu_outputs.internal_offset_inc_not_set = True;
               alu_outputs.internal_seal_entry = True;

               // TODO inline this
               //alu_outputs = checkValidJump(alu_outputs, True, cs1_val, cs1_base, {0,inputs.rs1_idx}, getAddr(maskedTarget));
               WordXL target = getAddr (maskedTarget);
`ifdef ISA_C
               Bool misaligned_target = cs1_base[0] != 1'b0;
`else
               Bool misaligned_target = (target [1] == 1'b1) || (cs1_base[1:0] != 2'b0);
`endif
               if (misaligned_target && True) begin
                   alu_outputs.control = CONTROL_TRAP;
                   alu_outputs.exc_code = exc_code_INSTR_ADDR_MISALIGNED;
               end
               alu_outputs.check_enable = True;
               authority = cs1_val;
               authorityIdx = {0, inputs.rs1_idx};
               authority_base = cs1_base;
               authority_top  = cs1_top;
               check_address_low = target;
               //alu_outputs.check_address_high = zeroExtend(target) + 2;
               addop1 = {zeroExtend (target), 1'b0};
               addop2 = {                  2, 1'b0};
               check_address_high_from_sum = True;
               alu_outputs.check_inclusive = True;

            end
            f5rs2_cap_CGetType: begin
               case (getKind(cs1_val)) matches
                  tagged UNSEALED: begin
                     alu_outputs.val1 = otype_unsealed_ext;
                  end
                  tagged SENTRY: begin
                     alu_outputs.val1 = otype_sentry_ext;
                  end
                  tagged RES0: begin
                     alu_outputs.val1 = otype_res0_ext;
                  end
                  tagged RES1: begin
                     alu_outputs.val1 = otype_res1_ext;
                  end
                  tagged SEALED_WITH_TYPE .otype: begin
                     alu_outputs.val1 = zeroExtend(otype);
                  end
               endcase // getKind (cs1_val)
            end
            default: alu_outputs.control = CONTROL_TRAP;
         endcase // funct5rs2
         end
      default: alu_outputs.control = CONTROL_TRAP;
      endcase // funct7
      end
      default: alu_outputs.control = CONTROL_TRAP;
      endcase // funct3
   end
`endif // ISA_CHERI

   case(alu_outputs.val1_source)
   SET_BOUNDS: begin
      // TODO this is wrong - the adder only does 32 bits, not 33
      //check_address_low = getAddr (cs1_val);
      addop1 = {pack (zeroExtend (getAddr (cs1_val))), 1'b0};
      addop2 = {pack (zeroExtend (alu_outputs.internal_op2)), 1'b0};
      check_address_high_from_sum = True;
   end
   GET_PRECISION: begin
      CapReg nullCapReg = nullCap;
      let result = getRepresentableAlignmentMask(nullCapReg, inputs.rs1_val);
      if (alu_outputs.internal_crrl_not_cram) begin
         //result = (inputs.rs1_val + ~result) & result;
         addop1 = {pack (inputs.rs1_val), 1'b0};
         addop2 = {pack (       ~result), 1'b0};
      end
   end
   endcase


   Bit #(TAdd #(XLEN, 2)) sum_tmp = zeroExtend (addop1) + zeroExtend (addop2);
   IntXL sum = unpack (sum_tmp [valueof (XLEN):1]);
   //Bit #(TAdd #(XLEN, 1)) longsum = zeroExtend (getAddr (cs1_val)) + zeroExtend (alu_outputs.internal_op2);
   Bit #(TAdd #(XLEN, 2)) longsum_tmp = zeroExtend (addop1) + zeroExtend (addop2);
   Bit #(TAdd #(XLEN, 1)) longsum = longsum_tmp[valueof(XLEN):1];

   Bool misaligned_target = (pack (sum))[1] == 1'b1;

`ifdef ISA_C
   misaligned_target = False;
`endif
   //match {.sum, .misaligned_target} <- adder_wrapper.func (addop1, addop2);

   Int #(TAdd #(1, XLEN)) shiftop_final = unpack (shiftop);
   let shift_res_full = shiftop_final >> shamt;
   Bit #(XLEN) shift_res = shift_left ? reverseBits (truncate (pack (shift_res_full)))
                                      : truncate (pack (shift_res_full));
   Bit #(32) shift_res_b32 = truncate (shift_res);

   Int #(TAdd #(1, XLEN)) s_cmpop1 = unpack (cmpop1);
   Int #(TAdd #(1, XLEN)) s_cmpop2 = unpack (cmpop2);
   Bool cmp_greater_than    = s_cmpop1 > s_cmpop2;
   Bool cmp_equal           = cmpop1 == cmpop2;
   Bool cmp_greater_than_eq = cmp_greater_than || cmp_equal;
   Bool cmp_less_than_eq    = !cmp_greater_than;
   Bool cmp_less_than       = !cmp_greater_than && !cmp_equal;

`ifdef ISA_CHERI






    case(alu_outputs.val1_source)
    SET_OFFSET: begin
        let result = modifyOffset(alu_outputs.internal_op1, alu_outputs.internal_op2, alu_outputs.internal_offset_inc_not_set);
        if (alu_outputs.internal_seal_entry) begin
            result.value = setKind(result.value, SENTRY);
        end
        alu_outputs.cap_val1 = result.value;
        alu_outputs.val1_cap_not_int = True;
    end
    SET_BOUNDS: begin
        let result = setBounds(cs1_val, alu_outputs.internal_op2);
        alu_outputs.cap_val1 = result.value;
        alu_outputs.val1_cap_not_int = True;

        alu_outputs.check_enable = True;
        authority = cs1_val;
        authority_base = cs1_base;
        authority_top  = cs1_top;
        alu_outputs.check_inclusive = True;
        check_address_low = getAddr (cs1_val);
        // this is dealt with before
        //alu_outputs.check_address_high = zeroExtend(getAddr(cs1_val)) + zeroExtend(alu_outputs.internal_op2);
        alu_outputs.check_exact_enable = alu_outputs.internal_bounds_exact;
        alu_outputs.check_exact_success = result.exact;
    end
    GET_PRECISION: begin
        CapReg nullCapReg = nullCap;
        let result = getRepresentableAlignmentMask(nullCapReg, inputs.rs1_val);
        if (alu_outputs.internal_crrl_not_cram) begin
            //result = (inputs.rs1_val + ~result) & result;
            result = pack (sum);
        end
        alu_outputs.val1 = result;
    end
    SET_ADDR: begin
        let result = setAddr(cs1_val, alu_outputs.internal_op2);
        alu_outputs.cap_val1 = result.value;
        alu_outputs.val1_cap_not_int = True;
    end
    endcase




   //alu_outputs.check_authority = toCapPipe (inputs.pcc);
   alu_outputs.check_authority = authority;
   // TODO this is not necessarily true; different for SCR accesses
   //alu_outputs.check_authority_idx = {1, scr_addr_PCC};
   alu_outputs.check_authority_idx = authorityIdx;
   // TODO might be able to remove this?
   alu_outputs.check_address_low = check_address_low;
   //alu_outputs.check_address_high = check_address_high_from_sum ? zeroExtend (longsum) : check_address_high;
   alu_outputs.check_address_high = check_address_high_from_sum ? pack (sum_tmp[(xlen+1):1]) : check_address_high;
   alu_outputs.mem_width_code = width_code;

   alu_outputs.authority_base = authority_base;
   alu_outputs.authority_top = authority_top;

   //ALU_Outputs alu_outputs_dereference = checkValidDereference (alu_outputs, authority, authorityIdx, pack (sum), width_code, is_load, is_store, data);

   if (width_code == w_SIZE_CAP && is_load && getHardPerms(authority).permitLoadCap) begin
      alu_outputs.mem_allow_cap = True;
   end

   //if (!isValidCap (authority)) begin
   //   alu_outputs_dereference = fv_CHERI_exc (alu_outputs_dereference, authorityIdx, exc_code_CHERI_Tag);
   //end else if (getKind (authority) != UNSEALED) begin
   //   alu_outputs_dereference = fv_CHERI_exc (alu_outputs_dereference, authorityIdx, exc_code_CHERI_Seal);
   //end else if (is_load && !getHardPerms(authority).permitLoad) begin
   //   alu_outputs_dereference = fv_CHERI_exc (alu_outputs_dereference, authorityIdx, exc_code_CHERI_RPerm);
   //end else if (is_store && !getHardPerms(authority).permitStore) begin
   //   alu_outputs_dereference = fv_CHERI_exc (alu_outputs_dereference, authorityIdx, exc_code_CHERI_WPerm);
   //end else if (is_store && width_code == w_SIZE_CAP && isValidCap (data) && !getHardPerms(authority).permitStoreCap) begin
   //   alu_outputs_dereference = fv_CHERI_exc (alu_outputs_dereference, authorityIdx, exc_code_CHERI_SCPerm);
   //end else if (is_store && width_code == w_SIZE_CAP && isValidCap (data) && !getHardPerms(data).global && !getHardPerms(authority).permitStoreLocalCap) begin
   //   alu_outputs_dereference = fv_CHERI_exc (alu_outputs_dereference, authorityIdx, exc_code_CHERI_SCLocalPerm);
   //end

    // tag checks
    if      (check_cs1_tagged             && !isValidCap(cs1_val))
        alu_outputs = fv_CHERI_exc(alu_outputs, zeroExtend(inputs.rs1_idx), exc_code_CHERI_Tag);
    else if (check_cs2_tagged             && !isValidCap(cs2_val))
        alu_outputs = fv_CHERI_exc(alu_outputs, zeroExtend(inputs.rs2_idx), exc_code_CHERI_Tag);
    else if (check_ddc_tagged             && !isValidCap(inputs.ddc))
        alu_outputs = fv_CHERI_exc(alu_outputs, {1'b1, scr_addr_DDC}      , exc_code_CHERI_Tag);
    // seal checks
    else if (check_cs1_sealed_with_type   && (getKind(cs1_val) matches tagged SEALED_WITH_TYPE ._ ? False : True))
        alu_outputs = fv_CHERI_exc(alu_outputs, zeroExtend(inputs.rs1_idx), exc_code_CHERI_Seal);
    else if (check_cs2_sealed_with_type   && (getKind(cs2_val) matches tagged SEALED_WITH_TYPE ._ ? False : True))
        alu_outputs = fv_CHERI_exc(alu_outputs, zeroExtend(inputs.rs2_idx), exc_code_CHERI_Seal);
    // unsealed checks
    else if (check_cs1_unsealed           && isValidCap(cs1_val) && getKind(cs1_val) != UNSEALED)
        alu_outputs = fv_CHERI_exc(alu_outputs, zeroExtend(inputs.rs1_idx), exc_code_CHERI_Seal);
    else if (check_cs1_unsealed_or_sentry && isValidCap(cs1_val) && getKind(cs1_val) != UNSEALED && getKind(cs1_val) != SENTRY)
        alu_outputs = fv_CHERI_exc(alu_outputs, zeroExtend(inputs.rs1_idx), exc_code_CHERI_Seal);
    else if (check_cs2_unsealed           && isValidCap(cs2_val) && getKind(cs2_val) != UNSEALED)
        alu_outputs = fv_CHERI_exc(alu_outputs, zeroExtend(inputs.rs2_idx), exc_code_CHERI_Seal);
    else if (check_ddc_unsealed           && isValidCap(inputs.ddc) && getKind(inputs.ddc) != UNSEALED)
        alu_outputs = fv_CHERI_exc(alu_outputs, {1'b1, scr_addr_DDC}      , exc_code_CHERI_Seal);
    // matching types
    else if (check_cs1_cs2_types_match    && getKind(cs1_val).SEALED_WITH_TYPE != getKind(cs2_val).SEALED_WITH_TYPE) // Already checked SEALED_WITH_TYPE
        alu_outputs = fv_CHERI_exc(alu_outputs, zeroExtend(inputs.rs1_idx), exc_code_CHERI_Type);
    // permit ccall
    else if (check_cs1_permit_ccall       && !getHardPerms(cs1_val).permitCCall)
        alu_outputs = fv_CHERI_exc(alu_outputs, zeroExtend(inputs.rs1_idx), exc_code_CHERI_CCallPerm);
    else if (check_cs2_permit_ccall       && !getHardPerms(cs2_val).permitCCall)
        alu_outputs = fv_CHERI_exc(alu_outputs, zeroExtend(inputs.rs2_idx), exc_code_CHERI_CCallPerm);
    // permit execute
    else if (check_cs1_permit_x           && !getHardPerms(cs1_val).permitExecute)
        alu_outputs = fv_CHERI_exc(alu_outputs, zeroExtend(inputs.rs1_idx), exc_code_CHERI_XPerm);
    // no permite execute
    else if (check_cs2_no_permit_x        && getHardPerms(cs2_val).permitExecute)
        alu_outputs = fv_CHERI_exc(alu_outputs, zeroExtend(inputs.rs2_idx), exc_code_CHERI_XPerm);
    // permit unseal
    else if (check_cs2_permit_unseal      && !getHardPerms(cs2_val).permitUnseal)
        alu_outputs = fv_CHERI_exc(alu_outputs, zeroExtend(inputs.rs2_idx), exc_code_CHERI_UnsealPerm);
    // permit seal
    else if (check_cs2_permit_seal        && !getHardPerms(cs2_val).permitSeal)
        alu_outputs = fv_CHERI_exc(alu_outputs, zeroExtend(inputs.rs2_idx), exc_code_CHERI_SealPerm);
    // points to cs1 type (???)
    else if (check_cs2_points_to_cs1_type && getAddr(cs2_val) != zeroExtend(getKind(cs1_val).SEALED_WITH_TYPE)) // Already checked SEALED_WITH_TYPE
        alu_outputs = fv_CHERI_exc(alu_outputs, zeroExtend(inputs.rs2_idx), exc_code_CHERI_Type);
    // valid type
    else if (check_cs2_addr_valid_type    && !validAsType(cs2_val, truncate(getAddr(cs2_val))))
        alu_outputs = fv_CHERI_exc(alu_outputs, zeroExtend(inputs.rs2_idx), exc_code_CHERI_Length);
    // perm subset checks
    else if (check_cs2_perm_subset_cs1    && (getPerms(cs1_val) & getPerms(cs2_val)) != getPerms(cs2_val))
        alu_outputs = fv_CHERI_exc(alu_outputs, zeroExtend(inputs.rs2_idx), exc_code_CHERI_Software);
    else if (check_cs2_perm_subset_ddc    && (getPerms(inputs.ddc) & getPerms(cs2_val)) != getPerms(cs2_val))
        alu_outputs = fv_CHERI_exc(alu_outputs, zeroExtend(inputs.rs2_idx), exc_code_CHERI_Software);
    // TODO check ordering on these
    // permit loads
    else if (check_cs1_permit_load && !getHardPerms(cs1_val).permitLoad)
        alu_outputs = fv_CHERI_exc(alu_outputs, {0, inputs.rs1_idx}, exc_code_CHERI_RPerm);
    else if (check_cs2_permit_load && !getHardPerms(cs2_val).permitLoad)
        alu_outputs = fv_CHERI_exc(alu_outputs, {0, inputs.rs2_idx}, exc_code_CHERI_RPerm);
    else if (check_ddc_permit_load && !getHardPerms(inputs.ddc).permitLoad)
        alu_outputs = fv_CHERI_exc(alu_outputs, {1,scr_addr_DDC}, exc_code_CHERI_RPerm);
    // permit load cap
    else if (check_cs1_permit_load_cap && getHardPerms(cs1_val).permitLoadCap)
        alu_outputs.mem_allow_cap = True;
    else if (check_cs2_permit_load_cap && getHardPerms(cs2_val).permitLoadCap)
        alu_outputs.mem_allow_cap = True;
    else if (check_ddc_permit_load_cap && getHardPerms(inputs.ddc).permitLoadCap)
        alu_outputs.mem_allow_cap = True;
    // permit stores
    else if (check_cs1_permit_store && !getHardPerms(cs1_val).permitStore)
        alu_outputs = fv_CHERI_exc(alu_outputs, {0, inputs.rs1_idx}, exc_code_CHERI_WPerm);
    else if (check_cs2_permit_store && !getHardPerms(cs2_val).permitStore)
        alu_outputs = fv_CHERI_exc(alu_outputs, {0, inputs.rs2_idx}, exc_code_CHERI_WPerm);
    else if (check_ddc_permit_store && !getHardPerms(inputs.ddc).permitStore)
        alu_outputs = fv_CHERI_exc(alu_outputs, {1,scr_addr_DDC}, exc_code_CHERI_WPerm);
    // permit global cap stores
    else if (check_cs1_permit_store && isValidCap(data) && !getHardPerms(cs1_val).permitStoreCap)
        alu_outputs = fv_CHERI_exc(alu_outputs, {0, inputs.rs1_idx}, exc_code_CHERI_SCPerm);
    else if (check_cs2_permit_store && isValidCap(data) && !getHardPerms(cs2_val).permitStoreCap)
        alu_outputs = fv_CHERI_exc(alu_outputs, {0, inputs.rs1_idx}, exc_code_CHERI_SCPerm);
    else if (check_ddc_permit_store && isValidCap(data) && !getHardPerms(inputs.ddc).permitStoreCap)
        alu_outputs = fv_CHERI_exc(alu_outputs, {0, inputs.rs1_idx}, exc_code_CHERI_SCPerm);
    // permit local cap stores
    else if (check_cs1_permit_store && isValidCap(data) && !getHardPerms(cs1_val).global && !getHardPerms(cs1_val).permitStoreLocalCap)
        alu_outputs = fv_CHERI_exc(alu_outputs, {0, inputs.rs1_idx}, exc_code_CHERI_SCLocalPerm);
    else if (check_cs2_permit_store && isValidCap(data) && !getHardPerms(cs2_val).global && !getHardPerms(cs2_val).permitStoreLocalCap)
        alu_outputs = fv_CHERI_exc(alu_outputs, {0, inputs.rs1_idx}, exc_code_CHERI_SCLocalPerm);
    else if (check_ddc_permit_store && isValidCap(data) && !getHardPerms(inputs.ddc).global && !getHardPerms(inputs.ddc).permitStoreLocalCap)
        alu_outputs = fv_CHERI_exc(alu_outputs, {0, inputs.rs1_idx}, exc_code_CHERI_SCLocalPerm);
`endif


   if (inputs.decoded_instr.opcode == op_BRANCH) begin
      Addr branch_target = pack (sum);
      Bool branch_taken  = False;

      if      (funct3 == f3_BEQ )  branch_taken = cmp_equal;
      else if (funct3 == f3_BNE )  branch_taken = !cmp_equal;
      else if (funct3 == f3_BLT )  branch_taken = cmp_less_than;
      else if (funct3 == f3_BGE )  branch_taken = cmp_greater_than_eq;
      else if (funct3 == f3_BLTU)  branch_taken = cmp_less_than;
      else if (funct3 == f3_BGEU)  branch_taken = cmp_greater_than_eq;

      Exc_Code exc_code = exc_code_ILLEGAL_INSTRUCTION;
      if (!trap && branch_taken && misaligned_target) begin
         exc_code = exc_code_INSTR_ADDR_MISALIGNED;
         trap = True;
      end

`ifdef ISA_CHERI
      cf_info = CF_Info {cf_op       : CF_BR,
                         from_PC     : pcc_addr,
                         taken       : branch_taken,
                         fallthru_PC : fallthru_pcc_addr,
                         taken_PC    : branch_target };
`else
      cf_info = CF_Info {cf_op       : CF_BR,
                         from_PC     : inputs.pc,
                         taken       : branch_taken,
                         fallthru_PC : fallthru_pc,
                         taken_PC    : branch_target };
`endif
      let next_pc = branch_taken ? branch_target : fallthru_pc;
      alu_outputs.control = trap ? CONTROL_TRAP : (branch_taken ? CONTROL_BRANCH : CONTROL_STRAIGHT);
      alu_outputs.exc_code = exc_code;
      alu_outputs.op_stage2 = OP_Stage2_ALU;
      alu_outputs.rd = 0;
`ifdef RVFI
      alu_outputs.val1 = 0;
`endif
      alu_outputs.addr = next_pc;
      alu_outputs.val2 = extend (branch_target);

`ifdef ISA_CHERI
      //alu_outputs = checkValidJump (alu_outputs, branch_taken, toCapPipe (inputs.pcc), getPCCBase (inputs.pcc), {1, scr_addr_PCC}, getPCCBase (inputs.pcc) + next_pc);
      alu_outputs.check_enable = branch_taken;
`endif
      alu_outputs.cf_info = cf_info;
`ifdef INCLUDE_TANDEM_VERIF
      alu_outputs.trace_data = mkTrace_OTHER (next_pc,
                                              fv_trace_isize (inputs),
                                              fv_trace_instr (inputs));
`endif
   end


   else if (inputs.decoded_instr.opcode == op_JAL) begin
      //alu_outputs = fv_JAL (inputs);
      Addr jump_target = pack (sum);

`ifdef ISA_CHERI
      cf_info = CF_Info {cf_op       : CF_JAL,
                         from_PC     : pcc_addr,
                         taken       : True,
                         fallthru_PC : fallthru_pcc_addr,
                         taken_PC    : jump_target};
`else
      cf_info = CF_Info {cf_op       : CF_JAL,
                         from_PC     : inputs.pc,
                         taken       : True,
                         fallthru_PC : fallthru_pc,
                         taken_PC    : jump_target};
`endif
      alu_outputs.control = misaligned_target ? CONTROL_TRAP : CONTROL_BRANCH;
      alu_outputs.exc_code = exc_code_INSTR_ADDR_MISALIGNED;
      alu_outputs.op_stage2 = OP_Stage2_ALU;
      alu_outputs.rd = inputs.decoded_instr.rd;
      alu_outputs.addr = jump_target;
      alu_outputs.val1 = extend (fallthru_pc);
      alu_outputs.cf_info = cf_info;

`ifdef ISA_CHERI
      //alu_outputs = checkValidJump (alu_outputs, branch_taken, toCapPipe (inputs.pcc), getPCCBase (inputs.pcc), {1, scr_addr_PCC}, getPCCBase (inputs.pcc) + next_pc);
      alu_outputs.check_enable = True;
`endif
`ifdef INCLUDE_TANDEM_VERIF
      alu_outputs.trace_data = mkTrace_I_RD (next_pc,
                                             fv_trace_isize (inputs),
                                             fv_trace_instr (inputs),
                                             inputs.decoded_instr.rd,
                                             fallthru_pc);
`endif
   end

   else if (inputs.decoded_instr.opcode == op_JALR) begin
      //alu_outputs = fv_JALR (inputs);
      Addr jump_target = pack (sum);
      jump_target[0] = 1'b0;

`ifdef ISA_CHERI
      cf_info = CF_Info {cf_op       : CF_JALR,
                         from_PC     : pcc_addr,
                         taken       : True,
                         fallthru_PC : fallthru_pcc_addr,
                         taken_PC    : jump_target};
`else
      cf_info = CF_Info {cf_op       : CF_JALR,
                         from_PC     : inputs.pc,
                         taken       : True,
                         fallthru_PC : fallthru_pc,
                         taken_PC    : jump_target};
`endif
      alu_outputs.control = misaligned_target ? CONTROL_TRAP : CONTROL_BRANCH;
      alu_outputs.exc_code = exc_code_INSTR_ADDR_MISALIGNED;
      alu_outputs.op_stage2 = OP_Stage2_ALU;
      alu_outputs.rd = inputs.decoded_instr.rd;
      alu_outputs.addr = jump_target;
      alu_outputs.val1 = extend (fallthru_pc);
      alu_outputs.cf_info = cf_info;

`ifdef ISA_CHERI
      //alu_outputs = checkValidJump (alu_outputs, branch_taken, toCapPipe (inputs.pcc), getPCCBase (inputs.pcc), {1, scr_addr_PCC}, getPCCBase (inputs.pcc) + next_pc);
      alu_outputs.check_enable = True;
`endif
`ifdef INCLUDE_TANDEM_VERIF
      alu_outputs.trace_data = mkTrace_I_RD (next_pc,
                                             fv_trace_isize (inputs),
                                             fv_trace_instr (inputs),
                                             inputs.decoded_instr.rd,
                                             fallthru_pc);
`endif

   end

`ifdef ISA_M
   // OP 'M' ops MUL/ MULH/ MULHSU/ MULHU/ DIV/ DIVU/ REM/ REMU
   else if (   (inputs.decoded_instr.opcode == op_OP)
	    && f7_is_OP_MUL_DIV_REM (inputs.decoded_instr.funct7))
      begin
	 // Will be executed in MBox in next stage
	 alu_outputs.op_stage2 = OP_Stage2_M;
	 alu_outputs.rd        = inputs.decoded_instr.rd;
	 alu_outputs.val1      = inputs.rs1_val;
	 alu_outputs.val2      = inputs.rs2_val;
         //alu_outputs.val1_fast = alu_outputs.val1;
         //alu_outputs.val2_fast = alu_outputs.val2;

`ifdef INCLUDE_TANDEM_VERIF
	 // Normal trace output (if no trap)
	 alu_outputs.trace_data = mkTrace_I_RD (fall_through_pc (inputs),
						fv_trace_isize (inputs),
						fv_trace_instr (inputs),
						inputs.decoded_instr.rd,
						?);
`endif
      end

`ifdef RV64
   // OP 'M' ops MULW/ DIVW/ DIVUW/ REMW/ REMUW
   else if (   (inputs.decoded_instr.opcode == op_OP_32)
	    && f7_is_OP_MUL_DIV_REM (inputs.decoded_instr.funct7))
      begin
	 // Will be executed in MBox in next stage
	 alu_outputs.op_stage2 = OP_Stage2_M;
	 alu_outputs.rd        = inputs.decoded_instr.rd;
	 alu_outputs.val1      = inputs.rs1_val;
	 alu_outputs.val2      = inputs.rs2_val;
         //alu_outputs.val1_fast = alu_outputs.val1;
         //alu_outputs.val2_fast = alu_outputs.val2;

`ifdef INCLUDE_TANDEM_VERIF
	 // Normal trace output (if no trap)
	 alu_outputs.trace_data = mkTrace_I_RD (fall_through_pc (inputs),
						fv_trace_isize (inputs),
						fv_trace_instr (inputs),
						inputs.decoded_instr.rd,
						?);
`endif
      end
`endif
`endif

   // OP_IMM and OP (shifts)
   else if (   (   (inputs.decoded_instr.opcode == op_OP_IMM)
		|| (inputs.decoded_instr.opcode == op_OP))
	    && (   (inputs.decoded_instr.funct3 == f3_SLLI)
		|| (inputs.decoded_instr.funct3 == f3_SRLI)
		|| (inputs.decoded_instr.funct3 == f3_SRAI))) begin
      //alu_outputs = fv_OP_and_OP_IMM_shifts (inputs);
      let rd_val = shift_res;

      alu_outputs.control = trap ? CONTROL_TRAP : CONTROL_STRAIGHT;
      alu_outputs.rd = inputs.decoded_instr.rd;

`ifndef SHIFT_SERIAL
      alu_outputs.op_stage2 = OP_Stage2_ALU;
      alu_outputs.val1 = rd_val;
`else
      alu_outputs.op_stage2 = OP_Stage2_SH;
      alu_outputs.val1 = rs1_val;
      WordXL = extend (shamt);
      val2 = (val2 | {0, instr_b30, 7'b0});
      alu_outputs.val2 = val2;
`endif

`ifdef INCLUDE_TANDEM_VERIF
	 alu_outputs.trace_data = mkTrace_I_RD (fall_through_pc (inputs),
						fv_trace_isize (inputs),
						fv_trace_instr (inputs),
						inputs.decoded_instr.rd,
						rd_val);
`endif
   end

   // Remaining OP_IMM and OP (excluding shifts and 'M' ops MUL/DIV/REM)
   else if (   (inputs.decoded_instr.opcode == op_OP_IMM)
	    || (inputs.decoded_instr.opcode == op_OP)) begin
      //alu_outputs = fv_OP_and_OP_IMM (inputs);
      let rd_val = ?;
      IntXL s_rs2_val_local = s_rs2_val;
      WordXL rs2_val_local  = rs2_val;
      if (inputs.decoded_instr.opcode == op_OP_IMM) begin
         s_rs2_val_local = extend (unpack (inputs.decoded_instr.imm12_I));
         rs2_val_local   = pack (s_rs2_val_local);
      end

      if      ((funct3 == f3_ADDI) && (!subtract))  rd_val = pack (sum);
      else if ((funct3 == f3_ADDI) && ( subtract))  rd_val = pack (sum);
      else if ( funct3 == f3_SLTI)                  rd_val = (cmp_less_than ? 1 : 0);
      else if ( funct3 == f3_SLTIU)                  rd_val = (cmp_less_than ? 1 : 0);
      else if ( funct3 == f3_XORI)                  rd_val = pack (s_rs1_val ^ s_rs2_val_local);
      else if ( funct3 == f3_ORI )                  rd_val = pack (s_rs1_val | s_rs2_val_local);
      else if ( funct3 == f3_ANDI)                  rd_val = pack (s_rs1_val & s_rs2_val_local);

      alu_outputs.control   = trap ? CONTROL_TRAP : CONTROL_STRAIGHT;
      alu_outputs.op_stage2 = OP_Stage2_ALU;
      alu_outputs.rd        = inputs.decoded_instr.rd;
      alu_outputs.val1      = rd_val;

`ifdef INCLUDE_TANDEM_VERIF
      alu_outputs.trace_data = mkTrace_I_RD (fall_through_pc (inputs),
                                             fv_trace_isize (inputs),
                                             fv_trace_instr (inputs),
                                             inputs.decoded_instr.rd,
                                             rd_val);
`endif
   end

`ifdef RV64
   else if (inputs.decoded_instr.opcode == op_OP_IMM_32) begin
      //alu_outputs = fv_OP_IMM_32 (inputs);
      WordXL rd_val = ?;

      if (funct3 == f3_ADDIW) begin
         WordXL tmp = pack (sum);
         rd_val = signExtend (tmp [31:0]);
      end
      else if ((funct3 == f3_SLLIW || funct3 == f3_SRxIW) && shamt5_is_0) begin
         rd_val = signExtend (shift_res_b32);
      end

      alu_outputs.control   = trap ? CONTROL_TRAP : CONTROL_STRAIGHT;
      alu_outputs.op_stage2 = OP_Stage2_ALU;
      alu_outputs.rd        = inputs.decoded_instr.rd;
      alu_outputs.val1      = rd_val;

`ifdef INCLUDE_TANDEM_VERIF
      alu_outputs.trace_data = mkTrace_I_RD (fall_through_pc (inputs),
                                             fv_trace_isize (inputs),
                                             fv_trace_instr (inputs),
                                             inputs.decoded_instr.rd,
                                             rd_val);
`endif
   end

   // Remaining op_OP_32 (excluding 'M' ops)
   else if (inputs.decoded_instr.opcode == op_OP_32) begin
      //alu_outputs = fv_OP_32 (inputs);
      WordXL rd_val = ?;
      Int #(32) sum_b32 = unpack (pack (sum)[31:0]);

      if (funct10 == f10_ADDW) begin
         rd_val = pack (signExtend (sum_b32));
      end
      else if (funct10 == f10_SUBW) begin
         rd_val = pack (signExtend (sum_b32));
      end
      else if (funct10 == f10_SLLW) begin
         rd_val = signExtend (shift_res_b32);
      end
      else if (funct10 == f10_SRLW) begin
         rd_val = signExtend (shift_res_b32);
      end
      else if (funct10 == f10_SRAW) begin
         rd_val = signExtend (shift_res_b32);
      end

      alu_outputs.control   = trap ? CONTROL_TRAP : CONTROL_STRAIGHT;
      alu_outputs.op_stage2 = OP_Stage2_ALU;
      alu_outputs.rd        = inputs.decoded_instr.rd;
      alu_outputs.val1      = rd_val;
`ifdef INCLUDE_TANDEM_VERIF
      alu_outputs.trace_data = mkTrace_I_RD (fall_through_pc (inputs),
                                             fv_trace_isize (inputs),
                                             fv_trace_instr (inputs),
                                             inputs.decoded_instr.rd,
                                             rd_val);
`endif
   end
`endif

   else if (inputs.decoded_instr.opcode == op_LUI) begin
      //alu_outputs = fv_LUI (inputs);
      Bit #(32) v32 = {inputs.decoded_instr.imm20_U, 12'h0};
      IntXL iv_local = extend (unpack (v32));
      let rd_val = pack (iv_local);

      alu_outputs.op_stage2 = OP_Stage2_ALU;
      alu_outputs.rd        = inputs.decoded_instr.rd;
      alu_outputs.val1      = rd_val;
`ifdef INCLUDE_TANDEM_VERIF
      alu_outputs.trace_data = mkTrace_I_RD (fall_through_pc (inputs),
                                             fv_trace_isize (inputs),
                                             fv_trace_instr (inputs),
                                             inputs.decoded_instr.rd,
                                             rd_val);
`endif
   end

   // If we are in CHERI, we might need to do a setOffset for AUIPCC, so moved to fv_CHERI
   else if (inputs.decoded_instr.opcode == op_AUIPC) begin
      //alu_outputs = fv_AUIPC (inputs);
      alu_outputs.val1      = pack (sum);
   end

   else if (inputs.decoded_instr.opcode == op_LOAD) begin
      //alu_outputs = fv_LD (inputs, Invalid);
      WordXL eaddr = pack (sum);

      alu_outputs.addr           = eaddr;
      alu_outputs.check_address_low = eaddr;
      alu_outputs.check_address_high = zeroExtend(eaddr) + (1 << width_code);

`ifdef ISA_CHERI
      //alu_outputs = checkValidDereference (alu_outputs, authority, authorityIdx, eaddr, width_code, False, True, ?);
`endif

`ifdef INCLUDE_TANDEM_VERIF
`ifdef ISA_F
      if (alu_outputs.rd_in_fpr)
         alu_outputs.trace_data = mkTrace_F_LOAD (fall_through_pc (inputs),
                                                  fv_trace_isize (inputs),
                                                  fv_trace_instr (inputs),
                                                  inputs.decoded_instr.rd,
                                                  ?,
                                                  eaddr,
                                                  inputs.mstatus);
      else
`endif
         alu_outputs.trace_data = mkTrace_I_LOAD (fall_through_pc (inputs),
                                                  fv_trace_isize (inputs),
                                                  fv_trace_instr (inputs),
                                                  inputs.decoded_instr.rd,
                                                  ?,
                                                  eaddr);
`endif
   end

   else if (inputs.decoded_instr.opcode == op_STORE) begin
      //alu_outputs = fv_ST (inputs);
      WordXL eaddr = pack (sum);
      alu_outputs.addr = eaddr;
      alu_outputs.check_address_low = eaddr;
      alu_outputs.check_address_high = zeroExtend(eaddr) + (1 << width_code);

`ifdef INCLUDE_TANDEM_VERIF
`ifdef ISA_F
      if (alu_outputs.rd_in_fpr)
         alu_outputs.trace_data = mkTrace_F_STORE (fall_through_pc (inputs),
                                                   funct3,
                                                   fv_trace_isize (inputs),
                                                   fv_trace_instr (inputs),
                                                   alu_outputs.val2,
                                                   eaddr);
      else
`else
         alu_outputs.trace_data = mkTrace_F_STORE (fall_through_pc (inputs),
                                                   funct3,
                                                   fv_trace_isize (inputs),
                                                   fv_trace_instr (inputs),
                                                   alu_outputs.val2,
                                                   eaddr);
`endif
`endif
   end

   else if (inputs.decoded_instr.opcode == op_MISC_MEM)
      alu_outputs = fv_MISC_MEM (inputs);

   else if (inputs.decoded_instr.opcode == op_SYSTEM)
      alu_outputs = fv_SYSTEM (inputs);

`ifdef ISA_A
   else if (inputs.decoded_instr.opcode == op_AMO)
      alu_outputs = fv_AMO (inputs);
`endif

`ifdef ISA_F
   else if (   (inputs.decoded_instr.opcode == op_LOAD_FP))
      alu_outputs = fv_LD (inputs, Invalid);

   else if (   (inputs.decoded_instr.opcode == op_STORE_FP))
      alu_outputs = fv_ST (inputs);

   else if (   (inputs.decoded_instr.opcode == op_FP)
            || (inputs.decoded_instr.opcode == op_FMADD)
            || (inputs.decoded_instr.opcode == op_FMSUB)
            || (inputs.decoded_instr.opcode == op_FNMSUB)
            || (inputs.decoded_instr.opcode == op_FNMADD))
      alu_outputs = fv_FP (inputs);
`endif

`ifdef ISA_CHERI
   else if ((inputs.decoded_instr.opcode == op_cap_Manip)) begin
      case (funct3)
      f3_cap_CIncOffsetImmediate: begin
      end
      f3_cap_CSetBoundsImmediate: begin
      end
      f3_cap_ThreeOp: begin
         case (funct7)
         f7_cap_CSpecialRW: begin
         end
         f7_cap_CSetBounds: begin
         end
         f7_cap_CSetBoundsExact: begin
         end
         f7_cap_CSetOffset: begin
         end
         f7_cap_CSetAddr: begin
         end
         f7_cap_CIncOffset: begin
         end
         f7_cap_CSeal: begin
         end
         f7_cap_CCSeal: begin
         end
         f7_cap_TwoSrc: begin
            case (inputs.decoded_instr.rd)
               rd_cap_CCall: begin
               end
            default: alu_outputs.control = CONTROL_TRAP;
            endcase // inputs.decoded_instr.rd
         end
         f7_cap_CUnseal: begin
         end
         f7_cap_CTestSubset: begin
         end
         f7_cap_CCopyType: begin
            case (getKind(cs2_val)) matches
               tagged UNSEALED: begin
               end
               tagged SENTRY: begin
               end
               tagged RES0: begin
               end
               tagged RES1: begin
               end
               tagged SEALED_WITH_TYPE .otype: begin
               end
            endcase // getKind (cs2_val)
         end
         f7_cap_CAndPerm: begin
         end
         f7_cap_CSetFlags: begin
         end
         f7_cap_CToPtr: begin
            if (isValidCap(cs1_val)) begin
               //alu_outputs.val1 = zeroExtend(getAddr(cs1_val) - (inputs.rs2_idx == 0 ? ddc_base : cs2_base));
               //addop1 = {getAddr (cs1_val), 1'b1};
               //addop2 = {~(inputs.rs2_idx == 0 ? ddc_base : cs2_base), 1'b1};
               alu_outputs.val1 = zeroExtend (pack (sum));
            end else begin
               alu_outputs.val1 = 0;
            end
         end
         f7_cap_CFromPtr: begin
         end
         f7_cap_CSub: begin
            //alu_outputs.val1 = zeroExtend(getAddr(cs1_val) - getAddr(cs2_val));
            //addop1 = { (getAddr (cs1_val)), 1'b1};
            //addop2 = {~(getAddr (cs2_val)), 1'b1};
            alu_outputs.val1 = zeroExtend (pack (sum));
         end
         f7_cap_CBuildCap: begin
            // TODO SHARE_SEAL
            let result = setValidCap(cs2_val, True);
            alu_outputs.cap_val1 = setKind(result, getKind(cs2_val) == SENTRY ? SENTRY : UNSEALED); // Preserve sentries
            alu_outputs.val1_cap_not_int = True;
         end
         f7_cap_Loads: begin
            Bit#(3) widthCode = zeroExtend(funct5rs2[1:0]);
            Bool is_lr = False;
            Bool is_unsigned = funct5rs2[2] == cap_mem_unsigned && funct5rs2[4] == 1'b0;
            Bool illegal = False;
            if (funct5rs2[4] == 1'b1) begin
               if (funct5rs2[2:0] == 3'b111) begin
                  widthCode = w_SIZE_Q;
               end else begin
`ifdef ISA_A
                  is_lr = True;
                  widthCode = funct5rs2[2:0];
`else
                  illegal = True;
`endif
               end
            end
            if ((widthCode > w_SIZE_MAX) || (is_unsigned && widthCode == w_SIZE_MAX)) illegal = True;
            if (illegal) begin
               // exc_code defaults to exc_code_ILLEGAL_INSTRUCTION
               alu_outputs.control = CONTROL_TRAP;
            end else begin
               //alu_outputs = memCommon(alu_outputs, False, is_unsigned, funct5rs2[3] == cap_mem_ddc, widthCode, inputs.ddc, cs1_val, inputs.rs1_idx, ?, is_lr, {f5_AMO_LR, 2'b0});
               //let eaddr = getAddr(addr) + (useDDC ? getAddr(ddc) : 0);
               Bool useDDC = funct5rs2[3] == cap_mem_ddc;
               //addop1 = {         getAddr (cs1_val), 1'b0};
               //addop2 = {useDDC ? getAddr (inputs.ddc) : 0, 1'b0};
               Addr eaddr = pack (sum);
               let op_stage2 = False ? OP_Stage2_ST : OP_Stage2_LD;
`ifdef ISA_A
               if (is_amo) op_stage2 = OP_Stage2_AMO;
`endif

               //width code must be checked externally

               alu_outputs.op_stage2      = op_stage2;
               alu_outputs.addr           = eaddr;

               // TODO inline this
               //alu_outputs = checkValidDereference(alu_outputs, authority, authorityIdx, eaddr, widthCode, False, True, data);
               alu_outputs.check_address_low = eaddr;



            end
         end
         f7_cap_Stores: begin
            let widthCode = funct5rd[2:0];
            Bool is_sc = funct5rd[4] == 1'b1;
            Bool illegal = False;
            if (is_sc) begin
`ifdef ISA_A
               alu_outputs.rd = inputs.rs2_idx;
`else
               illegal = True;
`endif
            end
            if (widthCode > w_SIZE_MAX) illegal = True;
            if (illegal) begin
               // exc_code defaults to exc_code_ILLEGAL_INSTRUCTION
               alu_outputs.control = CONTROL_TRAP;
            end else begin
               //alu_outputs = memCommon(alu_outputs, True, ?, funct5rd[3] == cap_mem_ddc, widthCode, inputs.ddc, cs1_val, inputs.rs1_idx, cs2_val, is_sc, {f5_AMO_SC, 2'b0});
               //let eaddr = getAddr(addr) + (useDDC ? getAddr(ddc) : 0);
               Bool useDDC = funct5rd[3] == cap_mem_ddc;
               Addr eaddr = pack (sum);
               let op_stage2 = True ? OP_Stage2_ST : OP_Stage2_LD;
`ifdef ISA_A
               if (is_amo) op_stage2 = OP_Stage2_AMO;
`endif

               //width code must be checked externally

               alu_outputs.op_stage2      = op_stage2;
               // TODO move this stuff later
               alu_outputs.addr           = eaddr;
               width_code = widthCode;
               alu_outputs.mem_unsigned   = True ? False : ?;
               alu_outputs.val1           = zeroExtend({f5_AMO_SC, 2'b0});
               alu_outputs.val2           = zeroExtend(getAddr(data)); //for stores
               alu_outputs.cap_val2       = data;
               alu_outputs.val2_cap_not_int = widthCode == w_SIZE_CAP;

               // TODO inline this
               //alu_outputs = checkValidDereference(alu_outputs, authority, authorityIdx, eaddr, widthCode, True, False, data);
               alu_outputs.check_address_low = eaddr;
            end
         end
         f7_cap_TwoOp: begin
            case (funct5rs2)
            f5rs2_cap_CGetLen: begin
            end
            f5rs2_cap_CGetBase: begin
            end
            f5rs2_cap_CGetTag: begin
            end
            f5rs2_cap_CGetSealed: begin
            end
            f5rs2_cap_CRRL: begin
            end
            f5rs2_cap_CRAM: begin
            end
            f5rs2_cap_CMove: begin
            end
            f5rs2_cap_CClearTag: begin
            end
            f5rs2_cap_CGetAddr: begin
            end
            f5rs2_cap_CSealEntry: begin
            end
            f5rs2_cap_CGetOffset: begin
            end
            f5rs2_cap_CGetFlags: begin
            end
            f5rs2_cap_CGetPerm: begin
            end
            f5rs2_cap_CJALR: begin
            end
            f5rs2_cap_CGetType: begin
               case (getKind(cs1_val)) matches
                  tagged UNSEALED: begin
                  end
                  tagged SENTRY: begin
                  end
                  tagged RES0: begin
                  end
                  tagged RES1: begin
                  end
                  tagged SEALED_WITH_TYPE .otype: begin
                  end
               endcase // getKind (cs1_val)
            end
            default: alu_outputs.control = CONTROL_TRAP;
         endcase // funct5rs2
         end
      default: alu_outputs.control = CONTROL_TRAP;
      endcase // funct7
      end
      default: alu_outputs.control = CONTROL_TRAP;
      endcase // funct3
   end
`endif // ISA_CHERI

   else begin
      alu_outputs.control = CONTROL_TRAP;

`ifdef INCLUDE_TANDEM_VERIF
      // Normal trace output (if no trap)
      alu_outputs.trace_data = mkTrace_TRAP (fall_through_pc (inputs),
					     fv_trace_isize (inputs),
					     fv_trace_instr (inputs),
					     ?,
					     ?,
					     ?,
					     ?,
					     ?);
`endif
   end


   return alu_outputs;
endfunction

   let tmp = fv_ALU (inputs);
   method ALU_Outputs alu_outputs;
      return tmp;
   endmethod
endmodule

// ================================================================

endpackage
