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
import Assert :: *;

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
`elsif

   // this is redundant information that is already present in getAddr (toCapPipe (inputs.pcc))
   Addr           pc;
`endif

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
`ifdef DELAY_STAGE1_TRAPS
   Bool trap;
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

typedef Bit #(TAdd #(2, XLEN)) ALUInt;

interface ALU_IFC;
   (* always_enabled *)
   method ALU_Outputs alu_outputs;
endinterface

`ifdef SYNTHESIZE_MODULES
(* synthesize *)
`endif
module mk_ALU #(ALU_Inputs inputs) (ALU_IFC);

function Tuple2 #(IntXL, Bool) fn_add_and_misaligned (ALUInt op1, ALUInt op2);
   let sum_tmp = op1 + op2;
   IntXL sum = unpack (sum_tmp [valueof (XLEN):1]);

   Bool misaligned_target = (pack (sum))[1] == 1'b1;

`ifdef ISA_C
   misaligned_target = False;
`endif
   return tuple2 (sum, misaligned_target);
endfunction

Wrapper2 #(ALUInt, ALUInt, Tuple2 #(IntXL, Bool)) adder_wrapper <- mkUniqueWrapper2 (fn_add_and_misaligned);

function IntXL fn_shift_arith (ALUInt shiftop, Bit #(TLog #(XLEN)) shamt, Bool shift_left);
   Int #(TAdd #(1, XLEN)) shiftop_final = unpack (shiftop[valueof (XLEN):1]);
   let shift_res_full = shiftop_final >> shamt;
   Bit #(XLEN) shift_res = shift_left ? reverseBits (truncate (pack (shift_res_full)))
                                      : truncate (pack (shift_res_full));
   return unpack (shift_res);
endfunction

Wrapper3 #(ALUInt, Bit #(TLog #(XLEN)), Bool, IntXL) shifter_wrapper <- mkUniqueWrapper3 (fn_shift_arith);



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
`ifdef DELAY_STAGE1_TRAPS
               trap      : False,
`endif
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


function Addr fall_through_pc_addr (ALU_Inputs  inputs);
`ifdef ISA_CHERI
   //return getAddr (toCapPipe (inputs.pcc)) + fall_through_pc_inc (inputs);
   return getPCCAddr (inputs.pcc) + fall_through_pc_inc (inputs);
`else
   return inputs.pc + fall_through_pc_inc (inputs);
`endif
endfunction

function Addr fall_through_pc (ALU_Inputs  inputs);
`ifdef ISA_CHERI
   //return getAddr (toCapPipe (inputs.pcc)) + fall_through_pc_inc (inputs);
   return getPC (inputs.pcc) + fall_through_pc_inc (inputs);
`else
   return inputs.pc + fall_through_pc_inc (inputs);
`endif
endfunction

let fallthru_pc = fall_through_pc (inputs);
let fallthru_pcc = fallthru_pc;

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
`ifdef DELAY_STAGE1_TRAPS
  outputs.trap = True;
  outputs.control = CONTROL_STRAIGHT;
`else
  outputs.control = CONTROL_TRAP;
`endif
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
   // TODO this adder and the one in checkValidJump cost ~250 ALMs
   //alu_outputs.check_address_high = zeroExtend(base) + (1 << widthCode);
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
`ifdef DELAY_STAGE1_TRAPS
       alu_outputs.trap = True;
       //alu_outputs.trap = False;
       alu_outputs.control = CONTROL_STRAIGHT;
`else
       alu_outputs.control = CONTROL_TRAP;
`endif
       alu_outputs.exc_code = exc_code_INSTR_ADDR_MISALIGNED;
   end
   alu_outputs.check_enable = branchTaken;
   alu_outputs.check_authority = authority;
   alu_outputs.check_authority_idx = authIdx;
   alu_outputs.check_address_low = target;
   //alu_outputs.check_address_high = zeroExtend(target) + 2;
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


function ActionValue #(ALU_Outputs) fv_BRANCH (ALU_Inputs inputs);
//function ALU_Outputs fv_BRANCH (ALU_Inputs inputs);
actionvalue
   let rs1_val = inputs.rs1_val;
   let rs2_val = inputs.rs2_val;

   // Signed versions of rs1_val and rs2_val
   IntXL s_rs1_val = unpack (inputs.rs1_val);
   IntXL s_rs2_val = unpack (inputs.rs2_val);

`ifdef MERGE_IMMEDIATE
   IntXL offset        = extend (unpack (inputs.decoded_instr.imm));
`else
   IntXL offset        = extend (unpack (inputs.decoded_instr.imm13_SB));
`endif
   //Addr  branch_target = pack (unpack (inputs.pc) + offset);
   //ALUInt addop1 = {pack (getAddr (toCapPipe (inputs.pcc))), 1'b0};
   ALUInt addop1 = {1'b0, pack (getPC (inputs.pcc)), 1'b0};
   ALUInt addop2 = {1'b0, pack (            offset), 1'b0};
   match {.sum, .misaligned_target} <- adder_wrapper.func (addop1, addop2);
   Addr branch_target = pack (sum);
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

//   Bool misaligned_target = (branch_target [1] == 1'b1);
//`ifdef ISA_C
//   misaligned_target = False;
//`endif

   Exc_Code exc_code = exc_code_ILLEGAL_INSTRUCTION;
   if ((! trap) && branch_taken && misaligned_target) begin
      trap = True;
      exc_code = exc_code_INSTR_ADDR_MISALIGNED;
   end

`ifdef ISA_CHERI
   let pcc_pc = getPC (inputs.pcc);
   let cf_info   = CF_Info {cf_op       : CF_BR,
			    from_PC     : pcc_pc,
			    taken       : branch_taken,
			    fallthru_PC : fallthru_pcc,
			    taken_PC    : branch_target };
`else
   let cf_info   = CF_Info {cf_op       : CF_BR,
			    from_PC     : inputs.pc,
			    taken       : branch_taken,
			    fallthru_PC : fall_through_pc (inputs),
			    taken_PC    : branch_target };
`endif

   let alu_outputs = alu_outputs_base;
   let next_pc     = (branch_taken ? branch_target : fallthru_pc);
`ifdef DELAY_STAGE1_TRAPS
   alu_outputs.trap = trap;
   alu_outputs.control = (trap ? CONTROL_STRAIGHT : (branch_taken ? CONTROL_BRANCH : CONTROL_STRAIGHT));
`else
   alu_outputs.control   = (trap ? CONTROL_TRAP : (branch_taken ? CONTROL_BRANCH : CONTROL_STRAIGHT));
`endif
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
   //alu_outputs = checkValidJump(alu_outputs, branch_taken, toCapPipe(inputs.pcc), getPCCBase(inputs.pcc), {1,scr_addr_PCC}, getPCCBase(inputs.pcc) + next_pc);
   alu_outputs = checkValidJump(alu_outputs, branch_taken, toCapPipeNoOffset(inputs.pcc), getPCCBase(inputs.pcc), {1,scr_addr_PCC}, getPCCBase(inputs.pcc) + next_pc);
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

//function ALU_Outputs fv_JAL (ALU_Inputs inputs);
function ActionValue #(ALU_Outputs) fv_JAL (ALU_Inputs inputs);
actionvalue
`ifdef MERGE_IMMEDIATE
   IntXL offset  = extend (unpack (inputs.decoded_instr.imm));
`else
   IntXL offset  = extend (unpack (inputs.decoded_instr.imm21_UJ));
`endif
   //Addr  next_pc = pack (unpack (inputs.pc) + offset);
   // PCC_CHANGES: i think this used to be a getAddr (toCapPipe (pcc))?
   ALUInt addop1 = {1'b0, pack (getPC (inputs.pcc)), 1'b0};
   ALUInt addop2 = {1'b0, pack (            offset), 1'b0};
   match {.sum, .misaligned_target} <- adder_wrapper.func (addop1, addop2);
   Addr  next_pc = pack (sum);
   Addr  ret_pc  = fallthru_pc;

//   Bool misaligned_target = (next_pc [1] == 1'b1);
//`ifdef ISA_C
//   misaligned_target = False;
//`endif

`ifdef ISA_CHERI
   let pcc_pc = getPC (inputs.pcc);
   let cf_info   = CF_Info {cf_op       : CF_JAL,
			    from_PC     : pcc_pc,
			    taken       : True,
			    fallthru_PC : fallthru_pcc,
			    taken_PC    : next_pc };
`else
   let cf_info   = CF_Info {cf_op       : CF_JAL,
			    from_PC     : inputs.pc,
			    taken       : True,
			    fallthru_PC : ret_pc,
			    taken_PC    : next_pc };
`endif

   let alu_outputs = alu_outputs_base;
`ifdef DELAY_STAGE1_TRAPS
   alu_outputs.trap = misaligned_target;
   alu_outputs.control = (misaligned_target ? CONTROL_STRAIGHT : CONTROL_BRANCH);
`else
   alu_outputs.control   = (misaligned_target ? CONTROL_TRAP : CONTROL_BRANCH);
`endif
   alu_outputs.exc_code  = exc_code_INSTR_ADDR_MISALIGNED;
   alu_outputs.op_stage2 = OP_Stage2_ALU;
   alu_outputs.rd        = inputs.decoded_instr.rd;
   alu_outputs.addr      = next_pc;
   alu_outputs.val1      = extend (ret_pc);
   alu_outputs.cf_info   = cf_info;

`ifdef ISA_CHERI
   //alu_outputs = checkValidJump(alu_outputs, True, toCapPipe(inputs.pcc), getPCCBase(inputs.pcc), {1,scr_addr_PCC}, getPCCBase(inputs.pcc) + next_pc);
   alu_outputs = checkValidJump(alu_outputs, True, toCapPipeNoOffset(inputs.pcc), getPCCBase(inputs.pcc), {1,scr_addr_PCC}, getPCCBase(inputs.pcc) + next_pc);
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
endactionvalue
endfunction

// ----------------------------------------------------------------
// JALR

//function ALU_Outputs fv_JALR (ALU_Inputs inputs);
function ActionValue #(ALU_Outputs) fv_JALR (ALU_Inputs inputs);
actionvalue
   let rs1_val = inputs.rs1_val;
   let rs2_val = inputs.rs2_val;

   // Signed versions of rs1_val and rs2_val
   IntXL s_rs1_val = unpack (rs1_val);
   IntXL s_rs2_val = unpack (rs2_val);
`ifdef MERGE_IMMEDIATE
   IntXL offset    = extend (unpack (inputs.decoded_instr.imm));
`else
   IntXL offset    = extend (unpack (inputs.decoded_instr.imm12_I));
`endif
   //Addr  next_pc   = pack (s_rs1_val + offset);
   ALUInt addop1 = {1'b0, pack (s_rs1_val), 1'b0};
   ALUInt addop2 = {1'b0, pack    (offset), 1'b0};
   match {.sum, .misaligned_target} <- adder_wrapper.func (addop1, addop2);
   Addr next_pc = pack (sum);
   Addr  ret_pc    = fall_through_pc (inputs);

   // next_pc [0] should be cleared
   next_pc [0] = 1'b0;

//   Bool misaligned_target = (next_pc [1] == 1'b1);
//`ifdef ISA_C
//   misaligned_target = False;
//`endif

`ifdef ISA_CHERI
   let pcc_pc = getPC (inputs.pcc);
   let target_pc = getPCCBase(inputs.pcc) + next_pc;
   let cf_info   = CF_Info {cf_op       : CF_JALR,
			    from_PC     : pcc_pc,
			    taken       : True,
			    fallthru_PC : pcc_pc + fall_through_pc_inc(inputs),
			    taken_PC    : target_pc };
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
   //alu_outputs = checkValidJump(alu_outputs, True, toCapPipe(inputs.pcc), getPCCBase(inputs.pcc), {1,scr_addr_PCC}, target_addr);
   alu_outputs = checkValidJump(alu_outputs, True, toCapPipeNoOffset(inputs.pcc), getPCCBase(inputs.pcc), {1,scr_addr_PCC}, target_pc);
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
endactionvalue
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
`ifdef MERGE_IMMEDIATE
				? truncate (inputs.decoded_instr.imm)
`else
				? truncate (inputs.decoded_instr.imm12_I)
`endif
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
`ifdef MERGE_IMMEDIATE
   Bool trap = ((rv_version == RV32) && (inputs.decoded_instr.imm[5] == 1));
`else
   Bool trap = ((rv_version == RV32) && (inputs.decoded_instr.imm12_I [5] == 1));
`endif

   let alu_outputs       = alu_outputs_base;
`ifdef DELAY_STAGE1_TRAPS
   alu_outputs.trap = trap;
   alu_outputs.control = CONTROL_STRAIGHT;
`else
   alu_outputs.control   = (trap ? CONTROL_TRAP : CONTROL_STRAIGHT);
`endif
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
`ifdef MERGE_IMMEDIATE
      s_rs2_val_local = extend (unpack (inputs.decoded_instr.imm));
`else
      s_rs2_val_local = extend (unpack (inputs.decoded_instr.imm12_I));
`endif
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
`ifdef DELAY_STAGE1_TRAPS
   alu_outputs.trap = trap;
   alu_outputs.control = CONTROL_STRAIGHT;
`else
   alu_outputs.control   = (trap ? CONTROL_TRAP : CONTROL_STRAIGHT);
`endif
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

`ifdef MERGE_IMMEDIATE
   Bit #(5) shamt       = truncate (inputs.decoded_instr.imm);
`else
   Bit #(5) shamt       = truncate (inputs.decoded_instr.imm12_I);
`endif
   Bool     shamt5_is_0 = (inputs.instr [25] == 1'b0);

   let    funct3 = inputs.decoded_instr.funct3;
   Bool   trap   = False;
   WordXL rd_val = ?;

   if (funct3 == f3_ADDIW) begin
`ifdef MERGE_IMMEDIATE
      IntXL  s_rs2_val = extend (unpack (inputs.decoded_instr.imm));
`else
      IntXL  s_rs2_val = extend (unpack (inputs.decoded_instr.imm12_I));
`endif
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
`ifdef DELAY_STAGE1_TRAPS
   alu_outputs.trap = True;
   alu_outputs.control = CONTROL_STRAIGHT;
`else
   alu_outputs.control   = (trap ? CONTROL_TRAP : CONTROL_STRAIGHT);
`endif
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
`ifdef DELAY_STAGE1_TRAPS
   alu_outputs.trap = True;
   alu_outputs.control = CONTROL_STRAIGHT;
`else
   alu_outputs.control   = (trap ? CONTROL_TRAP : CONTROL_STRAIGHT);
`endif
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
`ifdef MERGE_IMMEDIATE
   Bit #(32)  v32    = { inputs.decoded_instr.imm[19:0], 12'h0 };
`else
   Bit #(32)  v32    = { inputs.decoded_instr.imm20_U, 12'h0 };
`endif
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
`ifdef MERGE_IMMEDIATE
   IntXL  iv     = extend (unpack ({ inputs.decoded_instr.imm[19:0], 12'b0}));
`else
   IntXL  iv     = extend (unpack ({ inputs.decoded_instr.imm20_U, 12'b0}));
`endif
   // PCC_CHANGES: i think this used to be a getAddr (toCapPipe (pcc))?
   IntXL  pc_s   = unpack (getPC (inputs.pcc));
   WordXL rd_val = pack (pc_s + iv);

   let alu_outputs       = alu_outputs_base;
   alu_outputs.op_stage2 = OP_Stage2_ALU;
   alu_outputs.rd        = inputs.decoded_instr.rd;
`ifdef ISA_CHERI
   //if (getFlags(toCapPipe(inputs.pcc))[0] == 1'b1) begin
   if (getFlags(toCapPipeNoOffset(inputs.pcc))[0] == 1'b1) begin
       alu_outputs.val1_source = SET_OFFSET;
       // we are setting an offset so we don't care about the old one
       //alu_outputs.internal_op1 = toCapPipe(inputs.pcc);
       alu_outputs.internal_op1 = toCapPipeNoOffset(inputs.pcc);
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

`ifdef MERGE_IMMEDIATE
   IntXL  imm_s = extend (unpack (inputs.decoded_instr.imm));
`else
   IntXL  imm_s = extend (unpack (inputs.decoded_instr.imm12_I));
`endif
`ifdef ISA_CHERI
   if (valueOf(XLEN) == 32 && inputs.decoded_instr.funct3 == f3_LD) size = Valid(w_SIZE_D);

   //let authority = getFlags(toCapPipe(inputs.pcc))[0] == 1'b0 ? inputs.ddc : inputs.cap_rs1_val;
   //let authorityIdx = getFlags(toCapPipe(inputs.pcc))[0] == 1'b0 ? {1,scr_addr_DDC} : {0,inputs.rs1_idx};
   //WordXL eaddr = getFlags(toCapPipe(inputs.pcc))[0] == 1'b0 ? getAddr(inputs.ddc) + inputs.rs1_val + pack(imm_s) : getAddr(inputs.cap_rs1_val) + pack(imm_s);
   let authority = getFlags(toCapPipeNoOffset(inputs.pcc))[0] == 1'b0 ? inputs.ddc : inputs.cap_rs1_val;
   let authorityIdx = getFlags(toCapPipeNoOffset(inputs.pcc))[0] == 1'b0 ? {1,scr_addr_DDC} : {0,inputs.rs1_idx};
   WordXL eaddr = getFlags(toCapPipeNoOffset(inputs.pcc))[0] == 1'b0 ? getAddr(inputs.ddc) + inputs.rs1_val + pack(imm_s) : getAddr(inputs.cap_rs1_val) + pack(imm_s);
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

`ifdef DELAY_STAGE1_TRAPS
   alu_outputs.trap = !(legal_LD && legal_FP_LD);
   alu_outputs.control = CONTROL_STRAIGHT;
`else
   alu_outputs.control   = ((legal_LD && legal_FP_LD) ? CONTROL_STRAIGHT
                                                      : CONTROL_TRAP);
`endif
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
`ifdef MERGE_IMMEDIATE
   IntXL  imm_s     = extend (unpack (inputs.decoded_instr.imm));
`else
   IntXL  imm_s     = extend (unpack (inputs.decoded_instr.imm12_S));
`endif
`ifdef ISA_CHERI
   //let authority = getFlags(toCapPipe(inputs.pcc))[0] == 1'b0 ? inputs.ddc : inputs.cap_rs1_val;
   //let authorityIdx = getFlags(toCapPipe(inputs.pcc))[0] == 1'b0 ? {1,scr_addr_DDC} : {0,inputs.rs1_idx};
   //WordXL eaddr = getFlags(toCapPipe(inputs.pcc))[0] == 1'b0 ? getAddr(inputs.ddc) + inputs.rs1_val + pack(imm_s) : getAddr(inputs.cap_rs1_val) + pack(imm_s);
   let authority = getFlags(toCapPipeNoOffset(inputs.pcc))[0] == 1'b0 ? inputs.ddc : inputs.cap_rs1_val;
   let authorityIdx = getFlags(toCapPipeNoOffset(inputs.pcc))[0] == 1'b0 ? {1,scr_addr_DDC} : {0,inputs.rs1_idx};
   WordXL eaddr = getFlags(toCapPipeNoOffset(inputs.pcc))[0] == 1'b0 ? getAddr(inputs.ddc) + inputs.rs1_val + pack(imm_s) : getAddr(inputs.cap_rs1_val) + pack(imm_s);
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

`ifdef DELAY_STAGE1_TRAPS
   alu_outputs.trap = !(legal_ST && legal_FP_ST);
   alu_outputs.control = CONTROL_STRAIGHT;
`else
   alu_outputs.control   = ((legal_ST && legal_FP_ST) ? CONTROL_STRAIGHT
                                                      : CONTROL_TRAP);
`endif
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
   //if (valueOf(XLEN) == 64 && inputs.decoded_instr.funct3 == f3_LQ) begin
   //    // don't do anything here
   //    //return fv_LD(inputs, Valid(w_SIZE_Q));
   //end else
`endif
   begin
       let alu_outputs = alu_outputs_base;
       alu_outputs.control  = (  (inputs.decoded_instr.funct3 == f3_FENCE_I)
			       ? CONTROL_FENCE_I
			       : (  (inputs.decoded_instr.funct3 == f3_FENCE)
			          ? CONTROL_FENCE
`ifdef DELAY_STAGE1_TRAPS
                                  : CONTROL_STRAIGHT));
`else
			          : CONTROL_TRAP));
`endif

`ifdef DELAY_STAGE1_TRAPS
      alu_outputs.trap = !(inputs.decoded_instr.funct3 == f3_FENCE_I || inputs.decoded_instr.funct3 == f3_FENCE);
`endif

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
`ifdef MERGE_IMMEDIATE
	    if (inputs.decoded_instr.imm[11:0] == f12_ECALL) begin
`else
	    if (inputs.decoded_instr.imm12_I == f12_ECALL) begin
`endif
`ifdef DELAY_STAGE1_TRAPS
               alu_outputs.trap = True;
               alu_outputs.control = CONTROL_STRAIGHT;
`else
	       alu_outputs.control  = CONTROL_TRAP;
`endif
	       alu_outputs.exc_code = ((inputs.cur_priv == u_Priv_Mode)
				       ? exc_code_ECALL_FROM_U
				       : ((inputs.cur_priv == s_Priv_Mode)
					  ? exc_code_ECALL_FROM_S
					  : exc_code_ECALL_FROM_M));
	    end

	    // EBREAK instruction
`ifdef MERGE_IMMEDIATE
	    else if (inputs.decoded_instr.imm[11:0] == f12_EBREAK) begin
`else
	    else if (inputs.decoded_instr.imm12_I == f12_EBREAK) begin
`endif
`ifdef DELAY_STAGE1_TRAPS
               alu_outputs.trap = True;
               alu_outputs.control = CONTROL_STRAIGHT;
`else
	       alu_outputs.control  = CONTROL_TRAP;
`endif
	       alu_outputs.exc_code = exc_code_BREAKPOINT;
	    end

	    // MRET instruction
	    else if (   (inputs.cur_priv >= m_Priv_Mode)
`ifdef MERGE_IMMEDIATE
		     && (inputs.decoded_instr.imm[11:0] == f12_MRET))
`else
		     && (inputs.decoded_instr.imm12_I == f12_MRET))
`endif
	       begin
                  //if (getHardPerms(toCapPipe(inputs.pcc)).accessSysRegs) begin
                  if (getHardPerms(toCapPipeNoOffset(inputs.pcc)).accessSysRegs) begin
                     alu_outputs.control = CONTROL_MRET;
                  end else begin
`ifdef DELAY_STAGE1_TRAPS
               alu_outputs.trap = True;
               alu_outputs.control = CONTROL_STRAIGHT;
`else
                     alu_outputs.control = CONTROL_TRAP;
`endif
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
`ifdef MERGE_IMMEDIATE
		     && (inputs.decoded_instr.imm[11:0] == f12_SRET))
`else
		     && (inputs.decoded_instr.imm12_I == f12_SRET))
`endif
	       begin
                  //if (getHardPerms(toCapPipe(inputs.pcc)).accessSysRegs) begin
                  if (getHardPerms(toCapPipeNoOffset(inputs.pcc)).accessSysRegs) begin
                     alu_outputs.control = CONTROL_SRET;
                  end else begin
`ifdef DELAY_STAGE1_TRAPS
               alu_outputs.trap = True;
               alu_outputs.control = CONTROL_STRAIGHT;
`else
                     alu_outputs.control = CONTROL_TRAP;
`endif
                     alu_outputs.exc_code = exc_code_CHERI;
                     alu_outputs.cheri_exc_code = exc_code_CHERI_SysRegsPerm;
                     alu_outputs.cheri_exc_reg = {1'b1, scr_addr_PCC};
                  end
	       end
`endif

	    /*
	    // URET instruction (future: Piccolo does not support 'N' extension)
	    else if (   (inputs.cur_priv >= u_Priv_Mode)
`ifdef MERGE_IMMEDIATE
		     && (inputs.decoded_instr.imm[11:0] == f12_URET))
`else
		     && (inputs.decoded_instr.imm12_I == f12_URET))
`endif
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
`ifdef MERGE_IMMEDIATE
		     && (inputs.decoded_instr.imm[11:0] == f12_WFI))
`else
		     && (inputs.decoded_instr.imm12_I == f12_WFI))
`endif
	       begin
		  alu_outputs.control = CONTROL_WFI;
	       end

	    else begin
`ifdef DELAY_STAGE1_TRAPS
               alu_outputs.trap = True;
               alu_outputs.control = CONTROL_STRAIGHT;
`else
	       alu_outputs.control = CONTROL_TRAP;
`endif
	    end
	 end

      else begin
`ifdef DELAY_STAGE1_TRAPS
         alu_outputs.trap = True;
         alu_outputs.control = CONTROL_STRAIGHT;
`else
	 alu_outputs.control = CONTROL_TRAP;
`endif
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
`ifdef DELAY_STAGE1_TRAPS
         alu_outputs.trap = True;
         alu_outputs.control = CONTROL_STRAIGHT;
`else
      alu_outputs.control = CONTROL_TRAP;
`endif
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
`ifdef DELAY_STAGE1_TRAPS
   alu_outputs.trap    = !(inst_is_legal && rm_is_legal);
   alu_outputs.control = CONTROL_STRAIGHT;
`else
   alu_outputs.control     = ((inst_is_legal && rm_is_legal) ? CONTROL_STRAIGHT
			                                     : CONTROL_TRAP);
`endif
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
   //let authority = getFlags(toCapPipe(inputs.pcc))[0] == 1'b0 ? inputs.ddc : inputs.cap_rs1_val;
   //let authorityIdx = getFlags(toCapPipe(inputs.pcc))[0] == 1'b0 ? {1,scr_addr_DDC} : {0,inputs.rs1_idx};
   //WordXL eaddr = getFlags(toCapPipe(inputs.pcc))[0] == 1'b0 ? getAddr(inputs.ddc) + inputs.rs1_val : getAddr(inputs.cap_rs1_val);
   let authority = getFlags(toCapPipeNoOffset(inputs.pcc))[0] == 1'b0 ? inputs.ddc : inputs.cap_rs1_val;
   let authorityIdx = getFlags(toCapPipeNoOffset(inputs.pcc))[0] == 1'b0 ? {1,scr_addr_DDC} : {0,inputs.rs1_idx};
   WordXL eaddr = getFlags(toCapPipeNoOffset(inputs.pcc))[0] == 1'b0 ? getAddr(inputs.ddc) + inputs.rs1_val : getAddr(inputs.cap_rs1_val);
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

`ifdef DELAY_STAGE1_TRAPS
   alu_outputs.trap    = !(legal_f5 && legal_width);
   alu_outputs.control = CONTROL_STRAIGHT;
`else
   alu_outputs.control   = ((legal_f5 && legal_width) ? CONTROL_STRAIGHT : CONTROL_TRAP);
`endif
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


function ActionValue #(ALU_Outputs) fv_CHERI (ALU_Inputs inputs, WordXL ddc_base);
actionvalue
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
`ifdef MERGE_IMMEDIATE
             alu_outputs.internal_op2 = signExtend(inputs.decoded_instr.imm);
`else
             alu_outputs.internal_op2 = signExtend(inputs.decoded_instr.imm12_I);
`endif
             alu_outputs.internal_offset_inc_not_set = True;
        end
        f3_cap_CSetBoundsImmediate: begin
            check_cs1_tagged = True;
            check_cs1_unsealed = True;

            alu_outputs.val1_source = SET_BOUNDS;
`ifdef MERGE_IMMEDIATE
            alu_outputs.internal_op2 = zeroExtend(inputs.decoded_instr.imm);
`else
            alu_outputs.internal_op2 = zeroExtend(inputs.decoded_instr.imm12_I);
`endif
            alu_outputs.internal_bounds_exact = False;
            alu_outputs.check_authority_idx  = zeroExtend(inputs.rs1_idx);
        end
        f3_cap_ThreeOp: begin
            case (funct7)
            f7_cap_CSpecialRW: begin
                if (inputs.decoded_instr.rs2 == scr_addr_PCC && inputs.decoded_instr.rs1 == 0) begin
                    //alu_outputs.cap_val1 = toCapPipe(inputs.pcc);
                    alu_outputs.cap_val1 = toCapPipeNoOffset(inputs.pcc);
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
                    default: begin
`ifdef DELAY_STAGE1_TRAPS
                        alu_outputs.trap = True;
                        alu_outputs.control = CONTROL_STRAIGHT;
`else
                        alu_outputs.control = CONTROL_TRAP;
`endif
                    end
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
                    //alu_outputs.val1 = zeroExtend(getAddr(cs1_val) - (inputs.rs2_idx == 0 ? ddc_base : cs2_base));
                    ALUInt addop1 = {1'b0, pack (zeroExtend (getAddr (cs1_val))), 1'b1};
                    ALUInt addop2 = {1'b0, pack (~(inputs.rs2_idx == 0 ? ddc_base : cs2_base)), 1'b1};
                    match {.sum, .misaligned_addr} <- adder_wrapper.func (addop1, addop2);
                    alu_outputs.val1 = pack (sum);
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
                ALUInt addop1 = {1'b0, pack (zeroExtend (getAddr (cs1_val))), 1'b1};
                ALUInt addop2 = {1'b0, ~(pack (getAddr (cs2_val))), 1'b1};
                match {.sum, .misaligned_addr} <- adder_wrapper.func (addop1, addop2);
                alu_outputs.val1 = pack (sum);
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
`ifdef DELAY_STAGE1_TRAPS
                    alu_outputs.trap = True;
                    alu_outputs.control = CONTROL_STRAIGHT;
`else
                    alu_outputs.control = CONTROL_TRAP;
`endif
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
`ifdef DELAY_STAGE1_TRAPS
                    alu_outputs.trap = True;
                    alu_outputs.control = CONTROL_STRAIGHT;
`else
                    alu_outputs.control = CONTROL_TRAP;
`endif
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

                    //let pcc_addr = getAddr(toCapPipe(inputs.pcc));
                    let pcc_pc = getPC (inputs.pcc);
                    let cf_info   = CF_Info {cf_op       : CF_JALR,
                                             from_PC     : pcc_pc,
                                             taken       : True,
                                             //fallthru_PC : pcc_addr + fall_through_pc_inc(inputs),
                                             fallthru_PC : fall_through_pc (inputs),
                                             taken_PC    : getAddr(maskedTarget) };

                    next_pc[0] = 1'b0;

                    alu_outputs.control   = CONTROL_CAPBRANCH;
                    alu_outputs.cf_info   = cf_info;

                    alu_outputs.addr      = next_pc;
                    alu_outputs.pcc       = fromCapPipe(setKind(maskedTarget, UNSEALED));
                    alu_outputs.val1_source = SET_OFFSET;
                    //alu_outputs.internal_op1 = toCapPipe(inputs.pcc);
                    alu_outputs.internal_op1 = toCapPipeNoOffset(inputs.pcc);
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
                default: begin
`ifdef DELAY_STAGE1_TRAPS
                    alu_outputs.trap    = True;
                    alu_outputs.control = CONTROL_STRAIGHT;
`else
                    alu_outputs.control = CONTROL_TRAP;
`endif
                end
                endcase
            end
            default: begin
`ifdef DELAY_STAGE1_TRAPS
                alu_outputs.trap    = True;
                alu_outputs.control = CONTROL_STRAIGHT;
`else
                alu_outputs.control = CONTROL_TRAP;
`endif
            end
            endcase
        end
        default: begin
`ifdef DELAY_STAGE1_TRAPS
            alu_outputs.trap    = True;
            alu_outputs.control = CONTROL_STRAIGHT;
`else
            alu_outputs.control = CONTROL_TRAP;
`endif
        end
        endcase
    end

    // uses 1k ALMs
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
        //alu_outputs.check_address_high = zeroExtend(getAddr(cs1_val)) + zeroExtend(alu_outputs.internal_op2);
        ALUInt addop1 = {1'b0, pack (zeroExtend (getAddr (cs1_val))), 1'b0};
        ALUInt addop2 = {1'b0, pack (zeroExtend (alu_outputs.internal_op2)), 1'b0};
        match {.sum, .misaligned_addr} <- adder_wrapper.func (addop1, addop2);
        alu_outputs.check_address_high = pack (zeroExtend (sum));
        alu_outputs.check_exact_enable = alu_outputs.internal_bounds_exact;
        alu_outputs.check_exact_success = result.exact;
    end
    GET_PRECISION: begin
        CapReg nullCapReg = nullCap;
        let result = getRepresentableAlignmentMask(nullCapReg, inputs.rs1_val);
        if (alu_outputs.internal_crrl_not_cram) begin
            //result = (inputs.rs1_val + ~result) & result;
            ALUInt addop1 = {1'b0, pack (inputs.rs1_val), 1'b0};
            ALUInt addop2 = {1'b0, pack (       ~result), 1'b0};
            match {.sum, .misaligned_addr} <- adder_wrapper.func (addop1, addop2);
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
endactionvalue
endfunction
`endif

/*
function Tuple2 #(CapPipe, CapPipe) fv_cap_operands (ALU_Inputs inputs);
   let cs1 = inputs.cap_rs1_val;
   let cs2 = inputs.cap_rs2_val;
   let pcc = toCapPipe (inputs.pcc);
   let ddc = inputs.ddc;

   CapPipe op1 = inputs.cap_rs1_val;
   CapPipe op2 = inputs.cap_rs2_val;

   let funct3 = inputs.decoded_instr.funct3;
   alu_outputs.rd = inputs.decoded_instr.rd;
   alu_outputs.op_stage2 = OP_Stage2_ALU;
   case (funct3)
   f3_cap_CIncOffsetImmediate: begin
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
               WordXL target = {truncateLSB(getAddr(cs1_val)), 1'b0};
               //alu_outputs = checkValidJump(alu_outputs, True, cs1_val, cs1_base, zeroExtend(inputs.rs1_idx), target);
               alu_outputs.check_enable = True;
`ifdef ISA_C
                  Bool misaligned_target = cs1_base[0] != 1'b0;
`else
                  Bool misaligned_target = (target [1] == 1'b1) || (cs1_base[1:0] != 2'b0);
`endif
                  if (misaligned_target) begin
`ifdef DELAY_STAGE1_TRAPS
                     alu_outputs.trap = True;
                     //alu_outputs.trap = False;
                     alu_outputs.control = CONTROL_STRAIGHT;
`else
                     alu_outputs.control = CONTROL_TRAP;
`endif
                     alu_outputs.exc_code = exc_code_INSTR_ADDR_MISALIGNED;
                  end
                  authority = cs1_val;
                  authority_base = cs1_base;
                  authority_top = cs1_top;
                  authorityIdx = {1'b0, inputs.rs1_idx};
                  check_address_low = target;
                  addop1 = {target, 1'b0};
                  addop2 = {     2, 1'b0};
                  check_address_high_from_sum = True;
               end
            default: begin
`ifdef DELAY_STAGE1_TRAPS
               alu_outputs.trap    = True;
               alu_outputs.control = CONTROL_STRAIGHT;
`else
               alu_outputs.control = CONTROL_TRAP;
`endif
            end
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
`ifdef DELAY_STAGE1_TRAPS
               alu_outputs.trap    = True;
               alu_outputs.control = CONTROL_STRAIGHT;
`else
               alu_outputs.control = CONTROL_TRAP;
`endif
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
`ifdef DELAY_STAGE1_TRAPS
               alu_outputs.trap    = True;
               alu_outputs.control = CONTROL_STRAIGHT;
`else
               alu_outputs.control = CONTROL_TRAP;
`endif
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
               op1 = cs1;
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
`ifdef DELAY_STAGE1_TRAPS
                   alu_outputs.trap    = True;
                   alu_outputs.control = CONTROL_STRAIGHT;
`else
                   alu_outputs.control = CONTROL_TRAP;
`endif
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
            default: begin
`ifdef DELAY_STAGE1_TRAPS
               alu_outputs.trap = True;
               alu_outputs.control = CONTROL_TRAP;
`else
               alu_outputs.control = CONTROL_TRAP;
`endif
            end
         endcase // funct5rs2
         end
      default: begin
`ifdef DELAY_STAGE1_TRAPS
         alu_outputs.trap = True;
         alu_outputs.control = CONTROL_TRAP;
`else
         alu_outputs.control = CONTROL_TRAP;
`endif
      end
      endcase // funct7
      end
      default: begin
`ifdef DELAY_STAGE1_TRAPS
               alu_outputs.trap = True;
               alu_outputs.control = CONTROL_TRAP;
`else
         alu_outputs.control = CONTROL_TRAP;
`endif
      end
      endcase // funct3

endfunction
*/

// ----------------------------------------------------------------
// Top-level ALU function

function ALU_Outputs fv_ALU (ALU_Inputs inputs);
   let alu_outputs = alu_outputs_base;

   alu_outputs.val1_fast = inputs.rs1_val;
   alu_outputs.val2_fast = inputs.rs2_val;
   alu_outputs.rd = inputs.decoded_instr.rd;
   //let ddc_base = getBase (inputs.ddc);

   ALUInt addop1 = ?;
   ALUInt addop2 = ?;
   //ALUInt shiftop = ?;

   Bit #(TAdd #(XLEN, 1)) cmpop1 = zeroExtend (inputs.rs1_val);
   Bit #(TAdd #(XLEN, 1)) cmpop2 = zeroExtend (inputs.rs2_val);

   let rs1_val = inputs.rs1_val;
   let rs2_val = inputs.rs2_val;

   IntXL s_rs1_val = unpack (rs1_val);
   IntXL s_rs2_val = unpack (rs2_val);

   Bit #(1) instr_b30 = inputs.instr [30];
   Bool subtract = ((inputs.decoded_instr.opcode == op_OP) && (instr_b30 == 1'b1));

   let funct3 = inputs.decoded_instr.funct3;
   let funct10 = inputs.decoded_instr.funct10;

`ifdef MERGE_IMMEDIATE
   IntXL iv = extend (unpack ({inputs.decoded_instr.imm[19:0], 12'b0}));
`else
   IntXL iv = extend (unpack ({inputs.decoded_instr.imm20_U, 12'b0}));
`endif
   //IntXL pc_s = unpack (getAddr (toCapPipe (inputs.pcc)));
   IntXL pc_s = unpack (getPC (inputs.pcc));

`ifdef MERGE_IMMEDIATE
   IntXL imm_i_s = extend (unpack (inputs.decoded_instr.imm));
   IntXL imm_s_s = extend (unpack (inputs.decoded_instr.imm));
`else
   IntXL imm_i_s = extend (unpack (inputs.decoded_instr.imm12_I));
   IntXL imm_s_s = extend (unpack (inputs.decoded_instr.imm12_S));
`endif

   Bit #(32) rs1_val_b32 = rs1_val [31:0];
   Bit #(32) rs2_val_b32 = rs2_val [31:0];

   Int #(32) s_rs1_val_b32 = unpack (rs1_val_b32);
   Int #(32) s_rs2_val_b32 = unpack (rs2_val_b32);

   Bit #(TLog #(XLEN)) shamt = (  (inputs.decoded_instr.opcode == op_OP_IMM)
                               || (inputs.decoded_instr.opcode == op_OP_IMM_32))
`ifdef MERGE_IMMEDIATE
                                  ? truncate (inputs.decoded_instr.imm)
`else
                                  ? truncate (inputs.decoded_instr.imm12_I)
`endif
                                  : truncate (rs2_val);

`ifdef MERGE_IMMEDIATE
   Bool shamt5_is_0 = inputs.decoded_instr.imm[5] == 0;
`else
   Bool shamt5_is_0 = inputs.decoded_instr.imm12_I[5] == 0;
`endif
   Bool shift_left = ?;
   //Bit #(1) shift_arith = ?;

   Bool trap = False;
   Bool mem_illegal = False;


   let fallthru_pc_addr = fall_through_pc_addr (inputs);
   let fallthru_pc_pc = fall_through_pc (inputs);
`ifdef ISA_CHERI
   //let pcc_addr = getAddr (toCapPipe (inputs.pcc));
   let pcc_pc = pack (pc_s);
   let pcc_addr = getPCCAddr (inputs.pcc);
   let fallthru_pcc_pc   = fallthru_pc_pc;
   let fallthru_pcc_addr = fallthru_pc_addr;


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


   let funct5rs2 = inputs.decoded_instr.funct5rs2;
   let funct5rd = inputs.decoded_instr.funct5rd;
   let funct7  = inputs.decoded_instr.funct7;

   match {.cheri_op_sources,
          .cap_checks,
          .cheri_operation_select,
          .cheri_alu_control} = inputs.decoded_instr.cheri_info;
   let cheri_op1_source = cheri_op_sources.cheri_op1_source;
   let cheri_op2_source = cheri_op_sources.cheri_op2_source;

   let cs1_val = inputs.cap_rs1_val;
   let cs2_val = inputs.cap_rs2_val;

   let cheri_op1_val = cheri_op1_source == CHERI_OP_SOURCE_CS1 ? cs1_val
                     : cheri_op1_source == CHERI_OP_SOURCE_CS2 ? cs2_val
                     : cheri_op1_source == CHERI_OP_SOURCE_DDC ? inputs.ddc
                     : cheri_op1_source == CHERI_OP_SOURCE_PCC ? toCapPipeNoOffset (inputs.pcc)
                     :                                           cs1_val;

   let cheri_op2_val = cheri_op2_source == CHERI_OP_SOURCE_CS1 ? cs1_val
                     : cheri_op2_source == CHERI_OP_SOURCE_CS2 ? cs2_val
                     : cheri_op2_source == CHERI_OP_SOURCE_DDC ? inputs.ddc
                     : cheri_op2_source == CHERI_OP_SOURCE_PCC ? toCapPipeNoOffset (inputs.pcc)
                     :                                           cs2_val;

   let cheri_op1_base = cheri_op1_source == CHERI_OP_SOURCE_PCC ? getPCCBase (inputs.pcc)
                                                                : getBase (cheri_op1_val);
   let cheri_op1_top  = cheri_op1_source == CHERI_OP_SOURCE_PCC ? getPCCTop (inputs.pcc)
                                                                : getTop  (cheri_op1_val);
   let cheri_op1_offset = cheri_op1_source == CHERI_OP_SOURCE_PCC ? getPC (inputs.pcc)
                                                                  : getOffset (cheri_op1_val);
   let cheri_op1_addr   = cheri_op1_source == CHERI_OP_SOURCE_PCC ? getPCCAddr (inputs.pcc)
                                                                  : getAddr (cheri_op1_val);

   let cheri_op2_base = cheri_op2_source == CHERI_OP_SOURCE_PCC ? getPCCBase (inputs.pcc)
                                                                : getBase (cheri_op2_val);
   let cheri_op2_top  = cheri_op2_source == CHERI_OP_SOURCE_PCC ? getPCCTop (inputs.pcc)
                                                                : getTop  (cheri_op2_val);
   let cheri_op2_offset = cheri_op2_source == CHERI_OP_SOURCE_PCC ? getPC (inputs.pcc)
                                                                  : getOffset (cheri_op2_val);
   let cheri_op2_addr   = cheri_op1_source == CHERI_OP_SOURCE_PCC ? getPCCAddr (inputs.pcc)
                                                                  : getAddr (cheri_op2_val);

   let reserved_type = False;

   alu_outputs.mem_unsigned   = cheri_alu_control.alu_mem_unsigned;
   alu_outputs.check_inclusive = cheri_alu_control.alu_bounds_inclusive;
   CapPipe data = cheri_op2_val;
   alu_outputs.cap_val2 = data;
`endif

   let cf_info = CF_Info {cf_op       : ?,
                          from_PC     : pcc_addr,
                          taken       : ?,
                          fallthru_PC : fallthru_pc_addr,
                          taken_PC    : ?};

   if (cheri_alu_control.alu_illegal_instr) begin
      alu_outputs.trap = True;
      trap = True;
      alu_outputs.control = CONTROL_STRAIGHT;
   end


   if (inputs.decoded_instr.opcode == op_BRANCH) begin
   end

   else if (inputs.decoded_instr.opcode == op_JAL) begin
   end

   else if (inputs.decoded_instr.opcode == op_JALR) begin
   end

   else if (   (   (inputs.decoded_instr.opcode == op_OP_IMM)
		|| (inputs.decoded_instr.opcode == op_OP))
	    && (   (inputs.decoded_instr.funct3 == f3_SLLI)
		|| (inputs.decoded_instr.funct3 == f3_SRLI)
		|| (inputs.decoded_instr.funct3 == f3_SRAI))) begin
      if (funct3 == f3_SLLI) begin
         // SLLI
         shift_left = True;
      end else begin
         shift_left = False;
      end
      trap = (rv_version == RV32) && !shamt5_is_0;

`ifdef DELAY_STAGE1_TRAPS
      alu_outputs.trap = trap;
      alu_outputs.control = CONTROL_STRAIGHT;
`else
      alu_outputs.control = trap ? CONTROL_TRAP : CONTROL_STRAIGHT;
`endif
   end

   else if (   (inputs.decoded_instr.opcode == op_OP_IMM)
	    || (inputs.decoded_instr.opcode == op_OP)) begin
      if ((funct3 == f3_ADDI) && (!subtract)) begin
      end
      else if ((funct3 == f3_ADDI) && (subtract)) begin
      end
      else if (funct3 == f3_SLTI) begin
      end
      else if (funct3 == f3_SLTIU) begin
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
      if (funct3 == f3_ADDIW) begin
      end
      else if ((funct3 == f3_SLLIW) && shamt5_is_0) begin
         shift_left = True;
      end
      else if ((funct3 == f3_SRxIW) && shamt5_is_0) begin
         shift_left = False;
      end
      else begin
         trap = True;
      end
   end

   // Remaining op_OP_32 (excluding 'M' ops)
   else if (inputs.decoded_instr.opcode == op_OP_32) begin
      shamt = zeroExtend (shamt[4:0]);
      if (funct10 == f10_ADDW) begin
      end
      else if (funct10 == f10_SUBW) begin
      end
      else if (funct10 == f10_SLLW) begin
         shift_left = True;
      end
      else if (funct10 == f10_SRLW) begin
         shift_left = False;
      end
      else if (funct10 == f10_SRAW) begin
         shift_left = False;
      end
      else begin
         trap = True;
      end
   end
`endif
   // If we are in CHERI, we might need to do a setOffset for AUIPCC, so moved to fv_CHERI
   else if (inputs.decoded_instr.opcode == op_AUIPC) begin
   end
   else if (  inputs.decoded_instr.opcode == op_LOAD
           || inputs.decoded_instr.opcode == op_MISC_MEM && valueOf (XLEN) == 64 && funct3 == f3_LQ) begin
      //alu_outputs = fv_LD (inputs, Invalid);
      alu_outputs.op_stage2 = OP_Stage2_LD;
      alu_outputs.rd        = inputs.decoded_instr.rd;
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
`ifdef MERGE_IMMEDIATE
      IntXL s_imm_i = extend (unpack (inputs.decoded_instr.imm));
`else
      IntXL s_imm_i = extend (unpack (inputs.decoded_instr.imm12_I));
`endif
`ifdef ISA_F
      if (inputs.decoded_instr.opcode == op_LOAD_FP) begin
         trap = (fv_mstatus_fs (inputs.mstatus) != fs_xs_off);
      end
      alu_outputs.rd_in_fpr = (opcode == op_LOAD_FP);
`endif

`ifdef DELAY_STAGE1_TRAPS
      alu_outputs.trap           = trap;
      alu_outputs.control        = CONTROL_STRAIGHT;
`else
      alu_outputs.control        = (trap ? CONTROL_TRAP
                                         : CONTROL_STRAIGHT);
`endif

`ifdef ISA_CHERI
      if (valueOf (XLEN) == 32 && inputs.decoded_instr.funct3 == f3_LD) size = Valid (w_SIZE_D);
      is_load = True;
      width_code = fromMaybe ({0, funct3[1:0]}, size);
      Bool useDDC = getFlags (toCapPipeNoOffset (inputs.pcc))[0] == 1'b0;
`else
      addop1 = {1'b0, pack (s_rs1_val), 1'b0};
      addop2 = {1'b0, pack (  s_imm_i), 1'b0};
`endif

   end

   else if (inputs.decoded_instr.opcode == op_STORE) begin
`ifdef MERGE_IMMEDIATE
      IntXL s_imm_s = extend (unpack (inputs.decoded_instr.imm));
`else
      IntXL s_imm_s = extend (unpack (inputs.decoded_instr.imm12_S));
`endif
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
`ifdef DELAY_STAGE1_TRAPS
      alu_outputs.trap           = trap;
      alu_outputs.control        = CONTROL_STRAIGHT;
`else
      alu_outputs.control = trap ? CONTROL_TRAP : CONTROL_STRAIGHT;
`endif

`ifdef ISA_CHERI
      is_store = True;
      width_code = funct3;

`else
      addop1 = {1'b0, pack (s_rs1_val), 1'b0};
      addop2 = {1'b0, pack (  s_imm_s), 1'b0};
`endif

   end


`ifdef ISA_CHERI
   else if (inputs.decoded_instr.opcode == op_cap_Manip) begin
      alu_outputs.rd = inputs.decoded_instr.rd;
      alu_outputs.op_stage2 = OP_Stage2_ALU;
      case (funct3)
         f3_cap_CIncOffsetImmediate: begin end
         f3_cap_CSetBoundsImmediate: begin end
         f3_cap_ThreeOp: begin
            case (funct7)
               f7_cap_CSpecialRW: begin
                  if (inputs.decoded_instr.rs2 == scr_addr_PCC && inputs.decoded_instr.rs1 == 0) begin
                  end else if (inputs.decoded_instr.rs2 == scr_addr_DDC && inputs.decoded_instr.rs1 == 0) begin
                  end else begin
                     alu_outputs.control   = CONTROL_SCR_W;
                  end
               end
               f7_cap_CSetBounds: begin end
               f7_cap_CSetBoundsExact: begin end
               f7_cap_CSetOffset: begin end
               f7_cap_CSetAddr: begin end
               f7_cap_CIncOffset: begin end
               f7_cap_CSeal: begin end
               f7_cap_CCSeal: begin end
               f7_cap_TwoSrc: begin
                  case (inputs.decoded_instr.rd)
                     rd_cap_CCall: begin end
                     default: begin end
                  endcase // inputs.decoded_instr.rd
               end
               f7_cap_CUnseal: begin end
               f7_cap_CTestSubset: begin end
               f7_cap_CCopyType: begin end
               f7_cap_CAndPerm: begin end
               f7_cap_CSetFlags: begin end
               f7_cap_CToPtr: begin end
               f7_cap_CFromPtr: begin end
               f7_cap_CSub: begin end
               f7_cap_CBuildCap: begin end
               f7_cap_Loads: begin end
               f7_cap_Stores: begin end
               f7_cap_TwoOp: begin
                  case (funct5rs2)
                     f5rs2_cap_CGetLen: begin end
                     f5rs2_cap_CGetBase: begin end
                     f5rs2_cap_CGetTag: begin end
                     f5rs2_cap_CGetSealed: begin end
                     f5rs2_cap_CRRL: begin end
                     f5rs2_cap_CRAM: begin end
                     f5rs2_cap_CMove: begin end
                     f5rs2_cap_CClearTag: begin end
                     f5rs2_cap_CGetAddr: begin end
                     f5rs2_cap_CSealEntry: begin end
                     f5rs2_cap_CGetOffset: begin end
                     f5rs2_cap_CGetFlags: begin end
                     f5rs2_cap_CGetPerm: begin end
                     f5rs2_cap_CJALR: begin end
                     f5rs2_cap_CGetType: begin end
                     default: begin end
                  endcase // funct5rs2
               end
               default: begin end
            endcase // funct7
         end
      default: begin end
      endcase // funct3
   end
`endif // ISA_CHERI

   match {.op1_source,
          .op2_source,
          .cmpop1_source,
          .cmpop2_source} = inputs.decoded_instr.operands;

   case (op1_source)
      OP1_PC_ADDR: begin
         addop1 = {1'b0, pcc_addr, 1'b0};
      end
      OP1_RS1: begin
         addop1 = {1'b0, inputs.rs1_val, 1'b0};
      end
      OP1_RS1_S: begin
         addop1 = {signExtend (inputs.rs1_val), 1'b0};
      end
      OP1_RS1_NEG: begin
         addop1 = {1'b0, inputs.rs1_val, 1'b1};
      end
      OP1_RS1_REV: begin
         addop1 = {1'b0, reverseBits (inputs.rs1_val), 1'b0};
      end
`ifdef RV64
      OP1_RS1_B32: begin
         addop1 = {1'b0, zeroExtend (inputs.rs1_val[31:0]), 1'b0};
      end
      OP1_RS1_B32_S: begin
         if (shamt == 0) begin
            addop1 = {signExtend (inputs.rs1_val[31:0]), 1'b0};
         end else begin
            addop1 = {signExtend (inputs.rs1_val[31:0]), 1'b0};
         end
      end
      OP1_RS1_B32_REV: begin
         addop1 = {1'b0, reverseBits (zeroExtend (inputs.rs1_val[31:0])), 1'b0};
      end
      OP1_RS1_B32_NEG: begin
         addop1 = {1'b0, zeroExtend (inputs.rs1_val[31:0]), 1'b1};
      end
`endif
      OP1_RS1_MASKED: begin
         addop1 = {1'b0, (inputs.rs1_val & signExtend (2'b10)), 1'b0};
      end
      default: begin
         addop1 = 1;
      end
   endcase

   case (op2_source)
      OP2_IMM: begin
         addop2 = {1'b0, zeroExtend (inputs.decoded_instr.imm[11:0]), 1'b0};
      end
      OP2_IMM_S: begin
         addop2 = {1'b0, signExtend (inputs.decoded_instr.imm), 1'b0};
      end
      OP2_IMM_NEG: begin
         addop2 = {1'b0, ~(signExtend (inputs.decoded_instr.imm)), 1'b1};
      end
      OP2_IMM_HIGH: begin
         addop2 = {1'b0, signExtend (inputs.decoded_instr.imm[19:0]), 12'b0, 1'b0};
      end
      OP2_RS2: begin
         addop2 = {1'b0, inputs.rs2_val, 1'b1};
      end
      OP2_RS2_NEG: begin
         addop2 = {1'b0, ~(inputs.rs2_val), 1'b1};
      end
      OP2_TYPE_UNSEALED: begin
         addop2 = {1'b0, zeroExtend (otype_unsealed_ext), 1'b0};
      end
      OP2_TYPE_SENTRY: begin
         addop2 = {1'b0, zeroExtend (otype_sentry_ext), 1'b0};
      end
      OP2_KIND: begin
         let cap_kind = ?;
         case (getKind(cheri_op2_val)) matches
            tagged UNSEALED: begin
               cap_kind = otype_unsealed_ext;
               reserved_type = True;
            end
            tagged SENTRY: begin
               cap_kind = otype_sentry_ext;
               reserved_type = True;
            end
            tagged RES0: begin
               cap_kind = otype_res0_ext;
               reserved_type = True;
            end
            tagged RES1: begin
               cap_kind = otype_res1_ext;
               reserved_type = True;
            end
            tagged SEALED_WITH_TYPE .otype: begin
               cap_kind = zeroExtend(otype);
            end
         endcase
         addop2 = {1'b0, zeroExtend (cap_kind), 1'b0};
      end
`ifdef RV64
      OP2_RS2_B32: begin
         addop2 = {1'b0, zeroExtend (inputs.rs2_val[31:0]), 1'b0};
      end
      OP2_RS2_B32_NEG: begin
         addop2 = {1'b0, ~(signExtend (inputs.rs2_val[31:0])), 1'b1};
      end
`endif
      OP2_CHERI_OP2_ADDR: begin
         addop2 = {1'b0, getAddr (cheri_op2_val), 1'b0};
      end
      OP2_ZERO: begin
         addop2 = 0;
      end
      OP2_TWO: begin
         addop2 = {1'b0, zeroExtend (2'h2), 1'b0};
      end
      default: begin
         addop2 = 1;
      end
   endcase

   case (cmpop1_source)
      CMPOP1_RS1: begin
         cmpop1 = zeroExtend (inputs.rs1_val);
      end
      CMPOP1_RS1_S: begin
         cmpop1 = signExtend (inputs.rs1_val);
      end
   endcase

   case (cmpop2_source)
      CMPOP2_RS2: begin
         cmpop2 = zeroExtend (inputs.rs2_val);
      end
      CMPOP2_RS2_S: begin
         cmpop2 = signExtend (inputs.rs2_val);
      end
      CMPOP2_IMM: begin
         cmpop2 = {1'b0, signExtend (inputs.decoded_instr.imm)};
      end
      CMPOP2_IMM_S: begin
         cmpop2 = signExtend (inputs.decoded_instr.imm[11:0]);
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
`ifdef ISA_CHERI
`ifdef ISA_C
   misaligned_target = cheri_op1_base[0] != 1'b0;
`else
   misaligned_target = ((pack (sum))[1] == 1'b1) || (cheri_op1_base[1:0] != 2'b0);
   //misaligned_target = addop1[2] == 1'b1;
`endif
`endif

   if (cheri_alu_control.alu_check_misaligned && misaligned_target) begin
`ifdef DELAY_STAGE1_TRAPS
      alu_outputs.trap = True;
      alu_outputs.control = CONTROL_STRAIGHT;
`else
      alu_outputs.control = CONTROL_TRAP;
`endif
      alu_outputs.exc_code = exc_code_INSTR_ADDR_MISALIGNED;
   end

   //match {.sum, .misaligned_target} <- adder_wrapper.func (addop1, addop2);

   Int #(TAdd #(1, XLEN)) shiftop_final = unpack (addop1[valueof (XLEN)+1:1]);
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


   CapPipe pcc_to_update_to = ?;
   Bool update_pcc = False;
   case (cheri_operation_select)
      CHERI_NONE: begin
         if (cheri_op1_source == CHERI_OP_SOURCE_PCC) begin
            alu_outputs.cap_val1 = toCapPipe (inputs.pcc);
         end else begin
            alu_outputs.cap_val1 = cheri_op1_val;
         end
      end
      CHERI_CLEAR_TAG: begin
         alu_outputs.cap_val1 = setValidCap (cheri_op1_val, False);
      end
      CHERI_SET_OFFSET: begin
         let res = modifyOffset (cheri_op1_val, addop2[valueof (XLEN):1], cheri_alu_control.alu_offset_inc_not_set);
         if (cheri_alu_control.alu_seal_entry) begin
            res.value = setKind (res.value, SENTRY);
            alu_outputs.cap_val1 = res.value;
         end
         if (cheri_alu_control.alu_offset_conditional) begin
            if (getAddr (cheri_op2_val) == 0) begin
               res.value = nullCap;
            end else begin
               cap_checks.check_op1_tagged = True;
               cap_checks.check_op1_unsealed = True;
            end
         end
         alu_outputs.cap_val1 = res.value;
      end
      CHERI_CJALR: begin
         // note: cheri_op1_val is PCC, cheri_op2_val is CS1
         Addr next_pc = cheri_op2_addr;
         let maskedTarget = maskAddr (cheri_op2_val, signExtend (2'b10));
         next_pc[0] = 1'b0;
         alu_outputs.control = CONTROL_CAPBRANCH;
         alu_outputs.addr = next_pc;
         //alu_outputs.pcc = fromCapPipe (setKind (maskedTarget, UNSEALED));
         update_pcc = True;
         pcc_to_update_to = setKind (maskedTarget, UNSEALED);
         //alu_outputs.cap_val1 = (modifyOffset (cheri_op1_val, addop2[valueof (XLEN):1], False)).value;
         // TODO modifyOffset appears twice in ALU. maybe there is a way of
         // having only 1?
         alu_outputs.cap_val1 = (modifyOffset (cheri_op1_val, fallthru_pc_addr, False)).value;
         alu_outputs.cap_val1 = setKind (alu_outputs.cap_val1, SENTRY);
         width_code = 2;

         // we use cheri_op2 as our next pcc, so we need to check if it is misaligned
         // the other check for misaligned-ness is done on cheri_op1
`ifdef ISA_C
         misaligned_target = cheri_op2_base[0] != 1'b0;
`else
         misaligned_target = ((pack (sum))[1] == 1'b1) || (cheri_op2_base[1:0] != 2'b0);
`endif

         if (misaligned_target) begin
`ifdef DELAY_STAGE1_TRAPS
            alu_outputs.trap = True;
            alu_outputs.control = CONTROL_STRAIGHT;
`else
            alu_outputs.control = CONTROL_TRAP;
`endif
            alu_outputs.exc_code = exc_code_INSTR_ADDR_MISALIGNED;
         end
      end
      CHERI_SET_BOUNDS: begin
         // these are the only two sources of bounds
         // normally the new bounds would be in addop2 but this causes a long path
         let new_bounds = op2_source == OP2_RS2 ? rs2_val : zeroExtend (inputs.decoded_instr.imm[11:0]);
         let res = setBounds (cheri_op1_val, new_bounds);
         alu_outputs.cap_val1 = res.value;
         alu_outputs.check_exact_success = res.exact;
      end
      CHERI_SET_ADDR: begin
         let res = setAddr (cheri_op1_val, addop2[valueof (XLEN):1]);
         if (res.exact) begin
            alu_outputs.cap_val1 = res.value;
         end else begin
            alu_outputs.cap_val1 = setValidCap (res.value, False);
         end
      end
      CHERI_COPY_TYPE: begin
         let res_val = ?;
         if (reserved_type) begin
            res_val = nullWithAddr (addop2[valueof (XLEN):1]);
         end else begin
            let res = setAddr (cheri_op1_val, addop2[valueof (XLEN):1]);
            res_val = res.value;
         end
         alu_outputs.cap_val1 = res_val;
      end
      CHERI_SET_KIND: begin
         Bit #(XLEN) tmp_val = addop2[valueOf (XLEN):1];
         let newtype = truncate (tmp_val);
         let newtype_wrapped = ?;
         case (newtype)
            otype_unsealed_ext:  newtype_wrapped = UNSEALED;
            otype_sentry_ext:    newtype_wrapped = SENTRY;
            otype_res0_ext:      newtype_wrapped = RES0;
            otype_res1_ext:      newtype_wrapped = RES1;
            default:             newtype_wrapped = SEALED_WITH_TYPE (newtype);
         endcase
         alu_outputs.cap_val1 = setKind (cheri_op1_val, SEALED_WITH_TYPE (truncate (tmp_val)));
      end
      CHERI_SET_KIND_CONDITIONAL: begin
         if (  !isValidCap (cheri_op2_val)
            || (getAddr(cheri_op2_val) == otype_unsealed_ext)
            || (getKind(cheri_op1_val) != UNSEALED)
            ) begin
            alu_outputs.cap_val1 = cheri_op1_val;
         end else begin
            cap_checks.check_enable = True;
            cap_checks.check_op1_unsealed = True;
            cap_checks.check_op2_unsealed = True;
            cap_checks.check_op2_addr_valid_type = True;
            cap_checks.check_op2_permit_seal = True;
            Bit #(XLEN) tmp_val = addop2[valueOf (XLEN):1];
            alu_outputs.cap_val1 = setKind (cheri_op1_val, SEALED_WITH_TYPE (truncate (tmp_val)));
         end
      end
      CHERI_SET_KIND_AND_VALID: begin
         let res = setValidCap (cheri_op2_val, True);
         res = setKind (res, getKind (cheri_op2_val) == SENTRY ? SENTRY : UNSEALED);
         alu_outputs.cap_val1 = res;
      end
      CHERI_AND_PERMS: begin
         Bit #(XLEN) tmp_val = addop2[valueOf (XLEN):1];
         alu_outputs.cap_val1 = setPerms (cheri_op1_val, pack (getPerms (cheri_op1_val)) & truncate (tmp_val));
      end
      CHERI_SET_FLAG: begin
         Bit #(XLEN) tmp_val = addop2[valueOf (XLEN):1];
         alu_outputs.cap_val1 = setFlags (cheri_op1_val, truncate (tmp_val));
      end
      CHERI_GET_ADDR: begin
         alu_outputs.val1 = getAddr (cheri_op1_val);
      end
      CHERI_GET_LENGTH: begin
         alu_outputs.val1 = truncate (getLength (cheri_op1_val));
      end
      CHERI_GET_BASE: begin
         alu_outputs.val1 = cheri_op1_base;
      end
      CHERI_GET_TAG: begin
         alu_outputs.val1 = zeroExtend (pack (isValidCap (cheri_op1_val)));
      end
      CHERI_GET_KIND: begin
         case (getKind (cheri_op1_val)) matches
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
      CHERI_GET_SEALED: begin
         alu_outputs.val1 = zeroExtend(pack(getKind(cheri_op1_val) != UNSEALED));
      end
      CHERI_GET_OFFSET: begin
         alu_outputs.val1 = getAddr (cheri_op1_val) - cheri_op2_base;
      end
      CHERI_GET_FLAGS: begin
         alu_outputs.val1 = zeroExtend (getFlags (cheri_op1_val));
      end
      CHERI_GET_PERMS: begin
         alu_outputs.val1 = zeroExtend (getPerms (cheri_op1_val));
      end
      CHERI_GET_PRECISION: begin
         CapReg nullCapReg = nullCap;
         let result = getRepresentableAlignmentMask(nullCapReg, inputs.rs1_val);
         if (alu_outputs.internal_crrl_not_cram) begin
            result = (inputs.rs1_val + ~result) & result;
         end
         alu_outputs.val1 = result;
      end
      CHERI_TEST_CONDITIONAL: begin
         if (  isValidCap (cheri_op1_val) == isValidCap (cheri_op2_val)
            && (getPerms (cheri_op1_val) & getPerms (cheri_op2_val)) == getPerms (cheri_op2_val)
            ) begin
            alu_outputs.op_stage2 = OP_Stage2_TestSubset;
         end else begin
            alu_outputs.val1 = 0;
         end
      end
      CHERI_C_TO_PTR: begin
         if (isValidCap (cheri_op1_val)) begin
            alu_outputs.val1 = getAddr (cheri_op1_val) - cheri_op2_base;
         end else begin
            alu_outputs.val1 = 0;
         end
      end
      CHERI_LOAD_CAP: begin
         alu_outputs.val1 = zeroExtend ({f5_AMO_LR, 2'b0});
         alu_outputs.val2 = ?;
      end
      CHERI_STORE_CAP: begin
         alu_outputs.val1 = zeroExtend ({f5_AMO_SC, 2'b0});
         alu_outputs.cap_val2 = data;
         alu_outputs.val2 = getAddr (data);
      end
      CHERI_CCALL: begin
         alu_outputs.cap_val1 = setKind (cheri_op2_val, UNSEALED);
         let unsealed_pcc = setKind (cheri_op1_val, UNSEALED);
         //alu_outputs.pcc = fromCapPipe (maskAddr (unsealed_pcc, signExtend (2'b10)));
         update_pcc = True;
         pcc_to_update_to = maskAddr (unsealed_pcc, signExtend (2'b10));
         alu_outputs.control = CONTROL_CAPBRANCH;
      end
      CHERI_ALU_SUM_OUTPUT: begin
         alu_outputs.val1 = pack (sum);
      end
   endcase

   if (update_pcc) begin
      alu_outputs.pcc = fromCapPipe (pcc_to_update_to);
   end

   if (cheri_alu_control.alu_ccall_rd) begin
      alu_outputs.rd = cCallRD;
   end


`ifdef ISA_CHERI

   alu_outputs.check_enable = cap_checks.check_enable;
   alu_outputs.internal_bounds_exact = cheri_alu_control.alu_bounds_exact;
   alu_outputs.check_exact_enable = cheri_alu_control.alu_bounds_exact;
   if (cheri_op_sources.cheri_authority_source == cheri_op_sources.cheri_op1_source) begin
      authority = cheri_op1_val;
      authority_base = cheri_op1_base;
      authority_top  = cheri_op1_top;
      authorityIdx = cap_checks.cheri_op1_id;
   end else begin
      authority = cheri_op2_val;
      authority_base = cheri_op2_base;
      authority_top  = cheri_op2_top;
      authorityIdx = cap_checks.cheri_op2_id;
   end

   alu_outputs.val1_cap_not_int = cheri_alu_control.alu_val1_cap_not_int;
   alu_outputs.val2_cap_not_int = cheri_alu_control.alu_val2_cap_not_int;

   width_code = cheri_alu_control.alu_mem_width_code;
   case (cap_checks.cheri_addr_check_source_high)
      CHERI_ADDR_CHECK_SOURCE_OP1: begin
         check_address_high = zeroExtend (getAddr (cheri_op1_val));
      end
      CHERI_ADDR_CHECK_SOURCE_OP1_ADDR: begin
         check_address_high = zeroExtend (getAddr (cheri_op1_val));
      end
      CHERI_ADDR_CHECK_SOURCE_OP1_ADDR_MASKED: begin
         check_address_high = {1'b0, truncateLSB (getAddr (cheri_op1_val)), 1'b0};
      end
      CHERI_ADDR_CHECK_SOURCE_OP2_BOUNDS: begin
         check_address_high = cheri_op2_top;
      end
      CHERI_ADDR_CHECK_SOURCE_OP2_ADDR: begin
         check_address_high = zeroExtend (getAddr (cheri_op2_val));
      end
      CHERI_ADDR_CHECK_SOURCE_OP2_ADDR_MASKED: begin
         check_address_high = {1'b0, truncateLSB (getAddr (cheri_op2_val)), 1'b0};
      end
      CHERI_ADDR_CHECK_SOURCE_OP2_KIND: begin
         let res = getKind (cheri_op2_val);
         let packed_type = ?;
         case (res) matches
            tagged UNSEALED: begin
               packed_type = zeroExtend (otype_unsealed_ext);
            end
            tagged SENTRY: begin
               packed_type = zeroExtend (otype_sentry_ext);
            end
            tagged RES0: begin
               packed_type = zeroExtend (otype_res0_ext);
            end
            tagged RES1: begin
               packed_type = zeroExtend (otype_res1_ext);
            end
            tagged SEALED_WITH_TYPE .otype: begin
               packed_type = zeroExtend (otype);
            end
         endcase
         check_address_high = packed_type;
      end
      CHERI_ADDR_CHECK_SOURCE_SUM: begin
         check_address_high = sum_tmp[xlen+1:1];
      end
      CHERI_ADDR_CHECK_SOURCE_SUM_WIDTH: begin
         check_address_high = {1'b0, pack (sum) + (1 << width_code)};
      end
   endcase


   case (cap_checks.cheri_addr_check_source_low)
      CHERI_ADDR_CHECK_SOURCE_OP1: begin
         check_address_low = getAddr (cheri_op1_val);
      end
      CHERI_ADDR_CHECK_SOURCE_OP1_ADDR: begin
         check_address_low = getAddr (cheri_op1_val);
      end
      CHERI_ADDR_CHECK_SOURCE_OP1_ADDR_MASKED: begin
         check_address_low = {truncateLSB (getAddr (cheri_op1_val)), 1'b0};
      end
      CHERI_ADDR_CHECK_SOURCE_OP2_BOUNDS: begin
         check_address_low = cheri_op2_base;
      end
      CHERI_ADDR_CHECK_SOURCE_OP2_ADDR: begin
         check_address_low = getAddr (cheri_op2_val);
      end
      CHERI_ADDR_CHECK_SOURCE_OP2_ADDR_MASKED: begin
         check_address_low = {truncateLSB (getAddr (cheri_op2_val)), 1'b0};
      end
      CHERI_ADDR_CHECK_SOURCE_OP2_KIND: begin
         let res = getKind (cheri_op2_val);
         let packed_type = ?;
         case (res) matches
            tagged UNSEALED: begin
               packed_type = zeroExtend (otype_unsealed_ext);
            end
            tagged SENTRY: begin
               packed_type = zeroExtend (otype_sentry_ext);
            end
            tagged RES0: begin
               packed_type = zeroExtend (otype_res0_ext);
            end
            tagged RES1: begin
               packed_type = zeroExtend (otype_res1_ext);
            end
            tagged SEALED_WITH_TYPE .otype: begin
               packed_type = zeroExtend (otype);
            end
         endcase
         check_address_low = packed_type;
      end
      CHERI_ADDR_CHECK_SOURCE_SUM: begin
         check_address_low = pack (sum);
      end
      CHERI_ADDR_CHECK_SOURCE_SUM_WIDTH: begin
         check_address_low = pack (sum);
      end
   endcase

   alu_outputs.check_authority = authority;
   alu_outputs.check_authority_idx = authorityIdx;
   alu_outputs.check_address_low = check_address_low;
   alu_outputs.check_address_high = check_address_high;
   alu_outputs.mem_width_code = width_code;

   alu_outputs.authority_base = authority_base;
   alu_outputs.authority_top = authority_top;

   if (width_code == w_SIZE_CAP && is_load && getHardPerms(authority).permitLoadCap) begin
      alu_outputs.mem_allow_cap = True;
   end

    // tag checks
    if      (cap_checks.check_op1_tagged             && !isValidCap(cheri_op1_val))
        alu_outputs = fv_CHERI_exc(alu_outputs, cap_checks.cheri_op1_id, exc_code_CHERI_Tag);

    else if (cap_checks.check_op2_tagged             && !isValidCap(cheri_op2_val))
        alu_outputs = fv_CHERI_exc(alu_outputs, cap_checks.cheri_op2_id, exc_code_CHERI_Tag);

    else if (cap_checks.check_op2_derivable          && !isDerivable (cheri_op2_val))
        alu_outputs = fv_CHERI_exc(alu_outputs, cap_checks.cheri_op2_id, exc_code_CHERI_Length);

    // seal checks
    else if (cap_checks.check_op1_sealed_with_type   && (getKind(cheri_op1_val) matches tagged SEALED_WITH_TYPE ._ ? False : True))
        alu_outputs = fv_CHERI_exc(alu_outputs, cap_checks.cheri_op1_id, exc_code_CHERI_Seal);

    else if (cap_checks.check_op2_sealed_with_type   && (getKind(cheri_op2_val) matches tagged SEALED_WITH_TYPE ._ ? False : True))
        alu_outputs = fv_CHERI_exc(alu_outputs, cap_checks.cheri_op2_id, exc_code_CHERI_Seal);
    // unsealed checks
    else if (cap_checks.check_op1_unsealed           && isValidCap(cheri_op1_val) && getKind(cheri_op1_val) != UNSEALED)
        alu_outputs = fv_CHERI_exc(alu_outputs, cap_checks.cheri_op1_id, exc_code_CHERI_Seal);

    else if (cap_checks.check_op1_unsealed_or_sentry && isValidCap(cheri_op1_val) && getKind(cheri_op1_val) != UNSEALED && getKind(cheri_op1_val) != SENTRY)
        alu_outputs = fv_CHERI_exc(alu_outputs, cap_checks.cheri_op1_id, exc_code_CHERI_Seal);

    else if (cap_checks.check_op2_unsealed           && isValidCap(cheri_op2_val) && getKind(cheri_op2_val) != UNSEALED)
        alu_outputs = fv_CHERI_exc(alu_outputs, cap_checks.cheri_op2_id, exc_code_CHERI_Seal);

    else if (cap_checks.check_op2_unsealed_or_sentry && isValidCap(cheri_op2_val) && getKind(cheri_op2_val) != UNSEALED && getKind(cheri_op2_val) != SENTRY)
        alu_outputs = fv_CHERI_exc(alu_outputs, cap_checks.cheri_op2_id, exc_code_CHERI_Seal);

    // matching types
    else if (cap_checks.check_op1_op2_types_match    && getKind(cheri_op1_val).SEALED_WITH_TYPE != getKind(cheri_op2_val).SEALED_WITH_TYPE) // Already checked SEALED_WITH_TYPE
        alu_outputs = fv_CHERI_exc(alu_outputs, cap_checks.cheri_op1_id, exc_code_CHERI_Type);

    // permit ccall
    else if (cap_checks.check_op1_permit_ccall       && !getHardPerms(cheri_op1_val).permitCCall)
        alu_outputs = fv_CHERI_exc(alu_outputs, cap_checks.cheri_op1_id, exc_code_CHERI_CCallPerm);

    else if (cap_checks.check_op2_permit_ccall       && !getHardPerms(cheri_op2_val).permitCCall)
        alu_outputs = fv_CHERI_exc(alu_outputs, cap_checks.cheri_op2_id, exc_code_CHERI_CCallPerm);

    // permit execute
    else if (cap_checks.check_op1_permit_x           && !getHardPerms(cheri_op1_val).permitExecute)
        alu_outputs = fv_CHERI_exc(alu_outputs, cap_checks.cheri_op1_id, exc_code_CHERI_XPerm);

    else if (cap_checks.check_op2_permit_x           && !getHardPerms(cheri_op2_val).permitExecute)
        alu_outputs = fv_CHERI_exc(alu_outputs, cap_checks.cheri_op2_id, exc_code_CHERI_XPerm);

    // no permite execute
    else if (cap_checks.check_op2_no_permit_x        && getHardPerms(cheri_op2_val).permitExecute)
        alu_outputs = fv_CHERI_exc(alu_outputs, cap_checks.cheri_op2_id, exc_code_CHERI_XPerm);

    // permit unseal
    else if (cap_checks.check_op2_permit_unseal      && !getHardPerms(cheri_op2_val).permitUnseal)
        alu_outputs = fv_CHERI_exc(alu_outputs, cap_checks.cheri_op2_id, exc_code_CHERI_UnsealPerm);

    // permit seal
    else if (cap_checks.check_op2_permit_seal        && !getHardPerms(cheri_op2_val).permitSeal)
        alu_outputs = fv_CHERI_exc(alu_outputs, cap_checks.cheri_op2_id, exc_code_CHERI_SealPerm);

    // points to cs1 type (???)
    else if (cap_checks.check_op2_points_to_op1_type && getAddr(cheri_op2_val) != zeroExtend(getKind(cheri_op1_val).SEALED_WITH_TYPE)) // Already checked SEALED_WITH_TYPE
        alu_outputs = fv_CHERI_exc(alu_outputs, cap_checks.cheri_op2_id, exc_code_CHERI_Type);

    // valid type
    else if (cap_checks.check_op2_addr_valid_type    && !validAsType(cheri_op2_val, truncate(getAddr(cheri_op2_val))))
        alu_outputs = fv_CHERI_exc(alu_outputs, cap_checks.cheri_op2_id, exc_code_CHERI_Length);

    // perm subset checks
    else if (cap_checks.check_op2_perm_subset_op1    && (getPerms(cheri_op1_val) & getPerms(cheri_op2_val)) != getPerms(cheri_op2_val))
        alu_outputs = fv_CHERI_exc(alu_outputs, cap_checks.cheri_op2_id, exc_code_CHERI_Software);

    // TODO check ordering on these
    // permit loads
    else if (cap_checks.check_op1_permit_load && !getHardPerms(cheri_op1_val).permitLoad)
        alu_outputs = fv_CHERI_exc(alu_outputs, cap_checks.cheri_op1_id, exc_code_CHERI_RPerm);

    else if (cap_checks.check_op2_permit_load && !getHardPerms(cheri_op2_val).permitLoad)
        alu_outputs = fv_CHERI_exc(alu_outputs, cap_checks.cheri_op2_id, exc_code_CHERI_RPerm);

    // permit load cap
    else if (cap_checks.check_op1_permit_load_cap && getHardPerms(cheri_op1_val).permitLoadCap)
        alu_outputs.mem_allow_cap = True;

    else if (cap_checks.check_op2_permit_load_cap && getHardPerms(cheri_op2_val).permitLoadCap)
        alu_outputs.mem_allow_cap = True;

    // permit stores
    else if (cap_checks.check_op1_permit_store && !getHardPerms(cheri_op1_val).permitStore)
        alu_outputs = fv_CHERI_exc(alu_outputs, cap_checks.cheri_op1_id, exc_code_CHERI_WPerm);

    else if (cap_checks.check_op2_permit_store && !getHardPerms(cheri_op2_val).permitStore)
        alu_outputs = fv_CHERI_exc(alu_outputs, cap_checks.cheri_op2_id, exc_code_CHERI_WPerm);

    // permit global cap stores
    else if (cap_checks.check_op1_permit_store && isValidCap(data) && !getHardPerms(cheri_op1_val).permitStoreCap)
        alu_outputs = fv_CHERI_exc(alu_outputs, cap_checks.cheri_op1_id, exc_code_CHERI_SCPerm);

    else if (cap_checks.check_op2_permit_store && isValidCap(data) && !getHardPerms(cheri_op2_val).permitStoreCap)
        alu_outputs = fv_CHERI_exc(alu_outputs, cap_checks.cheri_op2_id, exc_code_CHERI_SCPerm);

    // permit local cap stores
    else if (cap_checks.check_op1_permit_store && isValidCap(data) && !getHardPerms(cheri_op1_val).global && !getHardPerms(cheri_op1_val).permitStoreLocalCap)
        alu_outputs = fv_CHERI_exc(alu_outputs, cap_checks.cheri_op1_id, exc_code_CHERI_SCLocalPerm);

    else if (cap_checks.check_op2_permit_store && isValidCap(data) && !getHardPerms(cheri_op2_val).global && !getHardPerms(cheri_op2_val).permitStoreLocalCap)
        alu_outputs = fv_CHERI_exc(alu_outputs, cap_checks.cheri_op2_id, exc_code_CHERI_SCLocalPerm);

    
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
                         fallthru_PC : fallthru_pc_addr,
                         taken_PC    : branch_target };
`else
      cf_info = CF_Info {cf_op       : CF_BR,
                         from_PC     : inputs.pc,
                         taken       : branch_taken,
                         fallthru_PC : fallthru_pc,
                         taken_PC    : branch_target };
`endif
      let next_pc = branch_taken ? branch_target : fallthru_pc_addr;
`ifdef DELAY_STAGE1_TRAPS
      alu_outputs.trap = trap;
      alu_outputs.control = branch_taken ? CONTROL_BRANCH : CONTROL_STRAIGHT;
`else
      alu_outputs.control = trap ? CONTROL_TRAP : (branch_taken ? CONTROL_BRANCH : CONTROL_STRAIGHT);
`endif
      alu_outputs.exc_code = exc_code;
      alu_outputs.op_stage2 = OP_Stage2_ALU;
      alu_outputs.rd = 0;
`ifdef RVFI
      alu_outputs.val1 = 0;
`endif
      alu_outputs.addr = next_pc;
      alu_outputs.val2 = extend (branch_target);

`ifdef ISA_CHERI
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
      Addr jump_target = pack (sum);

`ifdef ISA_CHERI
      cf_info = CF_Info {cf_op       : CF_JAL,
                         from_PC     : pcc_addr,
                         taken       : True,
                         fallthru_PC : fallthru_pc_addr,
                         taken_PC    : jump_target};
`else
      cf_info = CF_Info {cf_op       : CF_JAL,
                         from_PC     : inputs.pc,
                         taken       : True,
                         fallthru_PC : fallthru_pc,
                         taken_PC    : jump_target};
`endif
`ifdef DELAY_STAGE1_TRAPS
      alu_outputs.trap = misaligned_target;
      alu_outputs.control = CONTROL_BRANCH;
`else
      alu_outputs.control = misaligned_target ? CONTROL_TRAP : CONTROL_BRANCH;
`endif
      alu_outputs.exc_code = exc_code_INSTR_ADDR_MISALIGNED;
      alu_outputs.op_stage2 = OP_Stage2_ALU;
      alu_outputs.rd = inputs.decoded_instr.rd;
      alu_outputs.addr = jump_target;
      alu_outputs.val1 = extend (fallthru_pc_pc);
      alu_outputs.cf_info = cf_info;

`ifdef ISA_CHERI
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
      Addr jump_target = pack (sum);
      jump_target[0] = 1'b0;

`ifdef ISA_CHERI
      cf_info = CF_Info {cf_op       : CF_JALR,
                         from_PC     : pcc_addr,
                         taken       : True,
                         fallthru_PC : fallthru_pc_addr,
                         taken_PC    : jump_target};
`else
      cf_info = CF_Info {cf_op       : CF_JALR,
                         from_PC     : inputs.pc,
                         taken       : True,
                         fallthru_PC : fallthru_pc,
                         taken_PC    : jump_target};
`endif
`ifdef DELAY_STAGE1_TRAPS
      alu_outputs.trap = misaligned_target;
      alu_outputs.control = CONTROL_BRANCH;
`else
      alu_outputs.control = misaligned_target ? CONTROL_TRAP : CONTROL_BRANCH;
`endif
      alu_outputs.exc_code = exc_code_INSTR_ADDR_MISALIGNED;
      alu_outputs.op_stage2 = OP_Stage2_ALU;
      alu_outputs.rd = inputs.decoded_instr.rd;
      alu_outputs.addr = jump_target;
      alu_outputs.val1 = extend (fallthru_pc_pc);
      alu_outputs.cf_info = cf_info;

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
      let rd_val = shift_res;

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
      let rd_val = ?;
      IntXL s_rs2_val_local = s_rs2_val;
      WordXL rs2_val_local  = rs2_val;
      if (inputs.decoded_instr.opcode == op_OP_IMM) begin
`ifdef MERGE_IMMEDIATE
         s_rs2_val_local = extend (unpack (inputs.decoded_instr.imm));
`else
         s_rs2_val_local = extend (unpack (inputs.decoded_instr.imm12_I));
`endif
         rs2_val_local   = pack (s_rs2_val_local);
      end

      if      ((funct3 == f3_ADDI) && (!subtract))  rd_val = pack (sum);
      else if ((funct3 == f3_ADDI) && ( subtract))  rd_val = pack (sum);
      else if ( funct3 == f3_SLTI)                  rd_val = (cmp_less_than ? 1 : 0);
      else if ( funct3 == f3_SLTIU)                  rd_val = (cmp_less_than ? 1 : 0);
      else if ( funct3 == f3_XORI)                  rd_val = pack (s_rs1_val ^ s_rs2_val_local);
      else if ( funct3 == f3_ORI )                  rd_val = pack (s_rs1_val | s_rs2_val_local);
      else if ( funct3 == f3_ANDI)                  rd_val = pack (s_rs1_val & s_rs2_val_local);

`ifdef DELAY_STAGE1_TRAPS
      alu_outputs.trap = trap;
      alu_outputs.control = CONTROL_STRAIGHT;
`else
      alu_outputs.control   = trap ? CONTROL_TRAP : CONTROL_STRAIGHT;
`endif
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
      WordXL rd_val = ?;

      if (funct3 == f3_ADDIW) begin
         WordXL tmp = pack (sum);
         rd_val = signExtend (tmp [31:0]);
      end
      else if ((funct3 == f3_SLLIW || funct3 == f3_SRxIW) && shamt5_is_0) begin
         rd_val = signExtend (shift_res_b32);
      end

`ifdef DELAY_STAGE1_TRAPS
      alu_outputs.trap = trap;
      alu_outputs.control = CONTROL_STRAIGHT;
`else
      alu_outputs.control   = trap ? CONTROL_TRAP : CONTROL_STRAIGHT;
`endif
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

`ifdef DELAY_STAGE1_TRAPS
      alu_outputs.trap = trap;
      alu_outputs.control = CONTROL_STRAIGHT;
`else
      alu_outputs.control   = trap ? CONTROL_TRAP : CONTROL_STRAIGHT;
`endif
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
`ifdef MERGE_IMMEDIATE
      Bit #(32) v32 = {inputs.decoded_instr.imm[19:0], 12'h0};
`else
      Bit #(32) v32 = {inputs.decoded_instr.imm20_U, 12'h0};
`endif
      IntXL iv_local = extend (unpack (v32));
      let rd_val = pack (iv_local);

      //alu_outputs.trap = False;
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
      alu_outputs.val1      = pack (sum);
   end

   else if (  inputs.decoded_instr.opcode == op_LOAD
           || inputs.decoded_instr.opcode == op_MISC_MEM && valueOf (XLEN) == 64 && funct3 == f3_LQ) begin
      WordXL eaddr = pack (sum);
      alu_outputs.addr           = eaddr;

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
      WordXL eaddr = pack (sum);
      alu_outputs.addr = eaddr;

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

   else if (  inputs.decoded_instr.opcode == op_MISC_MEM
           && !(valueOf (XLEN) == 64 && funct3 == f3_LQ))
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
      f3_cap_CIncOffsetImmediate: begin end
      f3_cap_CSetBoundsImmediate: begin end
      f3_cap_ThreeOp: begin
         case (funct7)
         f7_cap_CSpecialRW: begin end
         f7_cap_CSetBounds: begin end
         f7_cap_CSetBoundsExact: begin end
         f7_cap_CSetOffset: begin end
         f7_cap_CSetAddr: begin end
         f7_cap_CIncOffset: begin end
         f7_cap_CSeal: begin end
         f7_cap_CCSeal: begin end
         f7_cap_TwoSrc: begin
            case (inputs.decoded_instr.rd)
               rd_cap_CCall: begin end
            default: begin end //alu_outputs.control = CONTROL_TRAP;
            endcase // inputs.decoded_instr.rd
         end
         f7_cap_CUnseal: begin end
         f7_cap_CTestSubset: begin end
         f7_cap_CCopyType: begin
            case (getKind(cs2_val)) matches
               tagged UNSEALED: begin end
               tagged SENTRY: begin end
               tagged RES0: begin end
               tagged RES1: begin end
               tagged SEALED_WITH_TYPE .otype: begin end
            endcase // getKind (cs2_val)
         end
         f7_cap_CAndPerm: begin end
         f7_cap_CSetFlags: begin end
         f7_cap_CToPtr: begin end
         f7_cap_CFromPtr: begin end
         f7_cap_CSub: begin end
         f7_cap_CBuildCap: begin end
         f7_cap_Loads: begin
            // TODO LR
            if (!trap) begin
               Addr eaddr = pack (sum);
               let op_stage2 = False ? OP_Stage2_ST : OP_Stage2_LD;
`ifdef ISA_A
               if (is_amo) op_stage2 = OP_Stage2_AMO;
`endif

               alu_outputs.op_stage2      = op_stage2;
               alu_outputs.addr           = eaddr;
            end
         end
         f7_cap_Stores: begin
            if (!trap) begin
               Addr eaddr = pack (sum);
               let op_stage2 = OP_Stage2_ST;
`ifdef ISA_A
               if (is_amo) op_stage2 = OP_Stage2_AMO;
`endif
               //width code must be checked externally

               alu_outputs.op_stage2      = op_stage2;
               // TODO move this stuff later
               alu_outputs.addr           = eaddr;
               alu_outputs.mem_unsigned   = False;
               alu_outputs.val1           = zeroExtend({f5_AMO_SC, 2'b0});
            end
         end
         f7_cap_TwoOp: begin
            case (funct5rs2)
            f5rs2_cap_CGetLen: begin end
            f5rs2_cap_CGetBase: begin end
            f5rs2_cap_CGetTag: begin end
            f5rs2_cap_CGetSealed: begin end
            f5rs2_cap_CRRL: begin end
            f5rs2_cap_CRAM: begin end
            f5rs2_cap_CMove: begin end
            f5rs2_cap_CClearTag: begin end
            f5rs2_cap_CGetAddr: begin end
            f5rs2_cap_CSealEntry: begin end
            f5rs2_cap_CGetOffset: begin end
            f5rs2_cap_CGetFlags: begin end
            f5rs2_cap_CGetPerm: begin end
            f5rs2_cap_CJALR: begin end
            f5rs2_cap_CGetType: begin
               case (getKind(cheri_op1_val)) matches
                  tagged UNSEALED: begin end
                  tagged SENTRY: begin end
                  tagged RES0: begin end
                  tagged RES1: begin end
                  tagged SEALED_WITH_TYPE .otype: begin end
               endcase // getKind (cheri_op1_val)
            end
            default: begin end //alu_outputs.control = CONTROL_TRAP;
         endcase // funct5rs2
         end
      default: begin end //alu_outputs.control = CONTROL_TRAP;
      endcase // funct7
      end
      default: begin end //alu_outputs.control = CONTROL_TRAP;
      endcase // funct3
   end
`endif // ISA_CHERI

   else begin
`ifdef DELAY_STAGE1_TRAPS
      alu_outputs.trap = True;
      alu_outputs.control = CONTROL_STRAIGHT;
`else
      alu_outputs.control = CONTROL_TRAP;
`endif

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
