// Copyright (c) 2016-2019 Bluespec, Inc. All Rights Reserved

package RISCV_MBox;

// ================================================================
// This package executes the 'M' extension instructions (MUL/DIV/REM)

// ================================================================
// Exports

export
RISCV_MBox_IFC (..),
mkRISCV_MBox;

// ================================================================
// BSV Library imports

import Assert    :: *;
import ConfigReg :: *;

// ----------------
// BSV additional libs

import Cur_Cycle  :: *;
import GetPut_Aux :: *;

// ================================================================
// Project imports

import ISA_Decls :: *;
import IntMulDiv :: *;

// ================================================================
// MBox interface

interface RISCV_MBox_IFC;
   method Action set_verbosity (Bit #(4) verbosity);

   method Action                   req_reset;
   method ActionValue #(Bit #(0))  rsp_reset;

   // MBox interface: request
   (* always_ready *)
   method Action  req (Bool is_OP_not_OP_32, Bit #(3) f3, WordXL v1, WordXL v2);

   // MBox interface: response
   (* always_ready *)   method Bool    valid;
   (* always_ready *)   method WordXL  word;
endinterface

// ================================================================

typedef enum { STATE_MUL1_START, STATE_MUL1, STATE_MUL2, STATE_DIV_REM_START, STATE_DIV_REM } State
deriving (Bits, Eq, FShow);

(* synthesize *)
module mkRISCV_MBox (RISCV_MBox_IFC);

   Reg #(Bit #(4)) cfg_verbosity <- mkConfigReg (0);

   Reg #(State)     rg_state <- mkRegU;

   Reg #(Bool)      rg_is_OP_not_OP_32 <- mkRegU;
   Reg #(Bit #(3))  rg_f3              <- mkRegU;
   Reg #(WordXL)    rg_v1              <- mkRegU;
   Reg #(WordXL)    rg_v2              <- mkRegU;
   Reg #(WordXL)    rg_v1_0            <- mkRegU;
   Reg #(WordXL)    rg_v2_0            <- mkRegU;
   Reg #(WordXL)    rg_result          <- mkRegU;

   IntDiv_IFC #(XLEN) intDiv <- mkIntDiv (rg_v1, rg_v2);

`ifdef MULT_SERIAL
`ifdef RV64
   IntMul_IFC#(64) intMul <- mkIntMul_64;
`else
   IntMul_IFC#(32) intMul <- mkIntMul_32;
`endif
`endif

   Reg #(Bool)    dw_valid  <- mkDWire (False);
   Reg #(WordXL)  dw_result <- mkDWire (?);

   rule start_operation (rg_state == STATE_MUL1_START || rg_state == STATE_DIV_REM_START);
      Bool is_signed = (rg_f3 [0] == 1'b0);
      rg_v1 <= rg_v1_0;
      rg_v2 <= rg_v2_0;
      if (rg_state == STATE_MUL1_START) begin
         rg_state <= rg_state == STATE_MUL1_START ? STATE_MUL1 : STATE_DIV_REM;
      end else begin
         rg_state <= rg_state == STATE_MUL1_START ? STATE_MUL1 : STATE_DIV_REM;
	 intDiv.start (is_signed, is_signed);
      end
   endrule


   // ----------------------------------------------------------------
   // MUL family: SYNTH implementation
   // Relies on the fav_MUL/MULH/MULHU/MULHSU/MULW functions later in
   // this package which do multiplication directly with Verilog's '*'
   // and rely on Verilog synthesis to implement the multiplier.
   // (DSPs on FPGAa).


`ifdef MULT_SYNTH

   rule rl_mul (rg_state == STATE_MUL1);
      if (cfg_verbosity > 1)
	 $display ("    RISCV_MBox.rl_mul");

      WordXL result = '1;

      if      (rg_is_OP_not_OP_32     && (rg_f3 == f3_MUL))     result <- fav_MUL (rg_v1, rg_v2);
      else if (rg_is_OP_not_OP_32     && (rg_f3 == f3_MULH))    result <- fav_MULH (rg_v1, rg_v2);
      else if (rg_is_OP_not_OP_32     && (rg_f3 == f3_MULHU))   result <- fav_MULHU (rg_v1, rg_v2);
      else if (rg_is_OP_not_OP_32     && (rg_f3 == f3_MULHSU))  result <- fav_MULHSU (rg_v1, rg_v2);
`ifdef RV64
      else if ((! rg_is_OP_not_OP_32) && (rg_f3 == f3_MUL))     result <- fav_MULW (rg_v1, rg_v2);
`endif
      else begin
	 // This should be Impossible
	 $display ("%0d: ERROR: RISCV_MBox.rl_mul: illegal f3.", cur_cycle);
	 $display ("    f3 0x%0h  v1 0x%0h  v2 0x%0h", rg_f3, rg_v1, rg_v2);
	 $finish (1);    // TODO: illegal instruction; should trap
      end

      rg_result <= result;
      rg_state  <= STATE_MUL2;
   endrule

   rule rl_mul2 (rg_state == STATE_MUL2);
      let result = rg_result;
      dw_valid  <= True;
      dw_result <= result;
   endrule

`endif

   // ----------------------------------------------------------------
   // MUL family: SERIAL implementation
   // Uses the iterative multiplier in the 'IntMulDiv' package.

`ifdef MULT_SERIAL
   rule rl_mul (rg_state == STATE_MUL1 && intMul.result_valid);
      WordXL result;
      if      (rg_is_OP_not_OP_32     && (rg_f3 == f3_MUL))     begin
	 result = (intMul.result_value)[xlen-1:0];
      end
      else if (rg_is_OP_not_OP_32     && (rg_f3 == f3_MULH))    begin
	 result = (intMul.result_value)[2 * xlen - 1 : xlen];
      end
      else if (rg_is_OP_not_OP_32     && (rg_f3 == f3_MULHU))   begin
	 result = (intMul.result_value)[2 * xlen - 1 : xlen];
      end
      else if (rg_is_OP_not_OP_32     && (rg_f3 == f3_MULHSU))  begin
	 result = (intMul.result_value)[2 * xlen - 1 : xlen];
      end
`ifdef RV64
      else if ((! rg_is_OP_not_OP_32) && (rg_f3 == f3_MUL))     begin
	 result = signExtend((intMul.result_value)[31:0]);
      end
`endif
      else begin
	 // This should be Impossible
	 $display ("%0d: ERROR: RISCV_MBox.rl_mul: illegal f3. again", cur_cycle);
	 result = 0; // to keep bsc happy
      end

      dw_valid  <= True;
      dw_result <= result;
   endrule
`endif

   // ----------------------------------------------------------------
   // DIV family and REM family
   // Uses the iterative divider provided in the imported 'IntMulDiv' package.

   rule rg_div_rem ((rg_state == STATE_DIV_REM) && intDiv.result_valid);
      match { .q, .r } = intDiv.result_value;
      WordXL result = ((rg_f3 [1] == 1'b0) ? q : r );

`ifdef RV64
      if (! rg_is_OP_not_OP_32)
	 result = signExtend (result [31:0]);
`endif

      dw_valid  <= True;
      dw_result <= result;
   endrule

   // ================================================================
   // INTERFACE

   method Action set_verbosity (Bit #(4) verbosity);
      cfg_verbosity <= verbosity;
   endmethod

   method Action req_reset;
      noAction;
   endmethod

   method ActionValue #(Bit #(0))  rsp_reset;
      return (?);
   endmethod

   // MBox interface: request
   method Action  req (Bool is_OP_not_OP_32, Bit #(3) f3, WordXL v1, WordXL v2);

      Bool is_signed = (f3 [0] == 1'b0);

`ifdef RV64
      if (! is_OP_not_OP_32) begin
	 // RV64 ops MULW/DIVW/DIVUW/REMW/REMUW)
	 if (is_signed) begin
	    v1 = signExtend (v1 [31:0]);
	    v2 = signExtend (v2 [31:0]);
	 end
	 else begin
	    v1 = zeroExtend (v1 [31:0]);
	    v2 = zeroExtend (v2 [31:0]);
	 end
      end
`endif

      rg_is_OP_not_OP_32 <= is_OP_not_OP_32;
      rg_f3              <= f3;
      rg_v1_0            <= v1;
      rg_v2_0            <= v2;

      // MUL, MULH, MULHU, MULHSU

      if (f3 [2] == 1'b0) begin
	 rg_state <= STATE_MUL1_START;

`ifdef MULT_SERIAL
	 Bool s1, s2;

	 if      (is_OP_not_OP_32     && (f3 == f3_MUL))     begin
	    s1 = False; s2 = False;
	 end
	 else if (is_OP_not_OP_32     && (f3 == f3_MULH))    begin
	    s1 = True; s2 = True;
	 end
	 else if (is_OP_not_OP_32     && (f3 == f3_MULHU))   begin
	    s1 = False; s2 = False;
	 end
	 else if (is_OP_not_OP_32     && (f3 == f3_MULHSU))  begin
	    s1 = True; s2 = False;
	 end
`ifdef RV64
	 else if ((! is_OP_not_OP_32) && (f3 == f3_MUL))     begin
	    // Signed versions of lower 32 bits of v_rs1 and v_rs2
	    v1 = signExtend (v1 [31:0]);
	    v2 = signExtend (v2 [31:0]);
	    s1 = True; s2 = True;
	 end
`endif
	 else begin
	    // This should be Impossible
	    $display ("%0d: ERROR: RISCV_MBox.rl_mul: illegal f3.", cur_cycle);
	    $display ("    f3 0x%0h  v1 0x%0h  v2 0x%0h", f3, v1, v2);
	    $finish (1);    // TODO: illegal instruction; should trap
	    s1 = ?; s2 = ?; // to keep bsc happy
	 end

	 intMul.put_args(s1, v1, s2, v2);
`endif
      end

      // DIV, DIVU, REM, REMU
      else begin
	 rg_state <= STATE_DIV_REM_START;
      end
   endmethod

   // MBox interface: response
   method Bool  valid;
      return dw_valid;
   endmethod

   method WordXL  word;
      return dw_result;
   endmethod
endmodule

// ================================================================
// ================================================================
// ================================================================
// Multiplication functions

// Below, ifdef RV32 versions of each function also work for RV64.
// However, there is a bug in Vivado synthesis when XLEN==64. Then,
// the code involves a 128b x 128b -> 128b multiply expression, for
// which Vivado produces buggy code and crashes on synthesis.

// The alternative forms (in ifdef RV64) only involve 64b x 64b -> 64b
// multiplication expressions, which Vivado seems to synthesize
// correctly to DSP code.

// TODO: Once Vivado fixes their bug, remove the 'ifdef RV64' code,
// and remove the 'ifdef RV32' brackets.

// ================================================================
// MUL

function ActionValue #(WordXL) fav_MUL (WordXL v_rs1, WordXL v_rs2);
   actionvalue
      // Signed versions of v_rs1 and v_rs2
      IntXL s_v_rs1 = unpack (v_rs1);
      IntXL s_v_rs2 = unpack (v_rs2);

      WordXL v_rd = pack (s_v_rs1 * s_v_rs2);
      return v_rd;
   endactionvalue
endfunction

// ================================================================
// MULH: signed XLEN x signed XLEN -> signed [2 x XLEN], return upper XLEN

`ifdef RV32

function ActionValue #(WordXL) fav_MULH (WordXL v_rs1, WordXL v_rs2);
   actionvalue
      // Signed versions of v_rs1 and v_rs2
      IntXL s_v_rs1 = unpack (v_rs1);
      IntXL s_v_rs2 = unpack (v_rs2);

      Int #(XLEN_2) s_v1     = extend (s_v_rs1);
      Int #(XLEN_2) s_v2     = extend (s_v_rs2);
      Int #(XLEN_2) s_result = s_v1 * s_v2;
      WordXL v_rd = pack (s_result) [2 * xlen - 1: xlen];
      return v_rd;
   endactionvalue
endfunction

`endif

`ifdef RV64

function ActionValue #(Bit #(64)) fav_MULH (Bit #(64) v_rs1, Bit #(64) v_rs2);
   actionvalue
      match { .neg1, .val1_64 } = fn_isneg_and_absval (v_rs1);
      match { .neg2, .val2_64 } = fn_isneg_and_absval (v_rs2);

      Bit #(128) prod = fn_unsigned_mul_64_64 (val1_64, val2_64);
      if (neg1 != neg2)
	 prod = fn_twos_comp (prod);

      Bit #(64) v_rd = prod [127:64];
      return v_rd;
   endactionvalue
endfunction

`endif

// ================================================================
// MULHU: unsigned XLEN x unsigned XLEN -> unsigned [2 x XLEN], return upper XLEN

`ifdef RV32

function ActionValue #(WordXL) fav_MULHU (WordXL v_rs1, WordXL v_rs2);
   actionvalue
      Bit #(XLEN_2) v1     = extend (v_rs1);
      Bit #(XLEN_2) v2     = extend (v_rs2);
      Bit #(XLEN_2) result = v1 * v2;
      WordXL v_rd = result [2 * xlen - 1: xlen];
      return v_rd;
   endactionvalue
endfunction

`endif

`ifdef RV64

function ActionValue #(Bit #(64)) fav_MULHU (Bit #(64) v_rs1, Bit #(64) v_rs2);
   actionvalue
      Bit #(128) prod = fn_unsigned_mul_64_64 (v_rs1, v_rs2);
      Bit #(64) v_rd = prod [127:64];
      return v_rd;
   endactionvalue
endfunction

`endif

// ================================================================
// MULHSU: signed XLEN x unsigned XLEN -> signed [2 x XLEN], return upper XLEN

`ifdef RV32

function ActionValue #(WordXL) fav_MULHSU (WordXL v_rs1, WordXL v_rs2);
   actionvalue
      // Signed version of v_rs1
      IntXL s_v_rs1 = unpack (v_rs1);

      Int #(XLEN_2) s_v1     = extend (s_v_rs1);
      Int #(XLEN_2) s_v2     = unpack (extend (v_rs2));
      Int #(XLEN_2) s_result = s_v1 * s_v2;
      WordXL v_rd = pack (s_result) [2 * xlen - 1: xlen];
      return v_rd;
   endactionvalue
endfunction

`endif

`ifdef RV64

function ActionValue #(Bit #(64)) fav_MULHSU (Bit #(64) v_rs1, Bit #(64) v_rs2);
   actionvalue
      match { .neg1, .val1_64 } = fn_isneg_and_absval (v_rs1);
      match { .neg2, .val2_64 } = tuple2 (False, v_rs2);

      Bit #(128) prod = fn_unsigned_mul_64_64 (val1_64, val2_64);
      if (neg1 != neg2)
	 prod = fn_twos_comp (prod);

      Bit #(64) v_rd = prod [127:64];
      return v_rd;
   endactionvalue
endfunction

`endif

// ================================================================
// MULW

`ifdef RV64
function ActionValue #(WordXL) fav_MULW (WordXL v_rs1, WordXL v_rs2);
   actionvalue
      // Signed versions of lower 32 bits of v_rs1 and v_rs2
      IntXL s_v_rs1 = unpack (signExtend (v_rs1 [31:0]));
      IntXL s_v_rs2 = unpack (signExtend (v_rs2 [31:0]));
      WordXL prod64 = pack (s_v_rs1 * s_v_rs2);

      WordXL v_rd = signExtend (prod64 [31:0]);
      return v_rd;
   endactionvalue
endfunction
`endif

// ================================================================
// Help-functions for Vivado work-around codes above

function Tuple2 #(Bool, Bit #(64)) fn_isneg_and_absval (Bit #(64) x);
   return (  (x[63] == 0)
	   ? tuple2 (False, x)
	   : tuple2 (True,  fn_twos_comp (x)));
endfunction

function Bit #(n) fn_twos_comp (Bit #(n) x);
   return (~ x) + 1;
endfunction

function Bit #(128) fn_unsigned_mul_64_64 (Bit #(64) v1, Bit #(64) v2);
   let zero_32b = 32'h0;
   let zero_64b = 64'h0;

   Bit #(64) ll = { zero_32b, v1 [31: 0]} * { zero_32b, v2 [31: 0]};
   Bit #(64) lh = { zero_32b, v1 [31: 0]} * { zero_32b, v2 [63:32]};
   Bit #(64) hl = { zero_32b, v1 [63:32]} * { zero_32b, v2 [31: 0]};
   Bit #(64) hh = { zero_32b, v1 [63:32]} * { zero_32b, v2 [63:32]};
   Bit #(128) result = (  {    hh,    zero_64b }
			+ { zero_32b, lh, zero_32b }
			+ { zero_32b, hl, zero_32b }
			+ { zero_64b, ll });
   return result;
endfunction

// ================================================================

endpackage
