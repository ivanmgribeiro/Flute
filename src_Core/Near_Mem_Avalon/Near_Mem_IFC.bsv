package Near_Mem_IFC;

import ISA_Decls :: *;
import Near_Mem_Avalon_Common :: *;
import ClientServer :: *;

typedef struct {
   Bit #(XLEN) avm_readdata;
   Bool        avm_waitrequest;
   Bool        avm_readdatavalid;
   Bit #(2)    avm_response;
} Avalon_Inputs deriving (Bits, FShow);

typedef struct {
   Bit #(XLEN)         avm_address;
   Bool                avm_read;
   Bool                avm_write;
   Bit #(XLEN)         avm_writedata;
   Bit #(Bytes_per_WordXL) avm_byteenable;
} Avalon_Outputs deriving (Bits, FShow);

interface Avalon_IFC;
   (* always_enabled *)
   method Action in (Avalon_Inputs inputs);
   (* always_ready *)
   method Avalon_Outputs out;
endinterface

interface Near_Mem_IFC;
   // Reset
   interface Server #(Token, Token) server_reset;

   //-------------
   // IMem

   // CPU side
   interface IMem_IFC imem;

   // Top side
   interface Avalon_IFC imem_master;


   //-------------
   // DMem

   // CPU side
   interface DMem_IFC dmem;

   // Top side
   interface Avalon_IFC dmem_master;

   interface Server #(Token, Token) server_fence_i;

   interface Server #(Fence_Ordering, Token) server_fence;

   // ----------------------------------------------------------------
   // For ISA tests: watch memory writes to <tohost> addr

`ifdef WATCH_TOHOST
   method Action set_watch_tohost (Bool watch_tohost, Bit #(64) tohost_addr);
`endif

endinterface


// ================================================================
// IMem interface

interface IMem_IFC;
   // CPU side: IMem request
   (* always_ready *)
   method Action  req (Bit #(3) f3,
		       WordXL addr,
		       // The following  args for VM
		       Priv_Mode  priv,
		       Bit #(1)   sstatus_SUM,
		       Bit #(1)   mstatus_MXR,
		       WordXL     satp
               );    // { VM_Mode, ASID, PPN_for_page_table }

   // CPU side: IMem response
   (* always_ready *)  method Bool     valid;
   (* always_ready *)  method Bool     is_i32_not_i16;
   (* always_ready *)  method WordXL   pc;
   (* always_ready *)  method Instr    instr;
   (* always_ready *)  method Bool     exc;
   (* always_ready *)  method Exc_Code exc_code;
   (* always_ready *)  method WordXL   tval;        // can be different from PC
endinterface

// ================================================================
// DMem interface

interface DMem_IFC;
   // CPU side: DMem request
   (* always_ready *)
   method Action  req (CacheOp op,
		       Bit #(3) f3,
		       WordXL addr,
		       Bit #(64) store_value,
		       // The following  args for VM
		       Priv_Mode  priv,
		       Bit #(1)   sstatus_SUM,
		       Bit #(1)   mstatus_MXR,
		       WordXL     satp);    // { VM_Mode, ASID, PPN_for_page_table }

   // CPU side: DMem response
   (* always_ready *)  method Bool       valid;
   // this will still be called word64 to simplify the work being undertaken
   // when in the core, this is always truncated to a WordXL
   // TODO change this (and the signals in the core) to be XLEN rather than hardcoded 64
   (* always_ready *)  method Bit #(64)  word64;      // Load-value
   (* always_ready *)  method Bit #(64)  st_amo_val;  // Final store-value for ST, SC, AMO
   (* always_ready *)  method Bool       exc;
   (* always_ready *)  method Exc_Code   exc_code;
endinterface

// ================================================================
// Extract bytes from raw word read from near-mem.
// The bytes of interest are offset according to LSBs of addr.
// Arguments:
//  - a RISC-V LD/ST f3 value (encoding LB, LH, LW, LD, LBU, LHU, LWU)
//  - a byte-address
//  - a load-word (loaded from cache/mem)
// result:
//  - word with correct byte(s) shifted into LSBs and properly extended
function Bit #(XLEN) fn_extract_and_extend_bytes (Bit #(3) f3, WordXL byte_addr, Bit #(XLEN) wordxl);
   Bit #(XLEN) result    = 0;
`ifdef RV64
   Bit #(3)  addr_lsbs = byte_addr [2:0];
`else
   Bit #(2)  addr_lsbs = byte_addr [1:0];
`endif

   case (f3)
      f3_LB: case (addr_lsbs)
		'h0: result = signExtend (wordxl [ 7: 0]);
		'h1: result = signExtend (wordxl [15: 8]);
		'h2: result = signExtend (wordxl [23:16]);
		'h3: result = signExtend (wordxl [31:24]);
`ifdef RV64
		'h4: result = signExtend (wordxl [39:32]);
		'h5: result = signExtend (wordxl [47:40]);
		'h6: result = signExtend (wordxl [55:48]);
		'h7: result = signExtend (wordxl [63:56]);
`endif
	     endcase
      f3_LBU: case (addr_lsbs)
		'h0: result = zeroExtend (wordxl [ 7: 0]);
		'h1: result = zeroExtend (wordxl [15: 8]);
		'h2: result = zeroExtend (wordxl [23:16]);
		'h3: result = zeroExtend (wordxl [31:24]);
`ifdef RV64
		'h4: result = zeroExtend (wordxl [39:32]);
		'h5: result = zeroExtend (wordxl [47:40]);
		'h6: result = zeroExtend (wordxl [55:48]);
		'h7: result = zeroExtend (wordxl [63:56]);
`endif
	     endcase

      f3_LH: case (addr_lsbs)
		'h0: result = signExtend (wordxl [15: 0]);
		'h2: result = signExtend (wordxl [31:16]);
`ifdef RV64
		'h4: result = signExtend (wordxl [47:32]);
		'h6: result = signExtend (wordxl [63:48]);
`endif
	     endcase
      f3_LHU: case (addr_lsbs)
		'h0: result = zeroExtend (wordxl [15: 0]);
		'h2: result = zeroExtend (wordxl [31:16]);
`ifdef RV64
		'h4: result = zeroExtend (wordxl [47:32]);
		'h6: result = zeroExtend (wordxl [63:48]);
`endif
	     endcase

      f3_LW: case (addr_lsbs)
		'h0: result = signExtend (wordxl [31: 0]);
`ifdef RV64
		'h4: result = signExtend (wordxl [63:32]);
`endif
	     endcase
      f3_LWU: case (addr_lsbs)
		'h0: result = zeroExtend (wordxl [31: 0]);
`ifdef RV64
		'h4: result = zeroExtend (wordxl [63:32]);
`endif
	     endcase

`ifdef RV64
      f3_LD: case (addr_lsbs)
		'h0: result = wordxl;
	     endcase
`endif
   endcase
   return result;
endfunction

function Bit #(XLEN) fn_extend_bytes (Bit #(3) f3, Bit #(XLEN) wordxl);
   Bit #(XLEN) result = ?;
   case (f3)
      f3_LB:  result = signExtend (wordxl [ 7:0]);
      f3_LBU: result = zeroExtend (wordxl [ 7:0]);
      f3_LH:  result = signExtend (wordxl [15:0]);
      f3_LHU: result = zeroExtend (wordxl [15:0]);
      f3_LW:  result = signExtend (wordxl [31:0]);
      f3_LWU: result = zeroExtend (wordxl [31:0]); // TODO is LWU allowed in RV32?
`ifdef RV64
      f3_LD:  result = zeroExtend (wordxl [31:0]);
`endif
   endcase
   return result;
endfunction


function Bit #(Bytes_per_WordXL) fn_byteenable_from_req (Bit #(3) f3, WordXL addr);
   Bit #(Bytes_per_WordXL) result = 0;
`ifdef RV64
   let addr_lsbs = addr[2:0];
`else
   let addr_lsbs = addr[1:0];
`endif
   case (f3)
      f3_LB, f3_LBU, f3_SB:
         result = zeroExtend(4'b0001);
      f3_LH, f3_LHU, f3_SH:
         result = zeroExtend(4'b0011);
      f3_LWU, f3_SW:
         result = zeroExtend(4'b1111);
`ifdef RV64
      f3_LD, f3_SD:
         case (addr_lsbs)
            'h0: result = zeroExtend(8'b1111_1111);
`endif
   endcase
   return result;
endfunction


endpackage: Near_Mem_IFC
