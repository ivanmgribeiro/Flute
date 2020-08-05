// Copyright (c) 2016-2020 Bluespec, Inc. All Rights Reserved.

package Near_Mem_Avalon_Common;

// ================================================================
// Types etc. shared by multiple modules in Near_Mem_Avalon complex.

// ================================================================
// Project imports

import ISA_Decls   :: *;

// ================================================================
// Near_Mem opcodes

typedef enum {  CACHE_LD
	      , CACHE_ST
   } CacheOp
deriving (Bits, Eq, FShow);

// ================================================================
// Check if addr is aligned

function Bool fn_is_aligned (Bit #(3) f3, Bit #(n) addr);
   return (    (f3 [1:0] == 2'b00)                                // B, BU
	   || ((f3 [1:0] == 2'b01) && (addr [0] == 1'b0))         // H, HU
	   || ((f3 [1:0] == 2'b10) && (addr [1:0] == 2'b00))      // W, WU
	   || ((f3 [1:0] == 2'b11) && (addr [2:0] == 3'b000))     // D
	   );
endfunction

// ================================================================

endpackage
