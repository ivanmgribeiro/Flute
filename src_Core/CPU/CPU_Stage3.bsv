// Copyright (c) 2016-2020 Bluespec, Inc. All Rights Reserved

package CPU_Stage3;

// ================================================================
// This is Stage 3 of the CPU.
// It is the WB ("Write Back") stage:
// - Writes back a GPR register value (if the instr has a GPR Rd)
// - Writes back an FPR register value (if the instr has an FPR Rd)
// - Updates CSR INSTRET
//     Note: this instr cannot be a CSRRx updating INSTRET, since
//           CSRRx is done completely off-pipe.
// = Optionaally: sends a TandemVerification trace packet

// ================================================================
// Exports

export
CPU_Stage3_IFC (..),
mkCPU_Stage3;

// ================================================================
// BSV library imports

import ConfigReg    :: *;
import FIFOF        :: *;
import GetPut       :: *;
import ClientServer :: *;

// ----------------
// BSV additional libs

import Cur_Cycle :: *;

// ================================================================
// Project imports

import ISA_Decls   :: *;
import GPR_RegFile :: *;
`ifdef ISA_F
import FPR_RegFile :: *;
`endif
import CSR_RegFile :: *;
import CPU_Globals :: *;

`ifdef INCLUDE_TANDEM_VERIF
import TV_Info     :: *;
`endif

`ifdef NEW_REG
import Forwarding_RegFile :: *;
`endif

import CPU_Stage3_syn :: *;

// ================================================================
// Interface

interface CPU_Stage3_IFC;
   // ---- Reset
   interface Server #(Token, Token) server_reset;

   // ---- Output
   (* always_ready *)
   method Output_Stage3  out;

   (* always_ready *)
   method Action deq;

   // ---- Input
   (* always_ready *)
   method Action enq (Data_Stage2_to_Stage3 x);

   (* always_ready *)
   method Action set_full (Bool full);

   // ---- Debugging
   method Action show_state;
endinterface

// ================================================================
// Module

(* synthesize *)
module mkRegUSynth_2to3 (Reg#(Data_Stage2_to_Stage3));
    let rg <- mkRegU;
    return rg;
endmodule

module mkCPU_Stage3 #(Bit #(4)         verbosity,
`ifdef NEW_REG
                      ForwardingPipelinedRegFileIFC #(Word, RegName, 4) gpr_regfile,
`else
		      GPR_RegFile_IFC  gpr_regfile,
`endif
`ifdef ISA_F
		      FPR_RegFile_IFC  fpr_regfile,
`endif
		      CSR_RegFile_IFC  csr_regfile)
                    (CPU_Stage3_IFC);

   FIFOF #(Token) f_reset_reqs <- mkFIFOF;
   FIFOF #(Token) f_reset_rsps <- mkFIFOF;

   Reg #(Bool)                  rg_full   <- mkReg (False);
   Reg #(Data_Stage2_to_Stage3) rg_stage3 <- mkRegUSynth_2to3;    // From Stage 2

   // ----------------------------------------------------------------
   // BEHAVIOR

   rule rl_reset;
      f_reset_reqs.deq;
      rg_full <= False;
      f_reset_rsps.enq (?);
   endrule

   // ----------------
   // Combinational output function

   let stage3_wrapper <- mkCPU_Stage3_syn;
   rule assign_inputs;
      stage3_wrapper.put_inputs(rg_full, rg_stage3);
   endrule

   let fv_out = stage3_wrapper.get_outputs;

   // ----------------
   // Actions on 'deq': writeback Rd and update CSR INSTRET

   function Action fa_deq;
      action
	 // Writeback Rd if valid
         $display("S3 fa_deq called");
`ifdef NEW_PIPE_LOGIC
         if (rg_stage3.invalid) begin
            gpr_regfile.writeReg (?, False);
            if (verbosity > 1) begin
               $display("pipelined regfile write nop: instr 0x%0h, pc 0x%0h", rg_stage3.instr, rg_stage3.pc);
            end
         end else
`endif
	 if (rg_stage3.rd_valid) begin
`ifdef ISA_F
            // Write to FPR
            if (rg_stage3.rd_in_fpr)
               fpr_regfile.write_rd (rg_stage3.rd, rg_stage3.frd_val);

            else
               // Write to GPR
`ifdef NEW_REG
               //gpr_regfile.writeReg (rg_stage3.rd_val, True);
`else
               gpr_regfile.write_rd (rg_stage3.rd, rg_stage3.rd_val);
`endif
`else
            // Write to GPR in a non-FD system
`ifdef NEW_REG
            $display(" pipelined regfile write: instr 0x%0h, value 0x%0h", rg_stage3.instr, rg_stage3.rd_val);
            if (rg_full && gpr_regfile.canWrite) begin
               gpr_regfile.writeReg (rg_stage3.rd_val, True);
            end
`else
            gpr_regfile.write_rd (rg_stage3.rd, rg_stage3.rd_val);
`endif
`endif

	    if (verbosity > 1)
`ifdef ISA_F
               if (rg_stage3.rd_in_fpr)
                  $display ("    S3.fa_deq: write FRd 0x%0h, rd_val 0x%0h",
                            rg_stage3.rd, rg_stage3.frd_val);
               else
`endif
                  $display ("    S3.fa_deq: write GRd 0x%0h, rd_val 0x%0h",
                            rg_stage3.rd, rg_stage3.rd_val);

`ifdef ISA_F
            // Update FCSR.fflags
            if (rg_stage3.upd_flags)
               csr_regfile.ma_update_fcsr_fflags (rg_stage3.fpr_flags);

            // Update MSTATUS.FS
            if (rg_stage3.upd_flags || rg_stage3.rd_in_fpr)
               csr_regfile.ma_update_mstatus_fs (fs_xs_dirty);
`endif
         end
`ifdef NEW_PIPE_LOGIC
	 else if (!rg_stage3.rd_valid) begin
            gpr_regfile.writeReg (?, False);
            if (verbosity > 1) begin
               $display(" pipelined regfile write None: instr 0x%0h, pc 0x%0h", rg_stage3.instr, rg_stage3.pc);
            end
         end
`endif
      endaction
   endfunction

   // ----------------------------------------------------------------
   // INTERFACE

   // ---- Reset
   interface server_reset = toGPServer (f_reset_reqs, f_reset_rsps);

   // ---- Output

   method Output_Stage3  out;
      return fv_out;
   endmethod

   method Action deq;
      fa_deq;
   endmethod

   // ---- Input
   method Action enq (Data_Stage2_to_Stage3 x);
      rg_stage3 <= x;

      if (verbosity > 1)
	 $display ("    S3.enq: ", fshow (x));
   endmethod

   method Action set_full (Bool full);
      rg_full <= full;
   endmethod

   // ---- Debugging
   method Action show_state;
      if (rg_full)
	 $display ("    CPU_Stage3 state: ", fshow (rg_stage3));
      else
	 $display ("    CPU_Stage3 state: empty");
   endmethod
endmodule

// ================================================================

endpackage
