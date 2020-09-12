// Copyright (c) 2016-2020 Bluespec, Inc. All Rights Reserved

//-
// RVFI_DII + CHERI modifications:
//     Copyright (c) 2018 Jack Deeley
//     Copyright (c) 2018-2019 Peter Rugg (RVFI_DII + CHERI)
//     All rights reserved.
//
//     This software was developed by SRI International and the University of
//     Cambridge Computer Laboratory (Department of Computer Science and
//     Technology) under DARPA contract HR0011-18-C-0016 ("ECATS"), as part of the
//     DARPA SSITH research programme.
//-

package CPU_Stage2;

// ================================================================
// This is Stage 2 of the CPU.
// It is the "DM" stage ("Data Memory"), which is the main function.

// However, this stage also contains all other (potentially) long-latency
// operations:
//    MBox ("M" extension ops, integer multiply/divide)
//    FDBox ("FD" extension ops, single and double precision floating point)

// This stage sends out Tandem Verifier information for pipelined instructions

// Note: $displays are indented by (stage num x 4) spaces.
// for traditional pipeline display
//     IF
//         DM
//             WB
// i.e., 8 spaces for this stage.

// ================================================================
// Exports

export
CPU_Stage2_IFC (..),
mkCPU_Stage2;

// ================================================================
// BSV library imports

import FIFOF        :: *;
import GetPut       :: *;
import ClientServer :: *;
import ConfigReg    :: *;

// ----------------
// BSV additional libs

import Cur_Cycle  :: *;

// ================================================================
// Project imports

import ISA_Decls     :: *;

`ifdef RVFI
import Verifier  :: *;
import RVFI_DII  :: *;
`endif
import TV_Info       :: *;

import CPU_Globals      :: *;
import Near_Mem_IFC     :: *;
`ifdef Near_Mem_Avalon
import Near_Mem_Avalon_Common :: *;
`else
import MMU_Cache_Common :: *;    // for CacheOp
`endif
import CSR_RegFile      :: *;    // For SATP, SSTATUS, MSTATUS

`ifdef SHIFT_SERIAL
import Shifter_Box  :: *;
`endif

`ifdef ISA_M
import RISCV_MBox  :: *;
`endif

`ifdef ISA_F
import FBox_Top    :: *;
import FBox_Core   :: *;   // For fv_nanbox function
`endif

`ifdef ISA_CHERI
import CHERICap :: *;
import CHERICC_Fat :: *;
`endif

import CPU_Stage2_syn :: *;

// ================================================================
// Interface

interface CPU_Stage2_IFC;
   // ---- Reset
   interface Server #(Token, Token) server_reset;

   // ---- Output
   (* always_ready *)
   method Output_Stage2  out;

   (* always_ready *)
   method Action deq;

   // ---- Input
   (* always_ready *)
   method Action enq (Data_Stage1_to_Stage2 x, Bool valid);

   (* always_ready *)
   method Action set_full (Bool full);
endinterface

// ================================================================
// Implementation module

module mkCPU_Stage2 #(Bit #(4)         verbosity,
		      CSR_RegFile_IFC  csr_regfile,    // for SATP and SSTATUS: TODO carry in Data_Stage1_to_Stage2
		      DMem_IFC         dcache)
                    (CPU_Stage2_IFC);

   FIFOF #(Token) f_reset_reqs <- mkFIFOF;
   FIFOF #(Token) f_reset_rsps <- mkFIFOF;

   Reg #(Bool)                  rg_resetting  <- mkReg (False);
   Reg #(Bool)                  rg_full       <- mkReg (False);
   Reg #(Data_Stage1_to_Stage2) rg_stage2     <- mkRegU;    // From Stage 1
   Reg #(Bit#(5))               rg_f5         <- mkReg (0);

   // ----------------
   // Serial shifter box

`ifdef SHIFT_SERIAL
   Shifter_Box_IFC shifter_box <- mkShifter_Box;
`endif

   // ----------------
   // Integer multiply/divide box

`ifdef ISA_M
   RISCV_MBox_IFC mbox <- mkRISCV_MBox;
`endif

   // ----------------
   // Floating point box

`ifdef ISA_F
   FBox_Top_IFC fbox <- mkFBox_Top (0);
`endif

   // ----------------

`ifdef RVFI
   let info_RVFI_s1 = rg_stage2.info_RVFI_s1;
`endif

   let bypass_base = Bypass {bypass_state: BYPASS_RD_NONE,
			     rd:           rg_stage2.rd,
			     rd_val:       extract_cap(rg_stage2.val1)
			     };

`ifdef ISA_F
   let fbypass_base = FBypass {bypass_state: BYPASS_RD_NONE,
			       rd:           rg_stage2.rd,
			       rd_val:       rg_stage2.fval1
			       };
`endif

`ifdef RVFI
    let info_RVFI_s2_base = Data_RVFI_Stage2 {
                                    stage1:     info_RVFI_s1,
                                    mem_rmask:  0,
                                    mem_wmask:  0
                                };
`endif

   let data_to_stage3_base = Data_Stage2_to_Stage3 {
        priv:       rg_stage2.priv
`ifdef ISA_CHERI
      , pcc:        rg_stage2.pcc
`else
      , pc:         rg_stage2.pc
`endif
      , instr:      rg_stage2.instr
`ifdef RVFI_DII
      , instr_seq:  rg_stage2.instr_seq
`endif
`ifdef RVFI
      , info_RVFI_s2: info_RVFI_s2_base
`endif
      , rd_valid:   False
      , rd:         rg_stage2.rd
      , rd_val:     cast (rg_stage2.val1)
`ifdef ISA_F
						    , rd_in_fpr:  False,
						    upd_flags:  False,
						    fpr_flags:  0,
						    frd_val:    rg_stage2.fval1
`endif
`ifdef INCLUDE_TANDEM_VERIF
						    , trace_data: rg_stage2.trace_data
`endif
						    };

   let  trap_info_dmem = Trap_Info_Pipe {
				    exc_code: dcache.exc_code,
`ifdef ISA_CHERI
            cheri_exc_code: dcache.exc_code == exc_code_CHERI ? exc_code_CHERI_Length: exc_code_CHERI_None,
            cheri_exc_reg: ?, //TODO
            epcc: rg_stage2.pcc,
`else
            epc:  rg_stage2.pc,
`endif
				    tval: rg_stage2.addr };

`ifdef ISA_F
   // The FBox can only generate ILLEGAL Instruction exceptions
   let  trap_info_fbox = Trap_Info_Pipe {
`ifdef ISA_CHERI
            epcc:     rg_stage2.pcc,
            cheri_exc_code: ?,
            cheri_exc_reg: ?,
`else
            epc:      rg_stage2.pc,
`endif
				    exc_code: exc_code_ILLEGAL_INSTRUCTION,
				    tval:     0 };
`endif

   // ----------------------------------------------------------------
   // BEHAVIOR

   rule rl_reset_begin;
      f_reset_reqs.deq;
      rg_full <= False;
      rg_resetting <= True;
`ifdef ISA_F
      fbox.server_reset.request.put (?);
`endif
   endrule

   rule rl_reset_end (rg_resetting);
      rg_resetting <= False;

`ifdef ISA_F
      let res <- fbox.server_reset.response.get;
`endif

      f_reset_rsps.enq (?);
   endrule

   // ----------------
   // Combinational output function

   let stage2_wrapper <- mkCPU_Stage2_syn;
   let stage2_outputs = stage2_wrapper.stage2_outputs (rg_full,
`ifdef ISA_A
                                                       rg_f5,
`endif
                                                       rg_stage2,
                                                       mbox.valid,
                                                       mbox.word,
                                                       dcache.valid,
                                                       dcache.exc,
                                                       dcache.exc_code,
`ifdef Near_Mem_Avalon
                                                       dcache.word64
`else
                                                       dcache.word128
`endif
                                                      );


   // ----------------
   // Initiate DM, Shifter box, MBox or FBox op

   function Action fa_enq (Data_Stage1_to_Stage2 x, Bool valid);
      action
	 if (valid) rg_stage2  <= x;

	 let funct3 = instr_funct3 (x.instr);

	 // If DMem access, initiate it
`ifdef ISA_A
	 Bool op_stage2_amo = (x.op_stage2 == OP_Stage2_AMO);
`ifdef ISA_CHERI
	 Bit #(5) amo_funct5 = getAddr(extract_cap(x.val1)) [6:2];
	 Bit #(7) amo_funct7 = getAddr(extract_cap(x.val1)) [6:0];
`else
	 Bit #(5) amo_funct5 = pack(x.val1) [6:2];
	 Bit #(7) amo_funct7 = pack(x.val1) [6:0];
`endif
         if (valid) rg_f5 <= amo_funct5;
`else
	 Bool op_stage2_amo = False;
	 Bit #(5) amo_funct5 = 0;
	 Bit #(7) amo_funct7 = 0;
`endif
	 if (((x.op_stage2 == OP_Stage2_LD) || (x.op_stage2 == OP_Stage2_ST) || op_stage2_amo) && !x.trap) begin
	    WordXL   mstatus     = csr_regfile.read_mstatus;
`ifdef ISA_PRIV_S
	    Bit #(1) sstatus_SUM = (csr_regfile.read_sstatus) [18];
`else
	    Bit #(1) sstatus_SUM = 0;
`endif
	    Bit #(1) mstatus_MXR = mstatus [19];
	    Priv_Mode  mem_priv = x.priv;
	    if (mstatus [17] == 1'b1) begin
	       mem_priv = mstatus [12:11];
	       // $display ("    S2.fa_enq: mem_priv %0d => %0d (mstatus.MPP) due to mstatus.MPRV", x.priv, mem_priv);
	    end

	    CacheOp cache_op = ?;
	    if      (x.op_stage2 == OP_Stage2_LD)  cache_op = CACHE_LD;
	    else if (x.op_stage2 == OP_Stage2_ST)  cache_op = CACHE_ST;
`ifdef ISA_A
	    else if (x.op_stage2 == OP_Stage2_AMO) cache_op = CACHE_AMO;
`endif

`ifdef ISA_CHERI
        CapReg capReg = cast(extract_cap(x.val2));
        CapMem capMem = cast(capReg);
        Bit#(TSub#(SizeOf#(CapMem),1)) tagless = truncate(capMem);
`endif

        dcache.req (cache_op,
`ifdef Near_Mem_Avalon
                        funct3,
`else
			x.mem_width_code,
            x.mem_unsigned,
`endif
`ifdef ISA_A
			amo_funct5,
`endif
			x.addr,
`ifdef ISA_F
			x.rs_frm_fpr ? tuple2(False,zeroExtend(x.fval2)) :
`endif
`ifdef ISA_CHERI
      tuple2(x.mem_width_code == w_SIZE_CAP && isValidCap(capMem), zeroExtend(tagless)),
`else
      tuple2(False, zeroExtend(x.val2)),
`endif
			mem_priv,
			sstatus_SUM,
			mstatus_MXR,
			csr_regfile.read_satp);
	 end

`ifdef SHIFT_SERIAL
	 // If Shifter box op, initiate it
	 else if (x.op_stage2 == OP_Stage2_SH)
	    shifter_box.req (unpack (funct3 [2]), x.val1_fast, x.val2_fast);
`endif

`ifdef ISA_M
	 // If MBox op, initiate it
	 else if (x.op_stage2 == OP_Stage2_M) begin
            // Instr fields required for decode for F/D opcodes
	    Bool is_OP_not_OP_32 = (x.instr [3] == 1'b0);
            mbox.req (is_OP_not_OP_32, funct3, x.val1_fast, x.val2_fast);
	 end
`endif

`ifdef ISA_F
	 // If FBox op, initiate it
	 else if (x.op_stage2 == OP_Stage2_FD) begin
	    // Instr fields required for decode for F/D opcodes
            let opcode = instr_opcode (x.instr);
	    let funct7 = instr_funct7 (x.instr);
            let rs2    = instr_rs2    (x.instr);
            Bit #(64) val1 = x.val1_frm_gpr ? extend(x.val1_fast)
                                            : extend (x.fval1);

	    fbox.req (opcode,
		      funct7,
		      x.rounding_mode,   // rm
		      rs2,
		      val1,
		      extend (x.fval2),
		      extend (x.fval3),
		      valid);
         end
`endif
      endaction
   endfunction

   // ----------------------------------------------------------------
   // INTERFACE

   // ---- Reset
   interface server_reset = toGPServer (f_reset_reqs, f_reset_rsps);

   // ---- Output
   method Output_Stage2  out;
      return stage2_outputs;
   endmethod

   method Action deq ();
      noAction;
   endmethod

   // ---- Input
   method Action enq (Data_Stage1_to_Stage2 x, Bool valid);
      fa_enq (x, valid);

      if (verbosity > 1 && valid)
	 $display ("%0t    CPU_Stage2.enq (Data_Stage1_to_Stage2) ", $time, fshow(x));
   endmethod

   method Action set_full (Bool full);
      rg_full <= full;
   endmethod
endmodule

// ================================================================

endpackage
