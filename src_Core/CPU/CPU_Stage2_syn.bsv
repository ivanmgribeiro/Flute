package CPU_Stage2_syn;

import ISA_Decls     :: *;
import CPU_Globals :: *;

`ifdef ISA_M
import RISCV_MBox  :: *;
`endif


interface CPU_Stage2_syn_IFC;
   (* always_ready *)
   method Output_Stage2 get_outputs();

   (* always_ready *)
   method Action put_inputs(Bool rg_full_in,
                            Data_Stage1_to_Stage2 rg_stage2_in,
                            Bool dcache_in,
                            Exc_Code dmem_exc_code_in,
                            Bit#(64) dmem_word64_in,
                            Bool mbox_valid_in,
                            WordXL mbox_word_in);
endinterface


(* synthesize *)
module mkCPU_Stage2_syn (CPU_Stage2_syn_IFC);
   Wire#(Bool) rg_full <- mkDWire (?);
   Wire#(Data_Stage1_to_Stage2) rg_stage2 <- mkDWire (?);
   Wire#(Bool) dcache_valid <- mkDWire (?);
   Wire#(Bool) dcache_exc <- mkDWire (?);
   Wire#(Exc_Code) dcache_exc_code <- mkDWire (?);
   Wire#(Bit#(64)) dcache_word64 <- mkDWire (?);
   Wire#(Bool) mbox_valid <- mkDWire (?);
   Wire#(WordXL) mbox_word <- mkDWire (?);


   Wire#(Output_Stage2) outputs <- mkDWire (?);




   let  trap_info_dmem = Trap_Info {epc:      rg_stage2.pc,
				    exc_code: dcache_exc_code,
				    tval:     rg_stage2.addr };


   let data_to_stage3_base = Data_Stage2_to_Stage3 {priv:       rg_stage2.priv,
						    pc:         rg_stage2.pc,
						    instr:      rg_stage2.instr,

						    rd_valid:   False,
						    rd:         rg_stage2.rd,
						    rd_val:     rg_stage2.val1
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


   let bypass_base = Bypass {bypass_state: BYPASS_RD_NONE,
			     rd:           rg_stage2.rd,
			     rd_val:       rg_stage2.val1
			     };

`ifdef ISA_F
   let fbypass_base = FBypass {bypass_state: BYPASS_RD_NONE,
			       rd:           rg_stage2.rd,
			       rd_val:       rg_stage2.fval1
			       };
`endif

   // ----------------
   // Combinational output function

   function Output_Stage2 fv_out;
      Output_Stage2 output_stage2 = ?;

      // This stage is empty
      if (! rg_full) begin
	 output_stage2 = Output_Stage2 {ostatus         : OSTATUS_EMPTY,
					trap_info       : ?,
					data_to_stage3  : ?,
					bypass          : no_bypass
`ifdef ISA_F
					, fbypass       : no_fbypass
`endif
					};
      end

      // This stage is just relaying ALU results from previous stage to next stage
      else if (rg_stage2.op_stage2 == OP_Stage2_ALU) begin
	 let data_to_stage3 = data_to_stage3_base;
	 data_to_stage3.rd_valid = True;

	 let bypass = bypass_base;
	 bypass.bypass_state = BYPASS_RD_RDVAL;

	 output_stage2 = Output_Stage2 {ostatus         : OSTATUS_PIPE,
					trap_info       : ?,
					data_to_stage3  : data_to_stage3,
					bypass          : bypass
`ifdef ISA_F
					, fbypass       : no_fbypass
`endif
					};
      end

      // This stage is doing a LOAD or AMO
      else if (   (rg_stage2.op_stage2 == OP_Stage2_LD)
`ifdef ISA_A
	       || (rg_stage2.op_stage2 == OP_Stage2_AMO)
`endif
	       )
	 begin
	    let ostatus = (  (! dcache_valid)
			   ? OSTATUS_BUSY
			   : (  dcache_exc
			      ? OSTATUS_NONPIPE
			      : OSTATUS_PIPE));

	    WordXL result = truncate (dcache_word64);

            let funct3 = instr_funct3 (rg_stage2.instr);

	    let data_to_stage3 = data_to_stage3_base;
	    data_to_stage3.rd_valid = (ostatus == OSTATUS_PIPE);

`ifdef ISA_F
            data_to_stage3.rd_in_fpr = rg_stage2.rd_in_fpr;
            // A FPR load
            if (rg_stage2.rd_in_fpr) begin
`ifdef ISA_D
               // Both FLW and FLD are legal instructions
               // A FLW result
               if (funct3 == f3_FLW)
                  // needs nan-boxing when destined for a DP register file
                  data_to_stage3.frd_val = fv_nanbox (dcache_word64);

               // A FLD result
               else
                  data_to_stage3.frd_val = dcache_word64;
`else
               // Only FLW is a legal instruction
               data_to_stage3.frd_val = truncate (dcache_word64);
`endif
            end
`endif
            // GPR loads
	    data_to_stage3.rd_val   = result;

            // Update the bypass channel, if not trapping (NONPIPE)
	    let bypass = bypass_base;
`ifdef ISA_F
	    let fbypass = fbypass_base;
`endif

	    if (ostatus != OSTATUS_NONPIPE) begin
`ifdef ISA_F
               // Bypassing FPR value.
               if (rg_stage2.rd_in_fpr) begin
		  // Choose one of the following two options

		  // Option 1: longer critical path, since the data is bypassed back into previous stage.
		  // We use data_to_stage3.rd_val since nanboxing has been done.
		  // fbypass.bypass_state = ((ostatus == OSTATUS_PIPE) ? BYPASS_RD_RDVAL : BYPASS_RD);
		  // fbypass.rd_val       = data_to_stage3.frd_val;

		  // Option 2: shorter critical path, since the data is not bypassed into previous stage,
		  // (the bypassing is effectively delayed until the next stage).
		  fbypass.bypass_state = BYPASS_RD;
               end
`endif

               // Bypassing GPR values
               if (rg_stage2.rd != 0) begin    // TODO: is this test necessary?
		  // Choose one of the following two options

		  // Option 1: longer critical path, since the data is bypassed back into previous stage.
		  // We use data_to_stage3.rd_val since nanboxing has been done.
		  // bypass.bypass_state = ((ostatus == OSTATUS_PIPE) ? BYPASS_RD_RDVAL : BYPASS_RD);
		  // bypass.rd_val       = result;

		  // Option 2: shorter critical path, since the data is not bypassed into previous stage,
		  // (the bypassing is effectively delayed until the next stage).
		  bypass.bypass_state = BYPASS_RD;
	       end
	    end

`ifdef INCLUDE_TANDEM_VERIF
	    let trace_data = rg_stage2.trace_data;
`ifdef ISA_F
            if (rg_stage2.rd_in_fpr) begin
               trace_data.word5 = data_to_stage3.frd_val;

               // Update MSTATUS.FS in trace packet
	       let new_mstatus = csr_regfile.mv_update_mstatus_fs (fs_xs_dirty);
               trace_data = fv_trace_update_mstatus_fs (trace_data, new_mstatus);
            end else
`endif
               trace_data.word1 = data_to_stage3.rd_val;

            data_to_stage3.trace_data = trace_data;
`endif

            output_stage2 = Output_Stage2 {ostatus         : ostatus,
					   trap_info       : trap_info_dmem,
					   data_to_stage3  : data_to_stage3,
					   bypass          : bypass
`ifdef ISA_F
					   , fbypass       : fbypass
`endif
					   };
	 end

      // This stage is doing a STORE
      else if (rg_stage2.op_stage2 == OP_Stage2_ST) begin
	 let ostatus = (  (! dcache_valid)
			     ? OSTATUS_BUSY
			     : (  dcache_exc
				? OSTATUS_NONPIPE
				: OSTATUS_PIPE));

	 let data_to_stage3 = data_to_stage3_base;
	 data_to_stage3.rd_valid = (ostatus == OSTATUS_PIPE);
	 data_to_stage3.rd       = 0;

	 output_stage2 = Output_Stage2 {ostatus         : ostatus,
					trap_info       : trap_info_dmem,
					data_to_stage3  : data_to_stage3,
					bypass          : no_bypass
`ifdef ISA_F
					, fbypass       : no_fbypass
`endif
					};
      end

`ifdef SHIFT_SERIAL
      // This stage is doing a serial shift
      else if (rg_stage2.op_stage2 == OP_Stage2_SH) begin
	 let ostatus = ((! shifter_box.valid) ? OSTATUS_BUSY : OSTATUS_PIPE);

	 let result = shifter_box.word;

	 let data_to_stage3 = data_to_stage3_base;
	 data_to_stage3.rd_valid = (ostatus == OSTATUS_PIPE);
	 data_to_stage3.rd_val   = result;

	 let bypass = bypass_base;
	 bypass.bypass_state = ((ostatus == OSTATUS_PIPE) ? BYPASS_RD_RDVAL : BYPASS_RD);
	 bypass.rd_val       = result;

`ifdef INCLUDE_TANDEM_VERIF
	 let trace_data            = rg_stage2.trace_data;
	 trace_data.word1          = result;
	 data_to_stage3.trace_data = trace_data;
`endif

	 output_stage2 = Output_Stage2 {ostatus         : ostatus,
					trap_info       : ?,
					data_to_stage3  : data_to_stage3,
					bypass          : bypass
`ifdef ISA_F
					, fbypass         : no_fbypass
`endif
					};
      end
`endif

`ifdef ISA_M
      // This stage is doing an integer multiply/divide
      else if (rg_stage2.op_stage2 == OP_Stage2_M) begin
	 let ostatus = ((! mbox_valid) ? OSTATUS_BUSY : OSTATUS_PIPE);

	 let result = mbox_word;

	 let data_to_stage3 = data_to_stage3_base;
	 data_to_stage3.rd_valid = (ostatus == OSTATUS_PIPE);
	 data_to_stage3.rd_val   = result;

	 let bypass = bypass_base;
	 bypass.bypass_state = ((ostatus == OSTATUS_PIPE) ? BYPASS_RD_RDVAL : BYPASS_RD);
	 bypass.rd_val       = result;

`ifdef INCLUDE_TANDEM_VERIF
	 let trace_data            = rg_stage2.trace_data;
	 trace_data.word1          = result;
	 data_to_stage3.trace_data = trace_data;
`endif

	 output_stage2 = Output_Stage2 {ostatus         : ostatus,
					trap_info       : ?,
					data_to_stage3  : data_to_stage3,
					bypass          : bypass
`ifdef ISA_F
					, fbypass         : no_fbypass
`endif
					};
      end
`endif

`ifdef ISA_F
      // This stage is doing a floating point op
      else if (rg_stage2.op_stage2 == OP_Stage2_FD) begin
	 let ostatus = ((! fbox.valid) ? OSTATUS_BUSY : OSTATUS_PIPE);

         // Extract fields from FBOX result
	 match {.value, .fflags} = fbox.word;

	 let data_to_stage3      = data_to_stage3_base;
	 data_to_stage3.rd_valid = (ostatus == OSTATUS_PIPE);
`ifdef ISA_D
	 data_to_stage3.frd_val  = value;
`else
	 data_to_stage3.frd_val  = truncate (value);
`endif
         data_to_stage3.rd_in_fpr= rg_stage2.rd_in_fpr;
         data_to_stage3.upd_flags= True;
         data_to_stage3.fpr_flags= fflags;

         // result is meant for a FPR
	 let bypass              = bypass_base;
         let fbypass             = fbypass_base;
         if (rg_stage2.rd_in_fpr) begin
            fbypass.bypass_state    = ((ostatus==OSTATUS_PIPE) ? BYPASS_RD_RDVAL
                                                               : BYPASS_RD);
`ifdef ISA_D
            fbypass.rd_val          = value;
`else
            fbypass.rd_val          = truncate (value);
`endif
         end

         // result is meant for a GPR
         else begin
            bypass.bypass_state     = ((ostatus==OSTATUS_PIPE) ? BYPASS_RD_RDVAL
                                                               : BYPASS_RD);
`ifdef RV64
            bypass.rd_val           = (value);
            data_to_stage3.rd_val   = value;
`else
            bypass.rd_val           = truncate (value);
            data_to_stage3.rd_val   = truncate (value);
`endif
         end

         // -----
`ifdef INCLUDE_TANDEM_VERIF
	 let trace_data = rg_stage2.trace_data;

         if (rg_stage2.rd_in_fpr) begin
            trace_data.word5 = data_to_stage3.frd_val;
         end else begin
            trace_data.word1 = data_to_stage3.rd_val;
         end

	 data_to_stage3.trace_data = trace_data;
`endif

	 output_stage2 = Output_Stage2 {ostatus         : ostatus,
					trap_info       : trap_info_fbox,
					data_to_stage3  : data_to_stage3,
					bypass          : bypass
`ifdef ISA_F
					, fbypass       : fbypass
`endif
         };
      end
`endif

      return output_stage2;
   endfunction



   rule assign_outputs;
      outputs <= fv_out;
   endrule


   method Action put_inputs(Bool rg_full_in,
                            Data_Stage1_to_Stage2 rg_stage2_in,
                            Bool dcache_valid_in,
                            Exc_Code dcache_exc_code_in,
                            Bit#(64) dcache_word64_in,
                            Bool mbox_valid_in,
                            WordXL mbox_word_in);
      rg_full <= rg_full_in;
      rg_stage2 <= rg_stage2_in;
      dcache_valid <= dcache_valid_in;
      dcache_exc_code <= dcache_exc_code_in;
      dcache_word64 <= dcache_word64_in;
      mbox_valid <= mbox_valid_in;
      mbox_word <= mbox_word_in;
   endmethod


   method Output_Stage2 get_outputs = outputs;

endmodule

endpackage






