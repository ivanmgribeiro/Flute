package CPU_Stage3_syn;

import CPU_Globals :: *;

interface CPU_Stage3_syn_IFC;
   (* always_ready *)
   method Output_Stage3 get_outputs();

   (* always_ready *)
   method Action put_inputs(Bool rg_full_in,
                            Data_Stage2_to_Stage3 rg_stage3_in);
endinterface


(* synthesize *)
module mkCPU_Stage3_syn (CPU_Stage3_syn_IFC);
   Wire#(Bool) rg_full <- mkDWire (?);
   Wire#(Data_Stage2_to_Stage3) rg_stage3 <- mkDWire (?);

   Wire#(Output_Stage3) outputs <- mkDWire (?);


   let bypass_base = Bypass {bypass_state: BYPASS_RD_NONE,
			     rd:           rg_stage3.rd,
			     // WordXL        WordXL
			     rd_val:       rg_stage3.rd_val
			     };

`ifdef ISA_F
   let fbypass_base = FBypass {bypass_state: BYPASS_RD_NONE,
			       rd:           rg_stage3.rd,
			       // WordFL        WordFL
			       rd_val:       rg_stage3.frd_val
			       };
`endif

   // ----------------
   // Combinational output function

   function Output_Stage3 fv_out;
      let bypass = bypass_base;
`ifdef ISA_F
      let fbypass = fbypass_base;
      if (rg_stage3.rd_in_fpr) begin
         bypass.bypass_state = BYPASS_RD_NONE;
         fbypass.bypass_state = (rg_full && rg_stage3.rd_valid) ? BYPASS_RD_RDVAL
                                                                : BYPASS_RD_NONE;
      end
      else begin
         fbypass.bypass_state = BYPASS_RD_NONE;
         bypass.bypass_state = (rg_full && rg_stage3.rd_valid) ? BYPASS_RD_RDVAL
                                                               : BYPASS_RD_NONE;
      end
`else
      bypass.bypass_state = (rg_full && rg_stage3.rd_valid) ? BYPASS_RD_RDVAL
                                                            : BYPASS_RD_NONE;
`endif

`ifdef INCLUDE_TANDEM_VERIF
      let trace_data = rg_stage3.trace_data;
`ifdef ISA_F
      if (rg_stage3.upd_flags) begin
	 let fflags = csr_regfile.mv_update_fcsr_fflags (rg_stage3.fpr_flags);
	 trace_data = fv_trace_update_fcsr_fflags (trace_data, fflags);
      end

      if (rg_stage3.upd_flags || rg_stage3.rd_in_fpr) begin
	 let new_mstatus = csr_regfile.mv_update_mstatus_fs (fs_xs_dirty);
	 trace_data = fv_trace_update_mstatus_fs (trace_data, new_mstatus);
      end
`endif
`endif

`ifdef NEW_PIPE_LOGIC
      return Output_Stage3 {ostatus: (rg_full ? (rg_stage3.invalid ? OSTATUS_NOP : OSTATUS_PIPE)
                                              : OSTATUS_EMPTY),
`else
      return Output_Stage3 {ostatus: (rg_full ? OSTATUS_PIPE
                                              : OSTATUS_EMPTY),
`endif
			    bypass : bypass
`ifdef ISA_F
			    , fbypass: fbypass
`endif
`ifdef INCLUDE_TANDEM_VERIF
			    , trace_data: trace_data
`endif
			    };
   endfunction


   rule assign_outputs;
      outputs <= fv_out;
   endrule

   method Output_Stage3 get_outputs = outputs;

   method Action put_inputs(Bool rg_full_in,
                            Data_Stage2_to_Stage3 rg_stage3_in);
      rg_full <= rg_full_in;
      rg_stage3 <= rg_stage3_in;
   endmethod


endmodule

endpackage
