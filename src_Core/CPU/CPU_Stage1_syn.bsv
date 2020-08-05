package CPU_Stage1_syn;

import ISA_Decls     :: *;
import CPU_Globals :: *;
import EX_ALU_functions :: *;
//
//`ifdef ISA_M
//import RISCV_MBox  :: *;
//`endif


interface CPU_Stage1_syn_IFC;
   (* always_ready *)
   method Output_Stage1 get_outputs();

   (* always_ready *)
   method Action put_inputs(Bool rg_full_in,
                            Data_StageD_to_Stage1 rg_stage_input_in,
                            Epoch cur_epoch_in,
                            Bool rs1_busy_in,
                            Word rs1_val_bypassed_in,
                            Bool rs2_busy_in,
                            Word rs2_val_bypassed_in,
`ifdef ISA_F
                            Bool frs1_busy_in,
                            Bool frs2_busy_in,
                            Bool frs3_busy_in,
`endif
                            ALU_Outputs alu_outputs_in,
                            Priv_Mode cur_priv_in);
endinterface


(* synthesize *)
module mkCPU_Stage1_syn (CPU_Stage1_syn_IFC);
   Wire#(Data_StageD_to_Stage1) rg_stage_input <- mkDWire (?);
   Wire#(Epoch) cur_epoch <- mkDWire (?);
   Wire#(Bool) rs1_busy <- mkDWire (?);
   Wire#(Word) rs1_val_bypassed <- mkDWire (?);
   Wire#(Bool) rs2_busy <- mkDWire (?);
   Wire#(Word) rs2_val_bypassed <- mkDWire (?);
`ifdef ISA_F
   Wire#(Bool) frs1_busy <- mkDWire (?);
   Wire#(Bool) frs2_busy <- mkDWire (?);
   Wire#(Bool) frs3_busy <- mkDWire (?);
`endif
   Wire#(Priv_Mode) cur_priv <- mkDWire(?);
   Wire#(Bool) rg_full <- mkDWire (?);
   Wire#(ALU_Outputs) alu_outputs <- mkDWire (?);

   Wire#(Output_Stage1) outputs <- mkDWire (?);


   //let fall_through_pc = rg_stage_input.pc + (rg_stage_input.is_i32_not_i16 ? 4 : 2);
//   let next_pc = ((alu_outputs.control == CONTROL_BRANCH)
//			? alu_outputs.addr
//			: fall_through_pc);
   let next_pc = ((alu_outputs.control == CONTROL_BRANCH)
			? alu_outputs.addr
                        // NOTE when we have no branch prediction, alu_outputs.cf_info.falthru_PC
                        // is precisely the same as rg_stage_input.pred_pc; we can save an
                        // adder here
			// : alu_outputs.cf_info.fallthru_PC);
			: rg_stage_input.pred_pc);

`ifdef RVFI
   let info_RVFI = Data_RVFI_Stage1 {
                       instr:          rg_stage_input.instr,
                       rs1_addr:       rg_stage_input.decoded_instr.rs1,
                       rs2_addr:       rg_stage_input.decoded_instr.rs2,
                       rs1_data:       rs1_val_bypassed,
                       rs2_data:       rs2_val_bypassed,
                       pc_rdata:       rg_stage_input.pc,
                       pc_wdata:       next_pc,
`ifdef ISA_F
                       mem_wdata:      alu_outputs.rs_frm_fpr ? alu_outputs.fval2 : alu_outputs.val2,
`else
                       mem_wdata:      alu_outputs.val2,
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


   let data_to_stage2 = Data_Stage1_to_Stage2 {pc            : rg_stage_input.pc,
					       instr         : rg_stage_input.instr,
`ifdef RVFI_DII
                                               instr_seq     : rg_stage_input.instr_seq,
`endif
					       op_stage2     : alu_outputs.op_stage2,
					       rd            : alu_outputs.rd,
					       addr          : alu_outputs.addr,
					       val1          : alu_outputs.val1,
					       val2          : alu_outputs.val2,
`ifdef ISA_F
					       fval1         : alu_outputs.fval1,
					       fval2         : alu_outputs.fval2,
					       fval3         : alu_outputs.fval3,
					       rd_in_fpr     : alu_outputs.rd_in_fpr,
					       rs_frm_fpr    : alu_outputs.rs_frm_fpr,
					       val1_frm_gpr  : alu_outputs.val1_frm_gpr,
					       rounding_mode : alu_outputs.rm,
`endif
`ifdef INCLUDE_TANDEM_VERIF
					       trace_data    : alu_outputs.trace_data,
`endif
`ifdef RVFI
                                               info_RVFI_s1  : info_RVFI,
`endif
					       priv          : cur_priv };



   // ----------------
   // Combinational output function

   function Output_Stage1 fv_out;
      Output_Stage1 output_stage1 = ?;

      // This stage is empty
      if (! rg_full) begin
	 output_stage1.ostatus = OSTATUS_EMPTY;
      end

      // Wrong branch-prediction epoch: discard instruction (convert into a NOOP)
      else if (rg_stage_input.epoch != cur_epoch) begin
	 output_stage1.ostatus = OSTATUS_PIPE;
	 output_stage1.control = CONTROL_DISCARD;

	 // For debugging only
	 let data_to_stage2 = Data_Stage1_to_Stage2 {pc:        rg_stage_input.pc,
						     instr:     rg_stage_input.instr,
`ifdef RVFI_DII
                                                     instr_seq: rg_stage_input.instr_seq,
`endif
						     op_stage2: OP_Stage2_ALU,
						     rd:        0,
						     addr:      ?,
						     val1:      ?,
						     val2:      ?,
`ifdef ISA_F
						     fval1           : ?,
						     fval2           : ?,
						     fval3           : ?,
						     rd_in_fpr       : ?,
					             rs_frm_fpr      : ?,
					             val1_frm_gpr    : ?,
						     rounding_mode   : ?,
`endif
`ifdef INCLUDE_TANDEM_VERIF
						     trace_data: alu_outputs.trace_data,
`endif
`ifdef RVFI
                                                     info_RVFI_s1 : ?,
`endif
						     priv:      cur_priv
						     };

	 output_stage1.data_to_stage2 = data_to_stage2;
      end

      // Stall if bypass pending for GPR rs1 or rs2
      else if (rs1_busy || rs2_busy) begin
	 output_stage1.ostatus = OSTATUS_BUSY;
      end

`ifdef ISA_F
      // Stall if bypass pending for FPR rs1, rs2 or rs3
      else if (frs1_busy || frs2_busy || frs3_busy) begin
	 output_stage1.ostatus = OSTATUS_BUSY;
      end
`endif

      // Trap on fetch-exception
      else if (rg_stage_input.exc) begin
	 output_stage1.ostatus   = OSTATUS_NONPIPE;
	 output_stage1.control   = CONTROL_TRAP;
	 output_stage1.trap_info = Trap_Info {epc:      rg_stage_input.pc,
					      exc_code: rg_stage_input.exc_code,
					      tval:     rg_stage_input.tval};
	 output_stage1.data_to_stage2 = data_to_stage2;
      end

      // ALU outputs: pipe (straight/branch)
      // and non-pipe (CSRR_W, CSRR_S_or_C, FENCE.I, FENCE, SFENCE_VMA, xRET, WFI, TRAP)
      else begin
	 let ostatus = (  (   (alu_outputs.control == CONTROL_STRAIGHT)
			   || (alu_outputs.control == CONTROL_BRANCH))
			? OSTATUS_PIPE
			: OSTATUS_NONPIPE);

	 // Compute MTVAL in case of traps
	 let tval = 0;
	 if (alu_outputs.exc_code == exc_code_ILLEGAL_INSTRUCTION) begin
	    // The instruction
`ifdef ISA_C
	    tval = (rg_stage_input.is_i32_not_i16
		    ? zeroExtend (rg_stage_input.instr)
		    : zeroExtend (rg_stage_input.instr_C));
`else
	    tval = zeroExtend (rg_stage_input.instr);
`endif
	 end
	 else if (alu_outputs.exc_code == exc_code_INSTR_ADDR_MISALIGNED)
	    tval = alu_outputs.addr;                           // The branch target pc
	 else if (alu_outputs.exc_code == exc_code_BREAKPOINT)
	    tval = rg_stage_input.pc;                          // The faulting virtual address

	 let trap_info = Trap_Info {epc:      rg_stage_input.pc,
				    exc_code: alu_outputs.exc_code,
				    tval:     tval};

         // if we are not using branch prediction, then we can remove this comparison, since
         // next_pc is calculated in precisely the same way as pred_pc
	 // let redirect = (next_pc != rg_stage_input.pred_pc);
         let redirect = alu_outputs.control == CONTROL_BRANCH;

	 output_stage1.ostatus        = ostatus;
	 output_stage1.control        = alu_outputs.control;
	 output_stage1.trap_info      = trap_info;
	 output_stage1.redirect       = redirect;
	 output_stage1.next_pc        = next_pc;
	 output_stage1.cf_info        = alu_outputs.cf_info;
	 output_stage1.data_to_stage2 = data_to_stage2;
      end

      return output_stage1;
   endfunction: fv_out




   rule assign_outputs;
      outputs <= fv_out;
   endrule


   method Action put_inputs(Bool rg_full_in,
                            Data_StageD_to_Stage1 rg_stage_input_in,
                            Epoch cur_epoch_in,
                            Bool rs1_busy_in,
                            Word rs1_val_bypassed_in,
                            Bool rs2_busy_in,
                            Word rs2_val_bypassed_in,
`ifdef ISA_F
                            Bool frs1_busy_in,
                            Bool frs2_busy_in,
                            Bool frs3_busy_in,
`endif
                            ALU_Outputs alu_outputs_in,
                            Priv_Mode cur_priv_in);

   rg_full <= rg_full_in;
   rg_stage_input <= rg_stage_input_in;
   cur_epoch <= cur_epoch_in;
   rs1_busy <= rs1_busy_in;
   rs1_val_bypassed <= rs1_val_bypassed_in;
   rs2_busy <= rs2_busy_in;
   rs2_val_bypassed <= rs2_val_bypassed_in;
`ifdef ISA_F
   frs1_busy <= frs1_busy_in;
   frs2_busy <= frs2_busy_in;
   frs3_busy <= frs3_busy_in;
`endif
   alu_outputs <= alu_outputs_in;
   cur_priv <= cur_priv_in;

   endmethod


   method Output_Stage1 get_outputs = outputs;

endmodule

endpackage






