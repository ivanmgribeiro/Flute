package CPU_Stage1_syn;

import ISA_Decls        :: *;
import CPU_Globals      :: *;
import Near_Mem_IFC     :: *;
import GPR_RegFile      :: *;
import EX_ALU_functions :: *;

`ifdef ISA_C
// 'C' extension (16b compressed instructions)
import CPU_Decode_C     :: *;
`endif

`ifdef ISA_CHERI
import CHERICap :: *;
import CHERICC_Fat :: *;
`endif

interface CPU_Stage1_syn_IFC;
   method Output_Stage1 stage1_outputs (
                                        Bool rg_full,
                                        Epoch cur_epoch,
                                        Priv_Mode cur_priv,
                                        Data_StageD_to_Stage1 rg_stage_input,
                                        PCC_T rg_pcc,
`ifdef RVFI
`ifdef ISA_CHERI
                                        CapPipe rs1_val_bypassed,
                                        CapPipe rs2_val_bypassed,
`else
                                        WordXL rs1_val_bypassed,
                                        WordXL rs2_val_bypassed,
`endif
`endif
                                        Bool rs1_busy,
                                        Bool rs2_busy,
`ifdef ISA_F
                                        Bool frs1_busy,
                                        Bool frs2_busy,
                                        Bool frs3_busy,
`endif
                                        ALU_Outputs alu_outputs
                                       );
endinterface

`ifdef SYNTHESIZE_MODULES
(* synthesize *)
`endif
module mkCPU_Stage1_syn (CPU_Stage1_syn_IFC);

   function Output_Stage1 fv_out (Bool rg_full,
                                   Epoch cur_epoch,
                                   Priv_Mode cur_priv,
                                   Data_StageD_to_Stage1 rg_stage_input,
                                   PCC_T rg_pcc,
`ifdef RVFI
`ifdef ISA_CHERI
                                   CapPipe rs1_val_bypassed,
                                   CapPipe rs2_val_bypassed,
`else
                                   WordXL rs1_val_bypassed,
                                   WordXL rs2_val_bypassed,
`endif
`endif
                                   Bool rs1_busy,
                                   Bool rs2_busy,
`ifdef ISA_F
                                   Bool frs1_busy,
                                   Bool frs2_busy,
                                   Bool frs3_busy,
`endif
                                   ALU_Outputs alu_outputs


   
                                  );

   let fall_through_pc_addr = alu_outputs.cf_info.fallthru_PC;
   let next_pc_addr_local = ((alu_outputs.control == CONTROL_BRANCH)
                          ? alu_outputs.addr
                          : fall_through_pc_addr);

   let next_pcc_local = (alu_outputs.control == CONTROL_CAPBRANCH)
                        ? alu_outputs.pcc
                        : setPCCAddr (rg_pcc, next_pc_addr_local);


`ifdef RVFI
   let rs1 = rg_stage_input.decoded_instr.rs1;
   let rs2 = rg_stage_input.decoded_instr.rs2;
   CapReg tmp_val2 = cast(alu_outputs.cap_val2);
   CapMem cap_val2 = cast(tmp_val2);
   let info_RVFI = Data_RVFI_Stage1 {
                       instr:          rg_stage_input.instr,
                       rs1_addr:       rs1,
                       rs2_addr:       rs2,
`ifdef ISA_CHERI
                       rs1_data:       getAddr(rs1_val_bypassed),
                       rs2_data:       getAddr(rs2_val_bypassed),
`else
                       rs1_data:       rs1_val_bypassed,
                       rs2_data:       rs2_val_bypassed,
`endif
                       pc_rdata:       getPC(rg_pcc),
                       pc_wdata:       getPC(next_pcc_local),
`ifdef ISA_F
                       mem_wdata:      alu_outputs.rs_frm_fpr ? alu_outputs.fval2 : truncate(cap_val2),
`else
                       mem_wdata:      truncate(cap_val2),
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

      let data_to_stage2 = Data_Stage1_to_Stage2 {
`ifdef ISA_CHERI
                                                  pcc:       rg_pcc,
`else
                                                  pc:        rg_stage_input.pc,
`endif
					          instr         : rg_stage_input.instr,
`ifdef RVFI_DII
                                                  instr_seq     : rg_stage_input.instr_seq,
`endif
					          op_stage2     : alu_outputs.op_stage2,
`ifdef DELAY_STAGE1_TRAPS
                                                  trap          : alu_outputs.trap,
                                                  trap_info     : ?,
`endif
					          rd            : alu_outputs.rd,
					          addr          : alu_outputs.addr,
                                                  mem_width_code: alu_outputs.mem_width_code,
                                                  mem_unsigned  : alu_outputs.mem_unsigned,
`ifdef ISA_CHERI
                                                  mem_allow_cap : alu_outputs.mem_allow_cap,
                                                  val1          : alu_outputs.val1_cap_not_int ? embed_cap(alu_outputs.cap_val1): embed_int(alu_outputs.val1),
                                                  val2          : alu_outputs.val2_cap_not_int ? embed_cap(alu_outputs.cap_val2): embed_int(alu_outputs.val2),
`else
                                                  val1          : alu_outputs.val1,
                                                  val2          : alu_outputs.val2,
`endif
                                                  val1_fast     : alu_outputs.val1_fast,
                                                  val2_fast     : alu_outputs.val2_fast,
`ifdef ISA_F
					          fval1         : alu_outputs.fval1,
					          fval2         : alu_outputs.fval2,
					          fval3         : alu_outputs.fval3,
					          rd_in_fpr     : alu_outputs.rd_in_fpr,
					          rs_frm_fpr    : alu_outputs.rs_frm_fpr,
					          val1_frm_gpr  : alu_outputs.val1_frm_gpr,
					          rounding_mode : alu_outputs.rm,
`endif
`ifdef ISA_CHERI
                                                  check_enable       : alu_outputs.check_enable,
                                                  check_inclusive    : alu_outputs.check_inclusive,
                                                  check_authority    : alu_outputs.check_authority,
                                                  check_authority_idx: alu_outputs.check_authority_idx,
                                                  check_address_low  : alu_outputs.check_address_low,
                                                  authority_base     : alu_outputs.authority_base,
                                                  check_address_high : alu_outputs.check_address_high,
                                                  authority_top      : alu_outputs.authority_top,
                                                  check_exact_enable : alu_outputs.check_exact_enable,
                                                  check_exact_success: alu_outputs.check_exact_success,
`endif
`ifdef INCLUDE_TANDEM_VERIF
					          trace_data    : alu_outputs.trace_data,
`endif
`ifdef RVFI
                                                  info_RVFI_s1  : info_RVFI,
`endif
					          priv          : cur_priv };

      let fetch_exc = checkValid(rg_pcc, rg_stage_input.is_i32_not_i16);

`ifndef DISABLE_BRANCH_PRED
      let redirect = (alu_outputs.control == CONTROL_CAPBRANCH)
        ? (getPCCAddr (alu_outputs.pcc) != rg_stage_input.pred_fetch_addr)
        : (next_pc_addr_local != rg_stage_input.pred_fetch_addr);
`else
      let redirect = alu_outputs.control == CONTROL_CAPBRANCH || alu_outputs.control == CONTROL_BRANCH;
`endif


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
	 let data_to_stage2 = Data_Stage1_to_Stage2 {
`ifdef ISA_CHERI
                                                     pcc:       rg_pcc,
`else
                                                     pc:        rg_stage_input.pc,
`endif
						     instr:     rg_stage_input.instr,
`ifdef RVFI_DII
                                                     instr_seq: rg_stage_input.instr_seq,
`endif
						     op_stage2: OP_Stage2_ALU,
`ifdef DELAY_STAGE1_TRAPS
                                                     trap: False,
                                                     trap_info : ?,
`endif
						     rd:        0,
						     addr:      ?,
						     val1:      ?,
						     val2:      ?,
						     val1_fast: ?,
						     val2_fast: ?,
`ifdef ISA_F
						     fval1           : ?,
						     fval2           : ?,
						     fval3           : ?,
						     rd_in_fpr       : ?,
					             rs_frm_fpr      : ?,
					             val1_frm_gpr    : ?,
						     rounding_mode   : ?,
`endif
                                                     mem_unsigned  : ?,
                                                     mem_width_code: ?,
`ifdef ISA_CHERI
                                               mem_allow_cap      : False,
                                               check_enable       : False,
                                               check_inclusive    : ?,
                                               check_authority    : ?,
                                               check_authority_idx: ?,
                                               check_address_low  : ?,
                                               authority_base     : ?,
                                               check_address_high : ?,
                                               authority_top      : ?,
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

`ifdef ISA_CHERI
      else if (isValid(fetch_exc)) begin
	 let trap_info = Trap_Info_Pipe {
                exc_code: exc_code_CHERI,
                cheri_exc_code : fetch_exc.Valid,
                cheri_exc_reg : {1, scr_addr_PCC},
                epcc: rg_pcc,
                tval: rg_stage_input.tval};
`ifdef DELAY_STAGE1_TRAPS
         output_stage1.ostatus   = OSTATUS_PIPE;
         output_stage1.control   = CONTROL_STRAIGHT;
         data_to_stage2.trap      = True;
         data_to_stage2.trap_info = trap_info;
`else
	 output_stage1.ostatus   = OSTATUS_NONPIPE;
	 output_stage1.control   = CONTROL_TRAP;
         output_stage1.trap_info = trap_info;
`endif
	 output_stage1.data_to_stage2 = data_to_stage2;
      end
`endif

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
	 let trap_info           = Trap_Info_Pipe {
                                              epcc: rg_pcc,
					      exc_code: rg_stage_input.exc_code,
                                              cheri_exc_code: ?,
                                              cheri_exc_reg: ?,
					      tval:     rg_stage_input.tval};
`ifdef DELAY_STAGE1_TRAPS
         output_stage1.ostatus   = OSTATUS_PIPE;
         output_stage1.control   = CONTROL_STRAIGHT;
         data_to_stage2.trap     = True;
         data_to_stage2.trap_info = trap_info;
`else
	 output_stage1.ostatus   = OSTATUS_NONPIPE;
	 output_stage1.control   = CONTROL_TRAP;
         output_stage1.trap_info = trap_info;
`endif
	 output_stage1.data_to_stage2 = data_to_stage2;
      end

      // ALU outputs: pipe (straight/branch)
      // and non-pipe (CSRR_W, CSRR_S_or_C, FENCE.I, FENCE, SFENCE_VMA, xRET, WFI, TRAP)
      else begin
	 let ostatus = (  (   (alu_outputs.control == CONTROL_STRAIGHT)
			   || (alu_outputs.control == CONTROL_BRANCH)
			   || (alu_outputs.control == CONTROL_CAPBRANCH))
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
`ifdef ISA_CHERI
	    tval = getPC(rg_pcc);                   // The faulting virtual address
`else
	    tval = rg_stage_input.pc;                          // The faulting virtual address
`endif

	 let trap_info = Trap_Info_Pipe {
                                    epcc: rg_pcc,
				    exc_code: alu_outputs.exc_code,
                                    cheri_exc_code: alu_outputs.cheri_exc_code,
                                    cheri_exc_reg: alu_outputs.cheri_exc_reg,
				    tval:     tval};
`ifdef DELAY_STAGE1_TRAPS
         data_to_stage2.trap = alu_outputs.trap;
         data_to_stage2.trap_info = trap_info;
`else
	 output_stage1.trap_info      = trap_info;
`endif

	 output_stage1.ostatus        = ostatus;
	 output_stage1.control        = alu_outputs.control;
	 output_stage1.redirect       = redirect;
	 output_stage1.cf_info        = alu_outputs.cf_info;
	 output_stage1.data_to_stage2 = data_to_stage2;
      end
`ifdef ISA_CHERI
      output_stage1.next_pcc       = next_pcc_local;
`else
      output_stage1.next_pc        = next_pc_local;
`endif

      return output_stage1;
   endfunction: fv_out

   method Output_Stage1 stage1_outputs (
                                        Bool rg_full,
                                        Epoch cur_epoch,
                                        Priv_Mode cur_priv,
                                        Data_StageD_to_Stage1 rg_stage_input,
                                        PCC_T rg_pcc,
`ifdef RVFI
`ifdef ISA_CHERI
                                        CapPipe rs1_val_bypassed,
                                        CapPipe rs2_val_bypassed,
`else
                                        WordXL rs1_val_bypassed,
                                        WordXL rs2_val_bypassed,
`endif
`endif
                                        Bool rs1_busy,
                                        Bool rs2_busy,
`ifdef ISA_F
                                        Bool frs1_busy,
                                        Bool frs2_busy,
                                        Bool frs3_busy,
`endif
                                        ALU_Outputs alu_outputs
                                       );
      return fv_out (
                     rg_full,
                     cur_epoch,
                     cur_priv,
                     rg_stage_input,
                     rg_pcc,
`ifdef RVFI
                     rs1_val_bypassed,
                     rs2_val_bypassed,
`endif
                     rs1_busy,
                     rs2_busy,
`ifdef ISA_F
                     frs1_busy,
                     frs2_busy,
                     frs3_busy,
`endif
                     alu_outputs
                  );

   endmethod
endmodule
endpackage
