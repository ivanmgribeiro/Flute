package CPU_Stage2_syn;

import ISA_Decls     :: *;
import CPU_Globals      :: *;
import Near_Mem_IFC     :: *;
`ifdef ISA_CHERI
import CHERICap :: *;
import CHERICC_Fat :: *;
`endif
`ifdef RVFI
import Verifier  :: *;
import RVFI_DII  :: *;
`endif

interface CPU_Stage2_syn_IFC;
   (* always_enabled *)
   method Output_Stage2 stage2_outputs (Bool rg_full,
`ifdef ISA_A
                                        Bit #(5) rg_f5,
`endif
                                        Data_Stage1_to_Stage2 rg_stage2,
                                        Bool mbox_valid,
                                        WordXL mbox_word,
                                        Bool dcache_valid,
                                        Bool dcache_exc,
                                        Exc_Code dcache_exc_code,
`ifdef Near_Mem_Avalon
                                        Tuple2 #(Bool, Bit #(64)) dcache_word64
`else
                                        Tuple2 #(Bool, Bit #(128)) dcache_word128
`endif

                                       );
endinterface

`ifdef SYNTHESIZE_MODULES
(* synthesize *)
`endif
module mkCPU_Stage2_syn (CPU_Stage2_syn_IFC);
   function Output_Stage2 fv_out (Bool rg_full,
`ifdef ISA_A
                                  Bit #(5) rg_f5,
`endif
                                  Data_Stage1_to_Stage2 rg_stage2,
                                  Bool mbox_valid,
                                  WordXL mbox_word,
                                  Bool dcache_valid,
                                  Bool dcache_exc,
                                  Exc_Code dcache_exc_code,
`ifdef Near_Mem_Avalon
                                        Tuple2 #(Bool, Bit #(64)) dcache_word64
`else
                                        Tuple2 #(Bool, Bit #(128)) dcache_word128
`endif
                                 );

   let bypass_base = Bypass {bypass_state: BYPASS_RD_NONE,
			     rd:           rg_stage2.rd,
			     rd_val:       extract_cap(rg_stage2.val1)
			     };

`ifdef RVFI
   let info_RVFI_s1 = rg_stage2.info_RVFI_s1;
`endif

`ifdef RVFI
      let info_RVFI_s2_base = Data_RVFI_Stage2 {
                                                stage1:     info_RVFI_s1,
                                                mem_rmask:  0,
                                                mem_wmask:  0
                                               };
`endif

   let  trap_info_dmem = Trap_Info_Pipe {
				    exc_code: dcache_exc_code,
`ifdef ISA_CHERI
            cheri_exc_code: dcache_exc_code == exc_code_CHERI ? exc_code_CHERI_Length: exc_code_CHERI_None,
            cheri_exc_reg: ?, //TODO
            epcc: rg_stage2.pcc,
`else
            epc:  rg_stage2.pc,
`endif
				    tval: rg_stage2.addr };


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







      Output_Stage2 output_stage2 = ?;

`ifdef ISA_CHERI
     let check_enable = rg_full && rg_stage2.check_enable;
     let check_exact_enable = rg_full && rg_stage2.check_exact_enable;
     let check_success =  (!rg_stage2.check_exact_enable || rg_stage2.check_exact_success) &&
                          rg_stage2.check_address_low >= rg_stage2.authority_base &&
                          (rg_stage2.check_inclusive ? (rg_stage2.check_address_high <= rg_stage2.authority_top) : (rg_stage2.check_address_high < rg_stage2.authority_top));
`endif

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
`ifdef DELAY_STAGE1_TRAPS
      else if (rg_stage2.trap) begin
         output_stage2.ostatus = OSTATUS_NONPIPE;
         output_stage2.trap_info = rg_stage2.trap_info;
         output_stage2.data_to_stage3 = data_to_stage3_base;// TODO
         output_stage2.bypass = no_bypass;
`ifdef ISA_F
         output_stage2.fbypass = no_fbypass;
`endif
      end
`endif
      // This stage is just relaying ALU results from previous stage to next stage
      else
      if (rg_stage2.op_stage2 == OP_Stage2_ALU) begin
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

`ifdef ISA_CHERI
      else if (   (rg_stage2.op_stage2 == OP_Stage2_TestSubset)) begin
          let ostatus = OSTATUS_PIPE;
          CapReg result = nullWithAddr(zeroExtend(pack(check_success)));
          let data_to_stage3 = data_to_stage3_base;
          data_to_stage3.rd_valid = True;
          data_to_stage3.rd_val = embed_cap(result);
          let bypass = bypass_base;
          bypass.bypass_state = BYPASS_RD;
`ifdef RVFI
          let info_RVFI_s2 = info_RVFI_s2_base;
          data_to_stage3.info_RVFI_s2 = info_RVFI_s2;
          output_stage2 = Output_Stage2 {ostatus:         ostatus,
                 trap_info:       trap_info_dmem,
                 data_to_stage3:  data_to_stage3,
                 bypass:          bypass
`ifdef INCLUDE_TANDEM_VERIF
               , trace_data:      ?
`endif
                                        };
`endif
      end
`endif

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
`ifdef RV64
        match {.mem_tag, .mem_val} = dcache_word128;
`else
`ifdef Near_Mem_Avalon
        match {.mem_tag, .mem_val} = dcache_word64;
`else
        match {.mem_tag, .mem_val} = dcache_word128;
`endif
`endif
`ifdef ISA_CHERI
        CapReg result = ?;
        if (rg_stage2.mem_width_code == w_SIZE_CAP) begin
          CapMem capMem = {pack(rg_stage2.mem_allow_cap && mem_tag), truncate(mem_val)};
          result = cast(capMem);
        end else begin
          result = nullWithAddr(truncate(mem_val));
        end
`else
        WordXL result = truncate(mem_val);
`endif

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
              data_to_stage3.frd_val = fv_nanbox (truncate(mem_val));

           // A FLD result
           else
              data_to_stage3.frd_val = truncate (mem_val);
`else
           // Only FLW is a legal instruction
           data_to_stage3.frd_val = truncate (mem_val);
`endif
        end
`endif
        // GPR loads
	data_to_stage3.rd_val   = embed_cap(result);

        // Update the bypass channel, if not trapping (NONPIPE)
	let bypass = bypass_base;
`ifdef ISA_F
        // In a system with FD, the LD result may be meant for FPR or GPR
        // Check before updating the appropriate bypass channel
	let fbypass = fbypass_base;
`endif

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
`elsif RVFI
	    let info_RVFI_s2 = info_RVFI_s2_base;
        // If we're doing a load or AMO other than SC, we need to set the read mask.
        if((rg_stage2.op_stage2 == OP_Stage2_LD)
`ifdef ISA_A
            ||((rg_stage2.op_stage2 == OP_Stage2_AMO) && (rg_f5 != f5_AMO_SC))
`endif
        ) begin
            info_RVFI_s2.mem_rmask = getMemMask({0,rg_stage2.mem_width_code},rg_stage2.addr);
        end
`ifdef ISA_A
`ifdef ISA_CHERI
        WordXL int_ret_val = getAddr(result);
`else
        WordXL int_ret_val = result;
`endif
        // If we're doing an AMO that's not an LR, we need to set the write mask as well.
        if (rg_stage2.op_stage2 == OP_Stage2_AMO && rg_f5 != f5_AMO_LR) begin
            // For most AMOs we can just go ahead and do it
            if (rg_f5 != f5_AMO_SC) begin
                info_RVFI_s2.mem_wmask = getMemMask(rg_stage2.mem_width_code,rg_stage2.addr);
                match {.new_ld_val,
                       .new_st_val} = fn_amo_op (rg_stage2.mem_width_code,
                                                 rg_f5,
                                                 rg_stage2.addr,
                                                 unpack(pack(toMem(result))),
                                                 tuple2(False, zeroExtend(rg_stage2.info_RVFI_s1.mem_wdata))
                                                );
                info_RVFI_s2.stage1.mem_wdata = truncate(pack(tpl_2(new_st_val)));
            // For SC however we do need to check that it was successful, otherwise we've not written.
            end else begin
                info_RVFI_s2.mem_wmask = ((int_ret_val != 0) ? getMemMask(rg_stage2.mem_width_code,rg_stage2.addr) : 0);
            end
        end
        data_to_stage3.info_RVFI_s2 = info_RVFI_s2;
`endif
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

`ifdef RVFI
`ifdef ISA_CHERI
	 data_to_stage3.rd_val   = embed_cap(nullCap);
`else
	 data_to_stage3.rd_val   = 0;
`endif
	 let info_RVFI_s2 = info_RVFI_s2_base;
	 info_RVFI_s2.mem_wmask = getMemMask(rg_stage2.mem_width_code,rg_stage2.addr);
	 data_to_stage3.info_RVFI_s2 = info_RVFI_s2;
`else
	 data_to_stage3.rd_val   = ?;
`endif

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
`elsif RVFI
	 // No memory op, so very simple.
	 let info_RVFI_s2 = info_RVFI_s2_base;
	 data_to_stage3.info_RVFI_s2 = info_RVFI_s2;
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
	 data_to_stage3.rd_val   = embed_int(result);

	 let bypass = bypass_base;
	 bypass.bypass_state = ((ostatus == OSTATUS_PIPE) ? BYPASS_RD_RDVAL : BYPASS_RD);
`ifdef ISA_CHERI
	 bypass.rd_val       = nullWithAddr(result);
`else
	 bypass.rd_val       = result;
`endif

`ifdef INCLUDE_TANDEM_VERIF
	 let trace_data            = rg_stage2.trace_data;
	 trace_data.word1          = result;
	 data_to_stage3.trace_data = trace_data;
`elsif RVFI
	 // No memory op, so very simple.
	 let info_RVFI_s2 = info_RVFI_s2_base;
	 data_to_stage3.info_RVFI_s2 = info_RVFI_s2;
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
            fbypass.rd_val          = truncate(value);
`endif
         end

         // result is meant for a GPR
         else begin
            bypass.bypass_state     = ((ostatus==OSTATUS_PIPE) ? BYPASS_RD_RDVAL
                                                               : BYPASS_RD);
`ifdef RV64
            bypass.rd_val           = nullWithAddr(value);
            data_to_stage3.rd_val   = embed_int(value);
`else
            bypass.rd_val           = nullWithAddr(truncate(value));
            data_to_stage3.rd_val   = embed_int(truncate(value));
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
`elsif RVFI
	 // No memory op, so very simple.
	 let info_RVFI_s2 = info_RVFI_s2_base;
	 data_to_stage3.info_RVFI_s2 = info_RVFI_s2;
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
`ifdef ISA_CHERI
      let  trap_info_capbounds = Trap_Info_Pipe {epcc:    rg_stage2.pcc,
                                                 exc_code: exc_code_CHERI,
                                                 cheri_exc_code: check_success ? exc_code_CHERI_Precision : exc_code_CHERI_Length,
                                                 cheri_exc_reg: rg_stage2.check_authority_idx,
                                                 tval: rg_stage2.check_address_low };
      output_stage2.check_success = check_enable && check_success;
      if ((check_enable && !check_success) || (check_exact_enable && !rg_stage2.check_exact_success)) begin
         output_stage2.ostatus = OSTATUS_NONPIPE;
         output_stage2.trap_info = trap_info_capbounds;
      end
`endif
      return output_stage2;
   endfunction

   method Output_Stage2 stage2_outputs (Bool rg_full,
`ifdef ISA_A
                                        Bit #(5) rg_f5,
`endif
                                        Data_Stage1_to_Stage2 rg_stage2,
                                        Bool mbox_valid,
                                        WordXL mbox_word,
                                        Bool dcache_valid,
                                        Bool dcache_exc,
                                        Exc_Code dcache_exc_code,
`ifdef Near_Mem_Avalon
                                        Tuple2 #(Bool, Bit #(64)) dcache_word64
`else
                                        Tuple2 #(Bool, Bit #(128)) dcache_word128
`endif
                                       );
      return fv_out (rg_full,
`ifdef ISA_A
                     rg_f5,
`endif
                     rg_stage2,
                     mbox_valid,
                     mbox_word,
                     dcache_valid,
                     dcache_exc,
                     dcache_exc_code,
`ifdef Near_Mem_Avalon
                     dcache_word64
`else
                     dcache_word128
`endif
                    );

   endmethod
endmodule

endpackage
