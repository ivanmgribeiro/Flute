/*
 * Copyright (c) 2019 Peter Rugg
 * All rights reserved.
 *
 * This software was developed by SRI International and the University of
 * Cambridge Computer Laboratory (Department of Computer Science and
 * Technology) under DARPA contract HR0011-18-C-0016 ("ECATS"), as part of the
 * DARPA SSITH research programme.
 *
 * @BERI_LICENSE_HEADER_START@
 *
 * Licensed to BERI Open Systems C.I.C. (BERI) under one or more contributor
 * license agreements.  See the NOTICE file distributed with this work for
 * additional information regarding copyright ownership.  BERI licenses this
 * file to you under the BERI Hardware-Software License, Version 1.0 (the
 * "License"); you may not use this file except in compliance with the
 * License.  You may obtain a copy of the License at:
 *
 *   http://www.beri-open-systems.org/legal/license-1-0.txt
 *
 * Unless required by applicable law or agreed to in writing, Work distributed
 * under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR
 * CONDITIONS OF ANY KIND, either express or implied.  See the License for the
 * specific language governing permissions and limitations under the License.
 *
 * @BERI_LICENSE_HEADER_END@
 */


`ifdef ISA_CHERI

typedef TMul#(XLEN, 2) CLEN;

typedef enum {
   CHERI_ADDR_CHECK_SOURCE_OP1,
   CHERI_ADDR_CHECK_SOURCE_OP1_ADDR,
   CHERI_ADDR_CHECK_SOURCE_OP1_ADDR_MASKED,
   CHERI_ADDR_CHECK_SOURCE_OP2_BOUNDS,
   CHERI_ADDR_CHECK_SOURCE_OP2_ADDR,
   CHERI_ADDR_CHECK_SOURCE_OP2_ADDR_MASKED,
   CHERI_ADDR_CHECK_SOURCE_OP2_KIND,
   CHERI_ADDR_CHECK_SOURCE_SUM,
   CHERI_ADDR_CHECK_SOURCE_SUM_WIDTH
} CHERI_Addr_Check_Source deriving (Bits, FShow, Eq);

typedef struct {
   Bool check_op1_tagged;              Bool check_op2_tagged;
   Bool check_op1_sealed_with_type;    Bool check_op2_sealed_with_type;
   Bool check_op1_unsealed;            Bool check_op2_unsealed;
   Bool check_op1_unsealed_or_sentry;  Bool check_op2_unsealed_or_sentry;
   Bool check_op1_op2_types_match;
   Bool check_op1_permit_ccall;        Bool check_op2_permit_ccall;
   Bool check_op1_permit_x;            Bool check_op2_permit_x;
   Bool check_op2_no_permit_x;
   Bool check_op2_permit_unseal;
   Bool check_op2_permit_seal;
   Bool check_op2_points_to_op1_type;
   Bool check_op2_addr_valid_type;
   Bool check_op2_perm_subset_op1;
   Bool check_op1_permit_load;         Bool check_op2_permit_load;
   Bool check_op1_permit_load_cap;     Bool check_op2_permit_load_cap; 
   Bool check_op1_permit_store;        Bool check_op2_permit_store;
   Bool check_op1_permit_store_cap;    Bool check_op2_permit_store_cap;
   Bool check_op2_derivable;

   Bit #(6) cheri_op1_id;
   Bit #(6) cheri_op2_id;

   Bool check_enable;
   CHERI_Addr_Check_Source cheri_addr_check_source_low;
   CHERI_Addr_Check_Source cheri_addr_check_source_high;
} CHERI_Cap_Checks deriving (Bits, FShow, Eq);

typedef enum {
   CHERI_OP_SOURCE_DDC,
   CHERI_OP_SOURCE_PCC,
   CHERI_OP_SOURCE_CS1,
   CHERI_OP_SOURCE_CS2
} CHERI_Op_Source deriving (Bits, FShow, Eq);

typedef struct {
   CHERI_Op_Source cheri_op1_source;
   CHERI_Op_Source cheri_op2_source;
   CHERI_Op_Source cheri_authority_source;
} CHERI_Op_Sources deriving (Bits, FShow, Eq);

typedef enum {
   CHERI_NONE,
   CHERI_CLEAR_TAG,
   CHERI_COPY_TYPE,
   CHERI_CJALR,
   CHERI_SET_OFFSET,
   CHERI_SET_BOUNDS,
   CHERI_SET_ADDR,
   CHERI_SET_KIND,
   CHERI_SET_KIND_CONDITIONAL,
   CHERI_SET_KIND_AND_VALID,
   CHERI_AND_PERMS,
   CHERI_SET_FLAG,
   CHERI_GET_ADDR,
   CHERI_GET_LENGTH,
   CHERI_GET_BASE,
   CHERI_GET_TAG,
   CHERI_GET_KIND,
   CHERI_GET_SEALED,
   CHERI_GET_OFFSET,
   CHERI_GET_FLAGS,
   CHERI_GET_PERMS,
   CHERI_GET_PRECISION,
   CHERI_TEST_CONDITIONAL,
   CHERI_C_TO_PTR,
   CHERI_LOAD_CAP,
   CHERI_STORE_CAP,
   CHERI_CCALL,
   CHERI_ALU_SUM_OUTPUT
} CHERI_Operation_Select deriving (Bits, FShow, Eq);

typedef struct {
   Bool alu_offset_inc_not_set;
   Bool alu_bounds_exact;
   Bool alu_bounds_inclusive;
   Bit #(6) alu_authority_id;
   Bool alu_val1_cap_not_int;
   Bool alu_val2_cap_not_int;
   Bool alu_crrl_not_cram;
   Bool alu_seal_entry;
   Bool alu_check_misaligned;
   Bool alu_offset_conditional;
   Bool alu_mem_unsigned;
   Bit #(3) alu_mem_width_code;
   Bool alu_illegal_instr;
   Bool alu_add_pcc_base_to_imm; // needed in order to calculate the address that we
                                 // will be jumping to in a JALR
   Bool alu_add_pcc_addr_to_imm;
   Bool alu_add_ddc_addr_to_imm; // used for ddc-relative loads and stores, allows us
                                 // to save an adder in the ALU which could be on the
                                 // critical path
   Bool alu_ccall_rd;
} CHERI_ALU_Control deriving (Bits, FShow, Eq);

//function Tuple2 #(CHERI_Op_Sources, CHERI_Cap_Checks) fn_get_cheri_op_sources_and_checks (Instr instr);
function Tuple4 #(CHERI_Op_Sources, CHERI_Cap_Checks, CHERI_Operation_Select, CHERI_ALU_Control) fn_cheri_decode (Instr instr, Bit #(1) pcc_cap_mode_bit);
   CHERI_Cap_Checks cap_checks = CHERI_Cap_Checks {
      check_op1_tagged:             False,  check_op2_tagged:           False,
      check_op1_sealed_with_type:   False,  check_op2_sealed_with_type: False,
      check_op1_unsealed:           False,  check_op2_unsealed:         False,
      check_op1_unsealed_or_sentry: False,  check_op2_unsealed_or_sentry: False,
      check_op1_op2_types_match:    False,
      check_op1_permit_ccall:       False,  check_op2_permit_ccall:     False,
      check_op1_permit_x:           False,  check_op2_permit_x:           False,
      check_op2_no_permit_x:        False,
      check_op2_permit_unseal:      False,
      check_op2_permit_seal:        False,
      check_op2_points_to_op1_type: False,
      check_op2_addr_valid_type:    False,
      check_op2_perm_subset_op1:    False,
      check_op1_permit_load:        False,  check_op2_permit_load:      False,
      check_op1_permit_load_cap:    False,  check_op2_permit_load_cap:  False,
      check_op1_permit_store:       False,  check_op2_permit_store:     False,
      check_op1_permit_store_cap:   False,  check_op2_permit_store_cap: False,
      check_op2_derivable: False,

      cheri_op1_id: ?,
      cheri_op2_id: ?,

      check_enable: False,
      cheri_addr_check_source_low: ?,
      cheri_addr_check_source_high: ?
   };

   // op1_source will be used as the source for EX_ALU's internal_op1
   // TODO need to set up something for internal_op2
   CHERI_Op_Sources cheri_op_sources = CHERI_Op_Sources {
      cheri_op1_source: CHERI_OP_SOURCE_CS1,
      cheri_op2_source: CHERI_OP_SOURCE_CS2,
      cheri_authority_source: CHERI_OP_SOURCE_CS1
   };

   CHERI_ALU_Control cheri_alu_control = CHERI_ALU_Control {
      alu_offset_inc_not_set: False,
      alu_bounds_exact: False,
      alu_bounds_inclusive: False,
      alu_authority_id: 0,
      alu_val1_cap_not_int: False,
      alu_val2_cap_not_int: False,
      alu_crrl_not_cram: False,
      alu_seal_entry: False,
      alu_check_misaligned: False,
      alu_offset_conditional: False,
      alu_mem_unsigned: False,
      alu_mem_width_code: 0,
      alu_illegal_instr: False,
      alu_add_ddc_addr_to_imm: False,
      alu_add_pcc_addr_to_imm: False,
      alu_add_pcc_base_to_imm: False,
      alu_ccall_rd: False
   };

   CHERI_Operation_Select cheri_operation_select = CHERI_NONE;

   let opcode = instr_opcode (instr);
   let rs1 = instr_rs1 (instr);
   let rs2 = instr_rs2 (instr);
   let funct5rs2 = instr_rs2 (instr);
   let rd  = instr_rd  (instr);
   let funct5rd  = instr_rd  (instr);
   let funct3 = instr_funct3 (instr);
   let funct7 = instr_funct7 (instr);

   // TODO check_enable

   if (opcode == op_BRANCH) begin
      cheri_op_sources.cheri_op1_source = CHERI_OP_SOURCE_PCC;
      cheri_op_sources.cheri_authority_source = CHERI_OP_SOURCE_PCC;
      // cap_checks.check_enabled is conditional on whether we take the branch or not
      cap_checks.cheri_addr_check_source_low = CHERI_ADDR_CHECK_SOURCE_SUM;
      cap_checks.cheri_addr_check_source_high = CHERI_ADDR_CHECK_SOURCE_SUM_WIDTH;
      cheri_alu_control.alu_mem_width_code = 1;
      cheri_alu_control.alu_bounds_inclusive = True;
      cheri_alu_control.alu_authority_id = {1'b0, scr_addr_PCC};
   end else if (opcode == op_JAL) begin
      cheri_op_sources.cheri_op1_source = CHERI_OP_SOURCE_PCC;
      cheri_op_sources.cheri_authority_source = CHERI_OP_SOURCE_PCC;
      cap_checks.check_enable = True;
      cap_checks.cheri_addr_check_source_low = CHERI_ADDR_CHECK_SOURCE_SUM;
      cap_checks.cheri_addr_check_source_high = CHERI_ADDR_CHECK_SOURCE_SUM_WIDTH;
      cheri_alu_control.alu_mem_width_code = 1;
      cheri_alu_control.alu_bounds_inclusive = True;
      cheri_alu_control.alu_authority_id = {1'b0, scr_addr_PCC};
   end else if (opcode == op_JALR) begin
      cheri_op_sources.cheri_op1_source = CHERI_OP_SOURCE_PCC;
      cheri_op_sources.cheri_authority_source = CHERI_OP_SOURCE_PCC;
      cap_checks.check_enable = True;
      cap_checks.cheri_addr_check_source_low = CHERI_ADDR_CHECK_SOURCE_SUM;
      cap_checks.cheri_addr_check_source_high = CHERI_ADDR_CHECK_SOURCE_SUM_WIDTH;
      cheri_alu_control.alu_mem_width_code = 1;
      cheri_alu_control.alu_bounds_inclusive = True;
      cheri_alu_control.alu_authority_id = {1'b0, scr_addr_PCC};


      cheri_alu_control.alu_add_pcc_base_to_imm = True;
   end else if (opcode == op_AUIPC) begin
      if (pcc_cap_mode_bit == 1'b1) begin
         // TODO currently in the ALU the PCC won't have an offset.
         cheri_op_sources.cheri_op1_source = CHERI_OP_SOURCE_PCC;
         cheri_operation_select = CHERI_SET_OFFSET;
         cheri_alu_control.alu_offset_inc_not_set = False;
         cheri_alu_control.alu_val1_cap_not_int = True;
         cheri_alu_control.alu_add_pcc_addr_to_imm = True;
      end
   end else if (  opcode == op_LOAD
               || opcode == op_MISC_MEM && valueOf (XLEN) == 64 && funct3 == f3_LQ) begin
      Bool useDDC = pcc_cap_mode_bit == 1'b0;
      cheri_op_sources.cheri_op1_source = useDDC ? CHERI_OP_SOURCE_DDC : CHERI_OP_SOURCE_CS1;
      // TODO
      // currently the address calculation for this is incorrect
      // in useDDC mode, this does not currently add the offset of DDC
      cheri_op_sources.cheri_authority_source = useDDC ? CHERI_OP_SOURCE_DDC : CHERI_OP_SOURCE_CS1;

      let width_code = zeroExtend (funct3[1:0]);
      if (opcode == op_MISC_MEM && valueOf (XLEN) == 64 && funct3 == f3_LQ) begin
         width_code = w_SIZE_Q;
      end

      cap_checks.check_op1_tagged = True;
      cap_checks.check_op1_unsealed = True;
      cap_checks.check_op1_permit_load = True;
      cap_checks.check_op1_permit_load_cap = width_code == w_SIZE_CAP;

      cap_checks.cheri_op1_id = useDDC ? {1'b1, scr_addr_DDC} : {1'b0, rs1};
      cap_checks.check_enable = True;
      cap_checks.cheri_addr_check_source_low = CHERI_ADDR_CHECK_SOURCE_SUM;
      cap_checks.cheri_addr_check_source_high = CHERI_ADDR_CHECK_SOURCE_SUM_WIDTH;
      cheri_alu_control.alu_mem_width_code = width_code;
      cheri_alu_control.alu_mem_unsigned = funct3[2] == 1'b1;
      cheri_alu_control.alu_add_ddc_addr_to_imm = useDDC;
   end else if (opcode == op_STORE) begin
      Bool useDDC = pcc_cap_mode_bit == 1'b0;
      cheri_op_sources.cheri_op1_source = useDDC ? CHERI_OP_SOURCE_DDC : CHERI_OP_SOURCE_CS1;
      // TODO
      // currently the address calculation for this is incorrect
      // in useDDC mode, this does not currently add the offset of DDC
      cheri_op_sources.cheri_authority_source = useDDC ? CHERI_OP_SOURCE_DDC : CHERI_OP_SOURCE_CS1;

      let width_code = zeroExtend (funct3[1:0]);

      cap_checks.check_op1_tagged = True;
      cap_checks.check_op1_unsealed = True;
      cap_checks.check_op1_permit_store = True;
      cap_checks.check_op1_permit_store_cap = width_code == w_SIZE_CAP;

      cap_checks.cheri_op1_id = useDDC ? {1'b1, scr_addr_DDC} : {1'b0, rs1};
      cap_checks.check_enable = True;
      cap_checks.cheri_addr_check_source_low = CHERI_ADDR_CHECK_SOURCE_SUM;
      cap_checks.cheri_addr_check_source_high = CHERI_ADDR_CHECK_SOURCE_SUM_WIDTH;
      cheri_alu_control.alu_mem_width_code = width_code;
      cheri_alu_control.alu_mem_unsigned = ?;
      cheri_alu_control.alu_add_ddc_addr_to_imm = useDDC;
   end else if (opcode == op_cap_Manip) begin
   case (funct3)
   f3_cap_CIncOffsetImmediate: begin
      cheri_op_sources.cheri_op1_source = CHERI_OP_SOURCE_CS1;
      cap_checks.check_op1_unsealed = True;
      cap_checks.cheri_op1_id = {1'b0, rs1};
      cheri_operation_select = CHERI_SET_OFFSET;
      cheri_alu_control.alu_offset_inc_not_set = True;

      cheri_alu_control.alu_val1_cap_not_int = True;

      // TODO
      // this can come from: immediate
      //                        in the case of an AUIPC
      //                                           this uses SET_OFFSET
      //                                        a CIncOffsetImmediate
      //                                           this uses SET_OFFSET
      //                                        a CSetBoundsImmediate
      //                                           this uses SET_BOUNDS
      //                     rs2
      //                        in the case of a CSetBounds
      //                                          this uses SET_BOUNDS
      //                                       a CSetBoundsExact
      //                                          this uses SET_BOUNDS
      //                                       a CSetOffset
      //                                          this uses SET_OFFSET
      //                                       a CSetAddr
      //                                          this uses SET_ADDR
      //                                       a CIncOffset
      //                                          this uses SET_OFFSET
      //                                       a CFromPtr
      //                                          this uses SET_OFFSET
      //                     otype
      //                        in the case of a CCopyType tagged with SEALED_WITH_TYPE
      //                                          this uses SET_ADDR
      //                     fallthru_pc
      //                        in the case of a CJALR
      //                                          this uses SET_OFFSET
      // can just make this always come from regular riscv operand cs2
      //internal_op2_source = immediate;
   end
   f3_cap_CSetBoundsImmediate: begin
      cheri_op_sources.cheri_op1_source = CHERI_OP_SOURCE_CS1;
      cheri_op_sources.cheri_authority_source = CHERI_OP_SOURCE_CS1;
      cap_checks.check_op1_tagged = True;
      cap_checks.check_op1_unsealed = True;
      cap_checks.cheri_op1_id = {1'b0, rs1};
      cheri_operation_select = CHERI_SET_BOUNDS;
      cheri_alu_control.alu_bounds_exact = False;
      cheri_alu_control.alu_authority_id = zeroExtend (rs1);

      cheri_alu_control.alu_val1_cap_not_int = True;
      cheri_alu_control.alu_bounds_inclusive = True;

      cap_checks.check_enable = True;
      cap_checks.cheri_addr_check_source_low = CHERI_ADDR_CHECK_SOURCE_OP1_ADDR;
      cap_checks.cheri_addr_check_source_high = CHERI_ADDR_CHECK_SOURCE_SUM;

      // TOD
      //internal_op2_source = immediate;
   end
   f3_cap_ThreeOp: begin
      case (funct7)
      f7_cap_CSpecialRW: begin
         if (rs2 == scr_addr_PCC && rs1 == 0) begin
            cheri_op_sources.cheri_op1_source = CHERI_OP_SOURCE_PCC;
            cheri_alu_control.alu_val1_cap_not_int = True;
            cheri_operation_select = CHERI_NONE;
         end else if (rs2 == scr_addr_DDC && rs1 == 0) begin
            cheri_op_sources.cheri_op1_source = CHERI_OP_SOURCE_DDC;
            cheri_alu_control.alu_val1_cap_not_int = True;
            cheri_operation_select = CHERI_NONE;
         end else begin
            cheri_op_sources.cheri_op1_source = CHERI_OP_SOURCE_CS1;
            cheri_alu_control.alu_val1_cap_not_int = True;
            cheri_operation_select = CHERI_NONE;
            //cheri_alu_control.alu_control   = CONTROL_SCR_W;
            // TODO
            // do i want to move control to decode or keep it in the ALU?
            // branch instructions need to work out control in ALU
            //cap_val1_source = c1_val;
         end
      end
      f7_cap_CSetBounds: begin
         cheri_op_sources.cheri_op1_source = CHERI_OP_SOURCE_CS1;
         cheri_op_sources.cheri_authority_source = CHERI_OP_SOURCE_CS1;
         cap_checks.check_op1_tagged = True;
         cap_checks.check_op1_unsealed = True;
         cap_checks.cheri_op1_id = {1'b0, rs1};
         cheri_operation_select = CHERI_SET_BOUNDS;
         cheri_alu_control.alu_authority_id = zeroExtend (rs1);
         cheri_alu_control.alu_bounds_exact = False;

         cheri_alu_control.alu_val1_cap_not_int = True;
         cheri_alu_control.alu_bounds_inclusive = True;

         cap_checks.check_enable = True;
         cap_checks.cheri_addr_check_source_low = CHERI_ADDR_CHECK_SOURCE_OP1_ADDR;
         cap_checks.cheri_addr_check_source_high = CHERI_ADDR_CHECK_SOURCE_SUM;

         // TOD
         //internal_op2_source = rs2_val; // non-cap
      end
      f7_cap_CSetBoundsExact: begin
         cheri_op_sources.cheri_op1_source = CHERI_OP_SOURCE_CS1;
         cheri_op_sources.cheri_authority_source = CHERI_OP_SOURCE_CS1;
         cap_checks.check_op1_tagged = True;
         cap_checks.check_op1_unsealed = True;
         cap_checks.cheri_op1_id = {1'b0, rs1};
         cheri_operation_select = CHERI_SET_BOUNDS;
         cheri_alu_control.alu_authority_id = zeroExtend (rs1);
         cheri_alu_control.alu_bounds_exact = True;

         cheri_alu_control.alu_val1_cap_not_int = True;
         cheri_alu_control.alu_bounds_inclusive = True;

         cap_checks.check_enable = True;
         cap_checks.cheri_addr_check_source_low = CHERI_ADDR_CHECK_SOURCE_OP1_ADDR;
         cap_checks.cheri_addr_check_source_high = CHERI_ADDR_CHECK_SOURCE_SUM;
         // TOD
         //internal_op2_source = rs2_val; // non-cap
      end
      f7_cap_CSetOffset: begin
         cheri_op_sources.cheri_op1_source = CHERI_OP_SOURCE_CS1;
         cheri_op_sources.cheri_authority_source = CHERI_OP_SOURCE_CS1;
         cheri_alu_control.alu_authority_id = {1'b0, rs1};
         cap_checks.check_op1_unsealed = True;
         cap_checks.cheri_op1_id = {1'b0, rs1};
         cheri_operation_select = CHERI_SET_OFFSET;
         cheri_alu_control.alu_offset_inc_not_set = False;

         cheri_alu_control.alu_val1_cap_not_int = True;

         // TOD
         //internal_op1_source = cs1_val;
         //internal_op2_source = rs2_val;
      end
      f7_cap_CSetAddr: begin
         cheri_op_sources.cheri_op1_source = CHERI_OP_SOURCE_CS1;
         cheri_op_sources.cheri_authority_source = CHERI_OP_SOURCE_CS1;
         cheri_alu_control.alu_authority_id = {1'b0, rs1};
         cap_checks.check_op1_unsealed = True;
         cap_checks.cheri_op1_id = {1'b0, rs1};
         cheri_operation_select = CHERI_SET_ADDR;

         cheri_alu_control.alu_val1_cap_not_int = True;

         // TOD
         //internal_op2_source = rs2_val;
      end
      f7_cap_CIncOffset: begin
         cheri_op_sources.cheri_op1_source = CHERI_OP_SOURCE_CS1;
         cheri_op_sources.cheri_authority_source = CHERI_OP_SOURCE_CS1;
         cheri_alu_control.alu_authority_id = {1'b0, rs1};
         cap_checks.check_op1_unsealed = True;
         cap_checks.cheri_op1_id = {1'b0, rs1};
         cheri_operation_select = CHERI_SET_OFFSET;
         cheri_alu_control.alu_offset_inc_not_set = True;

         cheri_alu_control.alu_val1_cap_not_int = True;

         // TOD
         //internal_op1_source = cs1_val;
         //internal_op2_source = rs2_val;
      end
      f7_cap_CSeal: begin
         cheri_op_sources.cheri_op1_source = CHERI_OP_SOURCE_CS1;
         cheri_op_sources.cheri_op2_source = CHERI_OP_SOURCE_CS2;
         cheri_op_sources.cheri_authority_source = CHERI_OP_SOURCE_CS2;

         cap_checks.check_op1_tagged = True;
         cap_checks.check_op2_tagged = True;
         cap_checks.check_op1_unsealed = True;
         cap_checks.check_op2_unsealed = True;
         cap_checks.check_op2_permit_seal = True;
         cap_checks.check_op2_addr_valid_type = True;
         cap_checks.cheri_op1_id = {1'b0, rs1};
         cap_checks.cheri_op2_id = {1'b0, rs2};

         cheri_alu_control.alu_authority_id = zeroExtend (rs2);
         cheri_alu_control.alu_val1_cap_not_int = True;
         cheri_alu_control.alu_bounds_inclusive = False;

         cap_checks.check_enable = True;
         cap_checks.cheri_addr_check_source_low = CHERI_ADDR_CHECK_SOURCE_OP2_ADDR;
         cap_checks.cheri_addr_check_source_high = CHERI_ADDR_CHECK_SOURCE_OP2_ADDR;

         cheri_operation_select = CHERI_SET_KIND;
         // TODO SHARE_SEAL
         // TODO maybe this can be moved later? could have a SEAL val1_source
         //alu_outputs.cap_val1 = setKind(cs1_val, SEALED_WITH_TYPE(truncate(getAddr(cs2_val))));
      end
      // TODO all after this
      f7_cap_CCSeal: begin
         cheri_op_sources.cheri_op1_source = CHERI_OP_SOURCE_CS1;
         cheri_op_sources.cheri_op2_source = CHERI_OP_SOURCE_CS2;
         cheri_op_sources.cheri_authority_source = CHERI_OP_SOURCE_CS2;
         cheri_alu_control.alu_authority_id = zeroExtend (rs2);
         cheri_alu_control.alu_bounds_inclusive = False;
         cheri_alu_control.alu_val1_cap_not_int = True;
         cap_checks.check_op1_tagged = True;
         cap_checks.cheri_op1_id = {1'b0, rs1};

         cap_checks.cheri_addr_check_source_low = CHERI_ADDR_CHECK_SOURCE_OP2_ADDR;
         cap_checks.cheri_addr_check_source_high = CHERI_ADDR_CHECK_SOURCE_OP2_ADDR;

         cheri_operation_select = CHERI_SET_KIND_CONDITIONAL;
         // TODO
         // TODO ALU_CHECK_ADDR
         //if (  (! isValidCap(cs2_val))
         //   || (getAddr(cs2_val) == otype_unsealed_ext)
         //   || (getKind(cs1_val) != UNSEALED)
         //   ) begin
         //   alu_outputs.cap_val1 = cs1_val;
         //end else begin
         //   alu_outputs.check_enable = True;
         //   check_cs1_unsealed = True;
         //   check_cs2_unsealed = True;
         //   check_cs2_addr_valid_type = True;
         //   check_cs2_permit_seal = True;
         //   // TODO SHARE_SEAL
         //   // TODO maybe this can be moved later? could have a SEAL val1_source
         //   alu_outputs.cap_val1 = setKind(cs1_val, SEALED_WITH_TYPE(truncate(getAddr(cs2_val))));
         //end
      end
      f7_cap_TwoSrc: begin
         case (rd)
            rd_cap_CCall: begin
               cheri_op_sources.cheri_op1_source = CHERI_OP_SOURCE_CS1;
               cheri_op_sources.cheri_op2_source = CHERI_OP_SOURCE_CS2;
               cheri_op_sources.cheri_authority_source = CHERI_OP_SOURCE_CS1;
               cheri_alu_control.alu_authority_id = zeroExtend (rs1);
               cap_checks.check_op1_tagged = True;
               cap_checks.check_op2_tagged = True;
               cap_checks.check_op1_sealed_with_type = True;
               cap_checks.check_op2_sealed_with_type = True;
               cap_checks.check_op1_op2_types_match = True;
               cap_checks.check_op1_permit_x = True;
               cap_checks.check_op2_no_permit_x = True;
               cap_checks.check_op1_permit_ccall = True;
               cap_checks.check_op2_permit_ccall = True;
               cap_checks.cheri_op1_id = {1'b0, rs1};
               cap_checks.cheri_op2_id = {1'b0, rs2};

               cheri_alu_control.alu_val1_cap_not_int = True;

               cap_checks.check_enable = True;
               cap_checks.cheri_addr_check_source_low = CHERI_ADDR_CHECK_SOURCE_OP1_ADDR_MASKED;
               // TODO op2 is already carrying the new type... can't really put the +2 there
               cap_checks.cheri_addr_check_source_high = CHERI_ADDR_CHECK_SOURCE_SUM;
               cheri_alu_control.alu_check_misaligned = True;
               cheri_operation_select = CHERI_CCALL;
               cheri_alu_control.alu_ccall_rd = True;
               //cheri_alu_control.alu_control = CONTROL_CAPBRANCH;

               ////check_address_low = target;
               ////addop1 = {target, 1'b0};
               ////addop2 = {     2, 1'b0};
               //// TODO
               //// TODO SHARE_SEAL
               //// TODO maybe this can be moved later? could have a SEAL val1_source
               ////alu_outputs.cap_val1 = setKind(cs2_val, UNSEALED);
               //alu_outputs.rd = cCallRD;
               //alu_outputs.pcc = fromCapPipe(maskAddr(setKind(cs1_val, UNSEALED), signExtend(2'b10)));
               ////alu_outputs.pcc = fromCapPipe(maskAddr(cs1_val, signExtend(2'b10)));
               //WordXL target = {truncateLSB(getAddr(cs1_val)), 1'b0};
               ////alu_outputs = checkValidJump(alu_outputs, True, cs1_val, cs1_base, zeroExtend(inputs.rs1_idx), target);
            end
         default: begin
            cheri_alu_control.alu_illegal_instr = True;
//`ifdef DELAY_STAGE1_TRAPS
//            alu_outputs.trap    = True;
//            alu_outputs.control = CONTROL_STRAIGHT;
//`else
//            alu_outputs.control = CONTROL_TRAP;
//`endif
         end
         endcase // inputs.decoded_instr.rd
      end
      f7_cap_CUnseal: begin
         cheri_op_sources.cheri_op1_source = CHERI_OP_SOURCE_CS1;
         cheri_op_sources.cheri_op2_source = CHERI_OP_SOURCE_CS2;
         cheri_op_sources.cheri_authority_source = CHERI_OP_SOURCE_CS2;
         cheri_alu_control.alu_authority_id = zeroExtend (rs2);
         cap_checks.check_op1_tagged = True;
         cap_checks.check_op2_tagged = True;
         cap_checks.check_op1_sealed_with_type = True;
         cap_checks.check_op2_unsealed = True;
         cap_checks.check_op2_points_to_op1_type = True;
         cap_checks.check_op2_permit_unseal = True;
         cap_checks.cheri_op1_id = {1'b0, rs1};
         cap_checks.cheri_op2_id = {1'b0, rs2};

         cheri_alu_control.alu_bounds_inclusive = False;
         cheri_alu_control.alu_val1_cap_not_int = True;

         cap_checks.check_enable = True;
         cap_checks.cheri_addr_check_source_low = CHERI_ADDR_CHECK_SOURCE_OP2_ADDR;
         cap_checks.cheri_addr_check_source_high = CHERI_ADDR_CHECK_SOURCE_OP2_ADDR;

         cheri_operation_select = CHERI_SET_KIND;

         // TODO SHARE_SEAL
         // TODO maybe this can be moved later? could have a SEAL val1_source
         //alu_outputs.cap_val1 = setKind(cs1_val, UNSEALED);
      end
      f7_cap_CTestSubset: begin
         Bool useDDC = rs1 == 0;
         cheri_op_sources.cheri_op1_source = useDDC ? CHERI_OP_SOURCE_DDC : CHERI_OP_SOURCE_CS1;
         cheri_op_sources.cheri_op2_source = CHERI_OP_SOURCE_CS2;
         cheri_op_sources.cheri_authority_source = useDDC ? CHERI_OP_SOURCE_DDC : CHERI_OP_SOURCE_CS1;

         cap_checks.cheri_addr_check_source_low = CHERI_ADDR_CHECK_SOURCE_OP2_BOUNDS;
         cap_checks.cheri_addr_check_source_high = CHERI_ADDR_CHECK_SOURCE_OP2_BOUNDS;
         cheri_alu_control.alu_bounds_inclusive = True;
         cheri_operation_select = CHERI_TEST_CONDITIONAL;

         // TODO
         //if (  isValidCap(local_cs1_val) == isValidCap(cs2_val)
         //   && ((getPerms(cs2_val) & getPerms(local_cs1_val)) == getPerms(cs2_val))
         //   ) begin
         //   alu_outputs.check_enable = False; // We do not require the check to pass to avoid a trap
         //   // TODO ALU_CHECK_ADDR
         //   alu_outputs.op_stage2 = OP_Stage2_TestSubset;
         //end else begin
         //   alu_outputs.val1 = zeroExtend(pack(False));
         //end
      end
      f7_cap_CCopyType: begin
         cheri_op_sources.cheri_op1_source = CHERI_OP_SOURCE_CS1;
         cheri_op_sources.cheri_op2_source = CHERI_OP_SOURCE_CS2;
         cheri_op_sources.cheri_authority_source = CHERI_OP_SOURCE_CS1;
         cheri_alu_control.alu_authority_id = zeroExtend (rs1);
         cap_checks.check_op1_tagged = True;
         cap_checks.check_op1_unsealed = True;
         cap_checks.cheri_op1_id = {1'b0, rs1};

         cheri_alu_control.alu_bounds_inclusive = False;
         cheri_alu_control.alu_val1_cap_not_int = True;

         cap_checks.cheri_addr_check_source_low = CHERI_ADDR_CHECK_SOURCE_OP2_KIND;
         cap_checks.cheri_addr_check_source_high = CHERI_ADDR_CHECK_SOURCE_OP2_KIND;
         //check_address_low = zeroExtend(otype);
         //check_address_high = zeroExtend(otype);

         //cheri_operation_select = CHERI_SET_ADDR;
         cheri_operation_select = CHERI_COPY_TYPE;

         // TODO
         //case (getKind(cs2_val)) matches
         //   tagged UNSEALED: begin
         //      alu_outputs.val1 = otype_unsealed_ext;
         //   end
         //   tagged SENTRY: begin
         //      alu_outputs.val1 = otype_sentry_ext;
         //   end
         //   tagged RES0: begin
         //      alu_outputs.val1 = otype_res0_ext;
         //   end
         //   tagged RES1: begin
         //      alu_outputs.val1 = otype_res1_ext;
         //   end
         //   tagged SEALED_WITH_TYPE .otype: begin
         //      alu_outputs.val1_source = SET_ADDR;
         //      cheri_alu_control.alu_val1_cap_not_int = True;
         //      alu_outputs.internal_op2 = zeroExtend(otype);

         //      alu_outputs.check_enable = True;

         //      // TODO ALU_CHECK_ADDR
         //   end
         //endcase // getKind (cs2_val)
      end
      f7_cap_CAndPerm: begin
         cheri_op_sources.cheri_op1_source = CHERI_OP_SOURCE_CS1;
         cap_checks.check_op1_tagged = True;
         cap_checks.check_op1_unsealed = True;
         cap_checks.cheri_op1_id = {1'b0, rs1};
         cheri_alu_control.alu_val1_cap_not_int = True;
         cheri_operation_select = CHERI_AND_PERMS;

         // TODO
         // TODO SHARE_AND_PERMS
         //alu_outputs.cap_val1 = setPerms(cs1_val, pack(getPerms(cs1_val)) & truncate(rs2_val));
      end
      f7_cap_CSetFlags: begin
         cheri_op_sources.cheri_op1_source = CHERI_OP_SOURCE_CS1;
         cap_checks.check_op1_unsealed = True;
         cap_checks.cheri_op1_id = {1'b0, rs1};
         cheri_alu_control.alu_val1_cap_not_int = True;
         cheri_operation_select = CHERI_SET_FLAG;

         // TODO
         // TODO SHARE_SET_FLAGS
         //alu_outputs.cap_val1 = setFlags(cs1_val, truncate(rs2_val));
      end
      f7_cap_CToPtr: begin
         Bool useDDC = rs2 == 0;
         cheri_op_sources.cheri_op1_source = CHERI_OP_SOURCE_CS1;
         cheri_op_sources.cheri_op2_source = useDDC ? CHERI_OP_SOURCE_DDC : CHERI_OP_SOURCE_CS2;
         cap_checks.check_op2_tagged = True;
         cap_checks.check_op1_unsealed = True;
         cap_checks.cheri_op1_id = {1'b0, rs1};
         cap_checks.cheri_op2_id = useDDC ? {1'b1, scr_addr_DDC} : {1'b0, rs2};

         cheri_operation_select = CHERI_C_TO_PTR;

         // TODO
         // could maybe replace this if with ANDing the result with 32{isValidCap(cs1_val))}
         //if (isValidCap(cs1_val)) begin
         //   //alu_outputs.val1 = zeroExtend(getAddr(cs1_val) - (inputs.rs2_idx == 0 ? ddc_base : cs2_base));
         //   // TODO set this below
         //   cheri_operation_select = CHERI_C_TO_PTR;
         //   addop1 = {getAddr (cs1_val), 1'b1};
         //   addop2 = {~(useDDC ? ddc_base : cs2_base), 1'b1};
         //end else begin
         //end
      end
      f7_cap_CFromPtr: begin
         Bool useDDC = rs1 == 0;
         cheri_op_sources.cheri_op1_source = useDDC ? CHERI_OP_SOURCE_DDC : CHERI_OP_SOURCE_CS1;
         cheri_alu_control.alu_offset_inc_not_set = False;
         cheri_alu_control.alu_val1_cap_not_int = True;
         cheri_operation_select = CHERI_SET_OFFSET;
         cheri_alu_control.alu_offset_conditional = True;

         // TODO
         //alu_outputs.internal_op2 = rs2_val;
      end
      f7_cap_CSub: begin
         cheri_operation_select = CHERI_ALU_SUM_OUTPUT;
         //alu_outputs.val1 = zeroExtend(getAddr(cs1_val) - getAddr(cs2_val));
         // TODO
         //addop1 = { (getAddr (cs1_val)), 1'b1};
         //addop2 = {~(getAddr (cs2_val)), 1'b1};
      end
      f7_cap_CBuildCap: begin
         Bool useDDC = rs1 == 0;
         cheri_op_sources.cheri_op1_source = useDDC ? CHERI_OP_SOURCE_DDC : CHERI_OP_SOURCE_CS1;
         cheri_op_sources.cheri_op2_source = CHERI_OP_SOURCE_CS2;
         cheri_op_sources.cheri_authority_source = useDDC ? CHERI_OP_SOURCE_DDC : CHERI_OP_SOURCE_CS1;
         cheri_alu_control.alu_authority_id = useDDC ? {1, scr_addr_DDC} : zeroExtend (rs1);
         cap_checks.check_op1_tagged = True;
         cap_checks.check_op1_unsealed = True;
         cap_checks.check_op2_perm_subset_op1 = True;
         cap_checks.cheri_op1_id = useDDC ? {1, scr_addr_DDC} : {1'b0, rs1};
         cap_checks.cheri_op2_id = {1'b0, rs2};

         cheri_alu_control.alu_bounds_inclusive = True;
         cheri_alu_control.alu_val1_cap_not_int = True;

         cap_checks.check_enable = True;
         cap_checks.cheri_addr_check_source_low = CHERI_ADDR_CHECK_SOURCE_OP2_BOUNDS;
         cap_checks.cheri_addr_check_source_high = CHERI_ADDR_CHECK_SOURCE_OP2_BOUNDS;
         cap_checks.check_op2_derivable = True;

         cheri_operation_select = CHERI_SET_KIND_AND_VALID;
         //let result = setValidCap(cs2_val, True);
         //alu_outputs.cap_val1 = setKind(result, getKind(cs2_val) == SENTRY ? SENTRY : UNSEALED); // Preserve sentries

         //if (!isDerivable(cs2_val)) begin
         //   alu_outputs = fv_CHERI_exc(alu_outputs, zeroExtend(inputs.rs2_idx), exc_code_CHERI_Length);
         //end
      end
      f7_cap_Loads: begin
         // this first section is fully based exclusively on the current instruction
         Bool useDDC = rs2[3] == cap_mem_ddc;

         Bool is_lr = False;
         Bool is_unsigned = rs2[2] == cap_mem_unsigned && rs2[4] == 1'b0;
         Bool illegal = False;

         Bit#(3) widthCode = zeroExtend(rs2[1:0]);
         if (rs2[4] == 1'b1) begin
            if (rs2[2:0] == 3'b111) begin
               widthCode = w_SIZE_Q;
            end else begin
`ifdef ISA_A
               // TODO set this
               // is_lr = True;
               widthCode = rs2[2:0];
`else
               illegal = True;
`endif
            end
         end

         cheri_op_sources.cheri_op1_source = useDDC ? CHERI_OP_SOURCE_DDC : CHERI_OP_SOURCE_CS1;
         cheri_op_sources.cheri_authority_source = useDDC ? CHERI_OP_SOURCE_DDC : CHERI_OP_SOURCE_CS1;

         cap_checks.cheri_addr_check_source_low  = CHERI_ADDR_CHECK_SOURCE_SUM;
         cap_checks.cheri_addr_check_source_high = CHERI_ADDR_CHECK_SOURCE_SUM_WIDTH;
         cheri_alu_control.alu_mem_width_code = widthCode;
         cheri_alu_control.alu_bounds_inclusive = True;
         cheri_alu_control.alu_add_ddc_addr_to_imm = useDDC;

         if (rs2[4] == 1'b1) begin
            if (rs2[2:0] == 3'b111) begin
               widthCode = w_SIZE_Q;
            end else begin
`ifdef ISA_A
               is_lr = True;
               widthCode = rs2[2:0];
`else
               illegal = True;
`endif
            end
         end
         if ((widthCode > w_SIZE_MAX) || (is_unsigned && widthCode == w_SIZE_MAX)) begin
            illegal = True;
         end

         if (!illegal) begin
            cheri_alu_control.alu_authority_id = useDDC ? {1,scr_addr_DDC} : {0,rs1};
            cap_checks.check_op1_tagged = True;
            cap_checks.check_op1_unsealed = True;
            cap_checks.check_op1_permit_load = True;
            cap_checks.check_op1_permit_load_cap = widthCode == w_SIZE_CAP;
            cap_checks.cheri_op1_id = useDDC ? {1, scr_addr_DDC} : {1'b0, rs1};

            cap_checks.check_enable = True;

            cheri_alu_control.alu_val2_cap_not_int = widthCode == w_SIZE_CAP;

            cheri_alu_control.alu_mem_unsigned   = is_unsigned;

            cheri_operation_select = CHERI_LOAD_CAP;
         end

         cheri_alu_control.alu_illegal_instr = illegal;

         // TODO
         if (illegal) begin
            cheri_alu_control.alu_illegal_instr = True;
            // exc_code defaults to exc_code_ILLEGAL_INSTRUCTION
//`ifdef DELAY_STAGE1_TRAPS
//            alu_outputs.trap    = True;
//            alu_outputs.control = CONTROL_STRAIGHT;
//`else
//            alu_outputs.control = CONTROL_TRAP;
//`endif
         end else begin
            //alu_outputs = memCommon(alu_outputs, False, is_unsigned, funct5rs2[3] == cap_mem_ddc, widthCode, inputs.ddc, cs1_val, inputs.rs1_idx, ?, is_lr, {f5_AMO_LR, 2'b0});
            //let eaddr = getAddr(addr) + (useDDC ? getAddr(ddc) : 0);

            // TODO
            //addop1 = {         getAddr (   cs1_val)    , 1'b0};
            //addop2 = {useDDC ? getAddr (inputs.ddc) : 0, 1'b0};
            //let op_stage2 = False ? OP_Stage2_ST : OP_Stage2_LD;
`ifdef ISA_A
            //if (is_amo) op_stage2 = OP_Stage2_AMO;
`endif

            //width code must be checked externally

            //alu_outputs.op_stage2      = op_stage2;
            // TODO move this stuff below? need to decide what needs moved
            //alu_outputs.val1           = zeroExtend({f5_AMO_LR, 2'b0});
            //alu_outputs.val2           = zeroExtend(getAddr(data)); //for stores
            //alu_outputs.cap_val2       = data;


            //// TODO inline this
            ////alu_outputs = checkValidDereference(alu_outputs, authority, authorityIdx, eaddr, widthCode, isStoreNotLoad, !isStoreNotLoad, data);
         end
      end
      f7_cap_Stores: begin
         Bool useDDC = funct5rd[3] == cap_mem_ddc;

         let widthCode = funct5rd[2:0];

         cheri_op_sources.cheri_op1_source = useDDC ? CHERI_OP_SOURCE_DDC : CHERI_OP_SOURCE_CS1;
         cheri_op_sources.cheri_op2_source = CHERI_OP_SOURCE_CS2;
         cheri_op_sources.cheri_authority_source = useDDC ? CHERI_OP_SOURCE_DDC : CHERI_OP_SOURCE_CS1;
         cheri_alu_control.alu_authority_id = useDDC ? {1, scr_addr_DDC} : {0, rs1};

         cap_checks.cheri_addr_check_source_low = CHERI_ADDR_CHECK_SOURCE_SUM;
         cap_checks.cheri_addr_check_source_high = CHERI_ADDR_CHECK_SOURCE_SUM_WIDTH;
         cheri_alu_control.alu_mem_width_code = widthCode;
         cheri_alu_control.alu_bounds_inclusive = True;
         cheri_alu_control.alu_mem_unsigned = ?;
         cheri_alu_control.alu_add_ddc_addr_to_imm = useDDC;

         Bool is_sc = funct5rd[4] == 1'b1;
         Bool illegal = False;
         if (is_sc) begin
`ifdef ISA_A
            alu_outputs.rd = rs2;
`else
            illegal = True;
`endif
         end
         if (widthCode > w_SIZE_MAX) illegal = True;

         if (!illegal) begin
            cap_checks.check_op1_tagged = True;
            cap_checks.check_op1_unsealed = True;
            cap_checks.check_op1_permit_store = True;
            cap_checks.check_op1_permit_store_cap = widthCode == w_SIZE_CAP;
            cap_checks.cheri_op1_id = useDDC ? {1, scr_addr_DDC} : {1'b0, rs1};

            cap_checks.check_enable = True;
            cheri_operation_select = CHERI_STORE_CAP;

            cheri_alu_control.alu_val2_cap_not_int = widthCode == w_SIZE_CAP;
         end

         cheri_alu_control.alu_illegal_instr = illegal;
            // exc_code defaults to exc_code_ILLEGAL_INSTRUCTION
//`ifdef DELAY_STAGE1_TRAPS
//            alu_outputs.trap    = True;
//            alu_outputs.control = CONTROL_STRAIGHT;
//`else
//            alu_outputs.control = CONTROL_TRAP;
//`endif
         if (!illegal) begin
            //alu_outputs = memCommon(alu_outputs, True, ?, funct5rd[3] == cap_mem_ddc, widthCode, inputs.ddc, cs1_val, inputs.rs1_idx, cs2_val, is_sc, {f5_AMO_SC, 2'b0});
            //let eaddr = getAddr(addr) + (useDDC ? getAddr(ddc) : 0);
            //addop1 = {         getAddr (cs1_val), 1'b0};
            //addop2 = {useDDC ? getAddr (inputs.ddc) : 0, 1'b0};
//            let op_stage2 = OP_Stage2_ST;
//`ifdef ISA_A
//            if (is_amo) op_stage2 = OP_Stage2_AMO;
//`endif

            //width code must be checked externally

            //alu_outputs.op_stage2      = op_stage2;
            //// TODO move this stuff later
            //alu_outputs.val1           = zeroExtend({f5_AMO_SC, 2'b0});
            //alu_outputs.val2           = zeroExtend(getAddr(data)); //for stores
            //alu_outputs.cap_val2       = data;

            // 
            //alu_outputs = checkValidDereference(alu_outputs, authority, authorityIdx, eaddr, widthCode, isStoreNotLoad, !isStoreNotLoad, data);
         end
      end
      f7_cap_TwoOp: begin
         case (rs2)
         f5rs2_cap_CGetLen: begin
            cheri_op_sources.cheri_op1_source = CHERI_OP_SOURCE_CS1;
            cheri_operation_select = CHERI_GET_LENGTH;
            
            // TODO
            //Bit#(XLEN) length = truncate(getLength(cs1_val));
            //alu_outputs.val1 = zeroExtend(length);
         end
         f5rs2_cap_CGetBase: begin
            cheri_op_sources.cheri_op1_source = CHERI_OP_SOURCE_CS1;
            cheri_operation_select = CHERI_GET_BASE;
            
            // TODO
            //alu_outputs.val1 = zeroExtend(cs1_base);
         end
         f5rs2_cap_CGetTag: begin
            cheri_op_sources.cheri_op1_source = CHERI_OP_SOURCE_CS1;
            cheri_operation_select = CHERI_GET_TAG;

            // TODO
            //alu_outputs.val1 = zeroExtend(pack(isValidCap(cs1_val)));
         end
         f5rs2_cap_CGetSealed: begin
            cheri_op_sources.cheri_op1_source = CHERI_OP_SOURCE_CS1;
            cheri_operation_select = CHERI_GET_SEALED;

            // TODO
            //alu_outputs.val1 = zeroExtend(pack(getKind(cs1_val) != UNSEALED));
         end
         f5rs2_cap_CRRL: begin
            cheri_op_sources.cheri_op1_source = CHERI_OP_SOURCE_CS1;
            cheri_operation_select = CHERI_GET_PRECISION;
            cheri_alu_control.alu_crrl_not_cram = True;
         end
         f5rs2_cap_CRAM: begin
            cheri_op_sources.cheri_op1_source = CHERI_OP_SOURCE_CS1;
            cheri_operation_select = CHERI_GET_PRECISION;
            cheri_alu_control.alu_crrl_not_cram = False;
         end
         f5rs2_cap_CMove: begin
            cheri_op_sources.cheri_op1_source = CHERI_OP_SOURCE_CS1;
            cheri_operation_select = CHERI_NONE;
            cheri_alu_control.alu_val1_cap_not_int = True;
         end
         f5rs2_cap_CClearTag: begin
            cheri_op_sources.cheri_op1_source = CHERI_OP_SOURCE_CS1;
            cheri_operation_select = CHERI_CLEAR_TAG;
            cheri_alu_control.alu_val1_cap_not_int = True;
         end
         f5rs2_cap_CGetAddr: begin
            cheri_op_sources.cheri_op1_source = CHERI_OP_SOURCE_CS1;
            cheri_operation_select = CHERI_GET_ADDR;
         end
         f5rs2_cap_CSealEntry: begin
            cheri_op_sources.cheri_op1_source = CHERI_OP_SOURCE_CS1;
            cap_checks.check_op1_tagged = True;
            cap_checks.check_op1_unsealed = True;
            cap_checks.check_op1_permit_x = True;
            cap_checks.cheri_op1_id = {1'b0, rs1};
            cheri_alu_control.alu_val1_cap_not_int = True;

            cheri_operation_select = CHERI_SET_KIND;

            // TODO
            // TODO SHARE_SEAL
            //alu_outputs.cap_val1 = setKind(cs1_val, SENTRY);
         end
         f5rs2_cap_CGetOffset: begin
            cheri_op_sources.cheri_op1_source = CHERI_OP_SOURCE_CS1;
            cheri_operation_select = CHERI_GET_OFFSET;
         end
         f5rs2_cap_CGetFlags: begin
            cheri_op_sources.cheri_op1_source = CHERI_OP_SOURCE_CS1;
            cheri_operation_select = CHERI_GET_FLAGS;
         end
         f5rs2_cap_CGetPerm: begin
            cheri_op_sources.cheri_op1_source = CHERI_OP_SOURCE_CS1;
            cheri_operation_select = CHERI_GET_PERMS;
         end
         f5rs2_cap_CJALR: begin
            // TODO:
            //    
            // TODO care needs to be taken for this:
            //    CJALR needs to call a setOffset on PCC
            //    maybe op2_source should be CS1? this would avoid a mux before
            //    the setOffset
            //    this is the only exception to the general rule that internal_op1 can just be op1
            cheri_op_sources.cheri_op1_source = CHERI_OP_SOURCE_PCC;
            // note that unlike in other instruction decodings, op2_source here is being set
            // as CS1.
            // The idea when this was done was because in all other cases, the ALU CHERI
            // operations are performed with op1 as their major operand. in order to avoid
            // muxing between op1 and op2 in the ALU, we simply put the CJALR operand in
            // op1_source and put CS1 in op2_source
            // however, this does mean that the authority is in op2_source rather than op1_source.
            // it might be interesting to see whether swapping these (ie having CS1 in op1_source and
            // pcc in op2_source) would have any effect on performance or area - the effect would probably
            // be minimal
            cheri_op_sources.cheri_op2_source = CHERI_OP_SOURCE_CS1;
            cheri_op_sources.cheri_authority_source = CHERI_OP_SOURCE_CS1;
            cheri_alu_control.alu_authority_id = zeroExtend (rs1);

            cap_checks.check_op2_tagged = True;
            cap_checks.check_op2_unsealed_or_sentry = True;
            cap_checks.check_op2_permit_x = True;
            cap_checks.cheri_op1_id = {1'b1, scr_addr_PCC};
            cap_checks.cheri_op2_id = {1'b0, rs1};

            //cheri_operation_select = CHERI_SET_OFFSET;
            cheri_operation_select = CHERI_CJALR;
            cheri_alu_control.alu_val1_cap_not_int = True;

            cheri_alu_control.alu_offset_inc_not_set = False;
            cheri_alu_control.alu_seal_entry = True;
            cheri_alu_control.alu_bounds_inclusive = True;
            cheri_alu_control.alu_check_misaligned = True;
            // TODO should be word-sized when ISA_C is not defined
            cheri_alu_control.alu_mem_width_code = w_SIZE_H;

            cap_checks.check_enable = True;
            cap_checks.cheri_addr_check_source_low = CHERI_ADDR_CHECK_SOURCE_OP2_ADDR_MASKED;
            cap_checks.cheri_addr_check_source_high = CHERI_ADDR_CHECK_SOURCE_SUM_WIDTH;
            //cheri_alu_control.alu_control   = CONTROL_CAPBRANCH;

            // TODO
            //Addr  next_pc   = cs1_offset;
            //Addr  ret_pc    = fallthru_pc;

            //let maskedTarget = maskAddr(cs1_val, signExtend(2'b10));

            ////let pcc_addr = getAddr(toCapPipe(inputs.pcc));
            //let pcc_pc = getPC (inputs.pcc);
            ////let target_addr = getPCCBase(inputs.pcc) + next_pc;
            //// TODO move this stuff later
            //let cf_info   = CF_Info {cf_op       : CF_JALR,
            //                         from_PC     : pcc_pc,
            //                         taken       : True,
            //                         fallthru_PC : fallthru_pcc_pc,
            //                         taken_PC    : getAddr(maskedTarget) };

            //next_pc[0] = 1'b0;

            //alu_outputs.cf_info   = cf_info;

            //alu_outputs.addr      = next_pc;
            //alu_outputs.pcc       = fromCapPipe(setKind(maskedTarget, UNSEALED));
            //alu_outputs.internal_op1 = toCapPipe(inputs.pcc);
            // TODO
            //alu_outputs.internal_op1 = toCapPipeNoOffset (inputs.pcc);
            //alu_outputs.internal_op2 = fallthru_pc;

            // TODO inline this
            //alu_outputs = checkValidJump(alu_outputs, True, cs1_val, cs1_base, {0,inputs.rs1_idx}, getAddr(maskedTarget));
//            WordXL target = getAddr (maskedTarget);
//`ifdef ISA_C
//            Bool misaligned_target = cs1_base[0] != 1'b0;
//`else
//            Bool misaligned_target = (target [1] == 1'b1) || (cs1_base[1:0] != 2'b0);
//`endif
//            if (misaligned_target && True) begin
//`ifdef DELAY_STAGE1_TRAPS
//                alu_outputs.trap    = True;
//                alu_outputs.control = CONTROL_STRAIGHT;
//`else
//                alu_outputs.control = CONTROL_TRAP;
//`endif
//                alu_outputs.exc_code = exc_code_INSTR_ADDR_MISALIGNED;
//            end

         end
         f5rs2_cap_CGetType: begin
            cheri_op_sources.cheri_op1_source = CHERI_OP_SOURCE_CS1;
            cheri_operation_select = CHERI_GET_KIND;
         end
         default: begin
            cheri_alu_control.alu_illegal_instr = True;
         end
      endcase // funct5rs2
      end
   default: begin
         cheri_alu_control.alu_illegal_instr = True;
   end
   endcase // funct7
   end
   default: begin
      cheri_alu_control.alu_illegal_instr = True;
      end
      endcase // funct3
   end





   return tuple4 (cheri_op_sources, cap_checks, cheri_operation_select, cheri_alu_control);
endfunction




function Bit #(5) instr_cap_funct5rs2 (Instr x); return x [24:20]; endfunction

function Bit #(5) instr_cap_funct5rd (Instr x); return x [11:7]; endfunction

function Instr mkInstr_Cap_type (Bit #(7) funct7, Bit #(5) funct5rs2, RegName rs1, Bit #(3) funct3, RegName rd, Bit #(7) opcode);
    let instr = { funct7, funct5rs2, rs1, funct3, rd, opcode };
    return instr;
endfunction

function Instr mkInstr_Cap_Store_type (Bit#(7) funct7, RegName rs2, RegName rs1, Bit #(3) funct3, Bit #(5) funct5rd, Bit #(7) opcode);
    let inst = { funct7, rs2, rs1, funct3, funct5rd, opcode };
    return inst;
endfunction

// Exception codes

typedef Bit #(5) CHERI_Exc_Code;

CHERI_Exc_Code exc_code_CHERI_None         = 0;
CHERI_Exc_Code exc_code_CHERI_Length       = 1;
CHERI_Exc_Code exc_code_CHERI_Tag          = 2;
CHERI_Exc_Code exc_code_CHERI_Seal         = 3;
CHERI_Exc_Code exc_code_CHERI_Type         = 4;
CHERI_Exc_Code exc_code_CHERI_Call         = 5;
CHERI_Exc_Code exc_code_CHERI_Return       = 6;
CHERI_Exc_Code exc_code_CHERI_Underflow    = 7;
CHERI_Exc_Code exc_code_CHERI_Software     = 8;
CHERI_Exc_Code exc_code_CHERI_TLB          = 9;
CHERI_Exc_Code exc_code_CHERI_Precision    = 10;
CHERI_Exc_Code exc_code_CHERI_Global       = 16;
CHERI_Exc_Code exc_code_CHERI_XPerm        = 17;
CHERI_Exc_Code exc_code_CHERI_RPerm        = 18;
CHERI_Exc_Code exc_code_CHERI_WPerm        = 19;
CHERI_Exc_Code exc_code_CHERI_LCPerm       = 20;
CHERI_Exc_Code exc_code_CHERI_SCPerm       = 21;
CHERI_Exc_Code exc_code_CHERI_SCLocalPerm  = 22;
CHERI_Exc_Code exc_code_CHERI_SealPerm     = 23;
CHERI_Exc_Code exc_code_CHERI_SysRegsPerm  = 24;
CHERI_Exc_Code exc_code_CHERI_CCallPerm    = 25;
CHERI_Exc_Code exc_code_CHERI_CCallIDCPerm = 26;
CHERI_Exc_Code exc_code_CHERI_UnsealPerm   = 27;

typedef struct {
  Bit #(6) cheri_exc_reg;
  CHERI_Exc_Code cheri_exc_code;
  } XCCSR
deriving(Bits);

function WordXL capexc_to_xccsr(XCCSR xccsr);
  return zeroExtend({xccsr.cheri_exc_reg, xccsr.cheri_exc_code, 3'b0, 1'b1, 1'b1});
endfunction

function WordXL capexc_to_xtval(XCCSR xccsr);
  return zeroExtend({xccsr.cheri_exc_reg, xccsr.cheri_exc_code});
endfunction

// SCR map

typedef Bit#(5) SCR_Addr;

SCR_Addr scr_addr_PCC = 0;
SCR_Addr scr_addr_DDC = 1;

SCR_Addr scr_addr_UTCC = 4;
SCR_Addr scr_addr_UTDC = 5;
SCR_Addr scr_addr_UScatchC = 6;
SCR_Addr scr_addr_UEPCC = 7;

SCR_Addr scr_addr_STCC = 12;
SCR_Addr scr_addr_STDC = 13;
SCR_Addr scr_addr_SScratchC = 14;
SCR_Addr scr_addr_SEPCC = 15;

SCR_Addr scr_addr_MTCC = 28;
SCR_Addr scr_addr_MTDC = 29;
SCR_Addr scr_addr_MScratchC = 30;
SCR_Addr scr_addr_MEPCC = 31;

function CapPipe update_scr_via_csr (CapPipe old_scr, WordXL new_csr, Bool allow_sealed);
    let new_scr = setOffset(old_scr, new_csr);
    let ret = new_scr.value;
    if (!new_scr.exact || (getKind(old_scr) != UNSEALED && !allow_sealed)) begin
        ret = setValidCap(ret, False);
    end
    return ret;
endfunction

RegName cCallRD = 31;

// Instruction field encodings

// Top-level opcodes
Opcode   op_cap_Manip = 7'h5b;
//Opcode   op_cap_Mem   = 7'h0b; // Not yet implemented

// ================================================================
// op_cap_Manip opcode subdivision

// f3 selects between immediate and 3-reg instructions
Bit #(3) f3_cap_ThreeOp             = 3'h0;
Bit #(3) f3_cap_CIncOffsetImmediate = 3'h1;
Bit #(3) f3_cap_CSetBoundsImmediate = 3'h2;
// 3'h3-3'h7 unused

// ================================================================
// op_cap_ThreeOp opcode subdivision

// f7 selects between 3-reg operations

// 7'h00 unused
Bit #(7) f7_cap_CSpecialRW      = 7'h01;
// 7'h02-7'h07 unused
Bit #(7) f7_cap_CSetBounds      = 7'h08;
Bit #(7) f7_cap_CSetBoundsExact = 7'h09;
// 7'h0a unused
Bit #(7) f7_cap_CSeal           = 7'h0b;
Bit #(7) f7_cap_CUnseal         = 7'h0c;
Bit #(7) f7_cap_CAndPerm        = 7'h0d;
Bit #(7) f7_cap_CSetFlags       = 7'h0e;
Bit #(7) f7_cap_CSetOffset      = 7'h0f;
Bit #(7) f7_cap_CSetAddr        = 7'h10;
Bit #(7) f7_cap_CIncOffset      = 7'h11;
Bit #(7) f7_cap_CToPtr          = 7'h12;
Bit #(7) f7_cap_CFromPtr        = 7'h13;
Bit #(7) f7_cap_CSub            = 7'h14;
// 7'h15-7'h1c unused
Bit #(7) f7_cap_CBuildCap       = 7'h1d;
Bit #(7) f7_cap_CCopyType       = 7'h1e;
Bit #(7) f7_cap_CCSeal          = 7'h1f;
Bit #(7) f7_cap_CTestSubset     = 7'h20;
// 7'h21-7'hfb unused
Bit #(7) f7_cap_Stores          = 7'h7c;
Bit #(7) f7_cap_Loads           = 7'h7d;
Bit #(7) f7_cap_TwoSrc          = 7'h7e;
Bit #(7) f7_cap_TwoOp           = 7'h7f;

// ================================================================
// f7_cap_TwoSrc opcode subdivision

// rd selects between 2-reg operations

// 5'h00 unused
Bit #(5) rd_cap_CCall          = 5'h01;
// 5'h02-5'h1f unused

// ================================================================
// f7_cap_TwoOp opcode subdivision

// f5rs2 selects between 2-reg operations (f5rs2 instead of f5 because f5
//        is already used in RISC-V and is in a different position

Bit #(5) f5rs2_cap_CGetPerm    = 5'h00;
Bit #(5) f5rs2_cap_CGetType    = 5'h01;
Bit #(5) f5rs2_cap_CGetBase    = 5'h02;
Bit #(5) f5rs2_cap_CGetLen     = 5'h03;
Bit #(5) f5rs2_cap_CGetTag     = 5'h04;
Bit #(5) f5rs2_cap_CGetSealed  = 5'h05;
Bit #(5) f5rs2_cap_CGetOffset  = 5'h06;
Bit #(5) f5rs2_cap_CGetFlags   = 5'h07;
Bit #(5) f5rs2_cap_CRRL        = 5'h08;
Bit #(5) f5rs2_cap_CRAM        = 5'h09;
Bit #(5) f5rs2_cap_CMove       = 5'h0a;
Bit #(5) f5rs2_cap_CClearTag   = 5'h0b;
Bit #(5) f5rs2_cap_CJALR       = 5'h0c;
Bit #(5) f5rs2_cap_CClearReg   = 5'h0d;
// 5'h0e unused
Bit #(5) f5rs2_cap_CGetAddr    = 5'h0f;
Bit #(5) f5rs2_cap_CClearFPReg = 5'h10;
Bit #(5) f5rs2_cap_CSealEntry  = 5'h11;
// 5'h12-5'h1f unused (5'h1f reserved for 1-reg instructions)

// ================================================================
// f7_cap_{Load, Store} opcode subdivision

MemReqSize cap_mem_SIZE_B = 'h0;
MemReqSize cap_mem_SIZE_H = 'h1;
MemReqSize cap_mem_SIZE_W = 'h2;
MemReqSize cap_mem_SIZE_D = 'h3;
//MemReqSize f5rs2_cap_mem_SIZE_Q = 'h4; //TODO

Bit #(1) cap_mem_ddc = 1'h0;
Bit #(1) cap_mem_cap = 1'h1;

Bit #(1) cap_mem_unsigned = 1'h1;
Bit #(1) cap_mem_signed = 1'h0;

// ================================================================
// Other:

// Region in MISC_MEM for LQ
Bit #(3) f3_LQ = 3'h2;
Bit #(3) f3_SQ = 3'b100;

`ifdef RV64
Bit #(3) w_SIZE_CAP = w_SIZE_Q;
Bit #(3) w_SIZE_MAX = w_SIZE_Q;
`else //RV32
Bit #(3) w_SIZE_CAP = w_SIZE_D;
Bit #(3) w_SIZE_MAX = w_SIZE_D;
`endif

Bit #(3) f3_AMO_CAP = w_SIZE_CAP;

// Special cases of Otypes that are extended to XLEN
Bit #(XLEN) otype_unsealed_ext = -1;
Bit #(XLEN) otype_sentry_ext = -2;
Bit #(XLEN) otype_res0_ext = -3;
Bit #(XLEN) otype_res1_ext = -4;

`endif
