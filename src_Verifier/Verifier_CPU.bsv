/*-
 * Copyright (c) 2018 Jack Deeley
 * Copyright (c) 2018 Peter Rugg
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

package Verifier_CPU;

//export mkVerifier_CPU, Verif_IFC(..);

import Memory           :: *;
import GetPut           :: *;
import ClientServer     :: *;

import Verifier         :: *;
import ISA_Decls        :: *;
import RVFI_DII         :: *;

import CPU_IFC          :: *;
import Verif_IFC        :: *;
import Fabric_Defs      :: *;
import AXI4_Lite_Types  :: *;
import CPU_Globals      :: *;
import FIFOF            :: *;
import CPU              :: *;

module mkVerifier_CPU #(parameter Bit#(64) pc_reset_value) (Verif_IFC);
    
    // The core we are going to verify
    CPU_IFC core <- mkCPU(pc_reset_value);

`ifdef RVFI
`ifndef RVFI_DII
    rule displayData;
        
        RVFI_DII_Execution #(XLEN) x <- core.to_verifier.get;
        $display("[[0x%4h]] insn:0x%8h, pc:0x%8h, rd:0x%8h, mem_addr:0x%8h, mem_wdata:0x%8h",
                    x.rvfi_order,x.rvfi_insn,x.rvfi_pc_rdata[31:0],x.rvfi_rd_wdata[31:0],
                    x.rvfi_mem_addr[31:0],x.rvfi_mem_wdata[31:0]);
         //$display("[[%4d]] pc: 0x%0h, insn: 0x%0h, wmask: 0x%0h, rmask: 0x%0h,
         //           mem_rdata: 0x%0h, rs1_data: 0x%0h, rs2_data: 0x%0h", x.rvfi_order,  
         //           x.rvfi_pc_rdata, x.rvfi_insn, x.rvfi_mem_wmask, x.rvfi_mem_rmask,   
         //           x.rvfi_mem_rdata, x.rvfi_rs1_data, x.rvfi_rs2_data);             
    endrule
`endif
`endif

`ifdef INCLUDE_TANDEM_VERIF
    method ActionValue#(Info_CPU_to_Verifier) getPacket() = core.to_verifier.get;
    method Bool halted = core.halted;
`elsif RVFI
`ifdef RVFI_DII
    interface RVFI_DII_Server rvfi_dii_server = core.rvfi_dii_server;
`else
    method ActionValue#(RVFI_DII_Execution #(XLEN)) getPacket() = core.to_verifier.get;
    method Bool halted = core.halted;
`endif
`endif

    method Action external_interrupt_req (b) = core.external_interrupt_req(b);
    method Action timer_interrupt_req    (b) = core.timer_interrupt_req(b);
    method Action software_interrupt_req (b) = core.software_interrupt_req(b);
    
    interface Server hart0_server_reset = core.hart0_server_reset;
    
    interface imem_master    =  core.imem_master;
    interface dmem_master    =  core.dmem_master;
    interface near_mem_slave =  core.near_mem_slave;
    
`ifdef INCLUDE_GDB_CONTROL
    
    interface Server hart0_server_run_halt = core.hart0_server_run_halt;
    interface Put    hart0_put_other_req   = core.hart0_put_other_req;
    
    interface MemoryServer hart0_gpr_mem_server = core.hart0_gpr_mem_server;
    interface MemoryServer hart0_csr_mem_server = core.hart0_csr_mem_server;
   
`endif
    
endmodule : mkVerifier_CPU

endpackage
