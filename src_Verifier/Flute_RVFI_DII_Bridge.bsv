/*-
 * Copyright (c) 2018-2019 Peter Rugg
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

package Flute_RVFI_DII_Bridge;

// ================================================================
// BSV library imports

import FIFO         :: *;
import SpecialFIFOs :: *;
import GetPut       :: *;

// ================================================================
// Project imports

import Near_Mem_IFC :: *;
import ISA_Decls :: *;

import Verifier  :: *;
import RVFI_DII  :: *;

// ================================================================

    interface Flute_RVFI_DII_Bridge_IFC;
        interface Flute_RVFI_DII_Server rvfi_dii_server;
        interface IMem_IFC instr_CPU;
        interface Put #(Rvfi_Trace) rvfi;
    endinterface

    module mkFluteRVFIDIIBridge(Flute_RVFI_DII_Bridge_IFC);
        Reg#(Maybe#(Tuple2#(Bit#(32), Dii_Id))) instr[2] <- mkCReg(2, Invalid);
        Reg#(Maybe#(WordXL)) fake_addr <- mkReg(Invalid);
        FIFO#(RVFI_DII_Execution #(XLEN,MEMWIDTH)) reports <- mkFIFO;
        Reg#(Maybe#(Dii_Id)) seq_req[2] <- mkCReg(2, Invalid);

        Bit#(32) nop = 'h00000013;
        
        Bit#(32) instrBits = tpl_1(fromMaybe(?,instr[1]));

        interface Flute_RVFI_DII_Server rvfi_dii_server;
            interface Get seqReq;
                method ActionValue#(Dii_Id) get if (isValid(seq_req[0]));
                  return seq_req[0].Valid;
                endmethod
            endinterface
            interface Put inst;
                method Action put (x);
                  instr[0] <= Valid(x);
                  seq_req[0] <= Invalid;
                endmethod
            endinterface
            interface trace_report = toGet (reports);
        endinterface

        interface IMem_IFC instr_CPU;
            method Action req (Bit #(3) f3,
                WordXL         addr,
                Priv_Mode      priv,
                Bit #(1)       sstatus_SUM,
                Bit #(1)       mstatus_MXR,
                WordXL         satp,
                Dii_Id seq_request);
                fake_addr <= Valid(addr);
                seq_req[1] <= Valid(seq_request);
                if (isValid(instr[1])) begin
                    instr[1] <= Valid(tuple2(nop, seq_request));
                end
            endmethod

`ifdef ISA_CHERI
            method Action commit;
                //do nothing
            endmethod
`endif

            method Bool valid = isValid (fake_addr) && isValid (instr[1]);
            method Bool is_i32_not_i16 = (instrBits[1:0] == 2'b11);
            method WordXL pc = fake_addr.Valid;
            method Tuple2#(Instr, Dii_Id) instr = instr[1].Valid;
            method Bool exc = False;
            method Exc_Code exc_code = 0;
            method WordXL tval = fake_addr.Valid; //TODO adjust this for compressed instructions?
        endinterface

        interface Put rvfi = toPut(reports);
    endmodule

endpackage
