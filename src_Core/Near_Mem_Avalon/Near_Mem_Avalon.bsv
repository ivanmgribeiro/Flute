package Near_Mem_Avalon;

import Cur_Cycle :: *;

import ISA_Decls :: *;
import Near_Mem_IFC :: *;
import Near_Mem_Avalon_Common :: *;
import ClientServer :: *;
import GetPut :: *;


(* synthesize *)
module mkNear_Mem (Near_Mem_IFC);

   // whether the current inputs are valid
   //Wire #(Bool)        dw_data_valid <- mkDWire (False);
   Reg #(Bool)        rg_data_valid[2] <- mkCReg (2, False);

   // registers to hold current response
   // these stay the same until a new response is received
   Reg #(Bit #(XLEN)) rg_data_readdata[2] <- mkCReg (2, 0);
   Reg #(Bool)        rg_data_pending[3] <- mkCReg (3, False);
   Reg #(Bit #(2))    rg_data_response[2] <- mkCReg (2, 0);

   // registers to hold current request
   // these stay the same until a new request is made
   Reg #(Addr)                rg_data_addr[2]       <- mkCRegU (2);
   Reg #(Bit #(XLEN))         rg_data_writedata[2]  <- mkCRegU (2);
   Reg #(Bit #(Bytes_per_WordXL)) rg_data_byteenable[2] <- mkCRegU (2);
   Reg #(Bool)                rg_data_write[2]      <- mkCReg (2, False);
   Reg #(Bool)                rg_data_read[2]       <- mkCReg (2, False);

   Reg #(Bool)                rg_data_waitrequest[2] <- mkCReg (2, False);
   Reg #(Bool)                rg_data_waitrequest_delayed[2] <- mkCReg (2, False);




   // whether the current inputs are valid
   //Wire #(Bool)        dw_instr_valid <- mkDWire (False);
   Reg #(Bool)        rg_instr_valid[2] <- mkCReg (2, False);

   // registers to hold current response
   // these stay the same until a new response is received
   Reg #(Instr)       rg_instr_readdata[2] <- mkCReg (2, 0);
   Reg #(Bool)        rg_instr_pending[3] <- mkCReg (3, False);
   Reg #(Bit #(2))    rg_instr_response[2] <- mkCReg (2, 0);

   // registers to hold current request
   // these stay the same until a new request is made
   Reg #(Addr)                rg_instr_addr[2]       <- mkCRegU (2);
   Reg #(Bit #(XLEN))         rg_instr_writedata[2]  <- mkCRegU (2);
   Reg #(Bit #(Bytes_per_WordXL)) rg_instr_byteenable[2] <- mkCRegU (2);
   Reg #(Bool)                rg_instr_write[2]      <- mkCReg (2, False);
   Reg #(Bool)                rg_instr_read[2]       <- mkCReg (2, False);

   Reg #(Bool)                rg_instr_waitrequest[2] <- mkCReg (2, False);
   Reg #(Bool)                rg_instr_waitrequest_delayed[2] <- mkCReg (2, False);




   interface Server server_reset;
      interface Put request;
         method Action put (Token t);
            rg_instr_pending[2] <= False;
            rg_data_pending[2] <= False;
            // TODO might have to reset other registers here?
            // in theory shouldn't be necessary, since they should only be read
            // when the "valid" is asserted, and this should only happen after
            // a request has been responded to (in which case the registers will have
            // been correctly updated)
         endmethod
      endinterface

      interface Get response;
         method ActionValue #(Token) get ();
            return ?;
         endmethod
      endinterface
   endinterface

   //#####################
   // INSTRUCTION MEMORY
   //#####################
   interface IMem_IFC imem;
      // CPU side: IMem request
      method Action  req (Bit #(3) f3,
           	       WordXL addr,
           	       // The following  args for VM
           	       Priv_Mode  priv,
           	       Bit #(1)   sstatus_SUM,
           	       Bit #(1)   mstatus_MXR,
           	       WordXL     satp
                  );    // { VM_Mode, ASID, PPN_for_page_table }
         rg_instr_addr[0] <= addr;
         rg_instr_read[0] <= True;
         rg_instr_write[0] <= False;
         rg_instr_writedata[0] <= ?;
         rg_instr_byteenable[0] <= signExtend(1'b1);
         rg_instr_pending[1] <= True;
      endmethod

      // CPU side: IMem response
      method Bool     valid = rg_instr_valid[1];
      // this is set to true because without ISA_C it is always true, and with
      // ISA_C we go through CPU_Fetch_C which changes this to actually be correct
      method Bool     is_i32_not_i16 = True;
      method WordXL   pc = rg_instr_addr[0];
      method Instr    instr = rg_instr_readdata[1];
      // TODO RVFI memory exceptions?
      method Bool     exc = ((|(rg_instr_response[1])) == 1 ? True : False);
      method Exc_Code exc_code;
         return rg_instr_read[0] ? exc_code_LOAD_ADDR_MISALIGNED
                              : exc_code_STORE_AMO_ADDR_MISALIGNED;
      endmethod
      method WordXL   tval = rg_instr_addr[0];
   endinterface

   interface Avalon_IFC imem_master;
      method Action in (Avalon_Inputs inputs);
         rg_instr_waitrequest[0] <= inputs.avm_waitrequest;
         rg_instr_waitrequest_delayed[0] <= rg_instr_waitrequest[0];
         // if rg_instr_waitrequest is high, then it did not get fulfilled last cycle
         // if inputs.avm_waitrequest is low, then it has now been fulfilled so it is
         // valid
         // for the moment, just look at whether waitrequest was high at the end of a
         // cycle where we made a write request
         if (  (rg_instr_pending[0] && rg_instr_write[0] && !rg_instr_waitrequest_delayed[0]) // receiving a write response
            || inputs.avm_readdatavalid) // receiving a read response
         begin
            rg_instr_pending[0] <= False;
            rg_instr_valid[0] <= True;
            rg_instr_readdata[0] <= inputs.avm_readdata;
            rg_instr_response[0] <= inputs.avm_response;
         end
      endmethod

      method Avalon_Outputs out;
         return Avalon_Outputs {
            avm_address    : rg_instr_addr[0],
            avm_read       : rg_instr_read[0] && rg_instr_pending[0],
            avm_write      : rg_instr_write[0] && rg_instr_pending[0],
            avm_writedata  : rg_instr_writedata[0],
            avm_byteenable : rg_instr_byteenable[0]
         };
      endmethod
   endinterface



   //#####################
   // DATA MEMORY
   //#####################
   interface DMem_IFC dmem;
      // CPU side: DMem request
      method Action  req (CacheOp op,
                          Bit #(3) f3,
                          WordXL addr,
                          Bit #(64) store_value,
                          // The following  args for VM
                          Priv_Mode  priv,
                          Bit #(1)   sstatus_SUM,
                          Bit #(1)   mstatus_MXR,
                          WordXL     satp);    // { VM_Mode, ASID, PPN_for_page_table }
         rg_data_addr[0] <= addr;
         rg_data_read[0] <= op == CACHE_LD;
         rg_data_write[0] <= op == CACHE_ST;
         rg_data_writedata[0] <= truncate(store_value);
         rg_data_byteenable[0] <= fn_byteenable_from_req(f3, addr);
         rg_data_pending[1] <= True;
      endmethod

      // CPU side: DMem response
      method Bool       valid = rg_data_valid[1];
      // this will still be called word64 to simplify the work being undertaken
      // when in the core, this is always truncated to a WordXL
      // TODO change this (and the signals in the core) to be XLEN rather than hardcoded 64
      method Bit #(64)  word64 = zeroExtend(rg_data_readdata[1]);      // Load-value
      // TODO not sure what this value is used for
      method Bit #(64)  st_amo_val = zeroExtend(rg_data_writedata[1]);  // Final store-value for ST, SC, AMO
      method Bool       exc = (|(rg_data_response[1]) == 1) ? True : False;
      method Exc_Code   exc_code;
         return rg_data_read[0] ? exc_code_LOAD_ADDR_MISALIGNED
                                : exc_code_STORE_AMO_ADDR_MISALIGNED;
      endmethod
   endinterface

   interface Avalon_IFC dmem_master;
      method Action in (Avalon_Inputs inputs);
         rg_data_waitrequest[0] <= inputs.avm_waitrequest;
         rg_data_waitrequest_delayed[0] <= rg_data_waitrequest[0];
         if (  (rg_data_pending[0] && rg_data_write[0] && !rg_data_waitrequest_delayed[0]) // receiving a write response
            || inputs.avm_readdatavalid) // receiving a read response
         begin
            rg_data_pending[0] <= False;
            rg_data_valid[0] <= True;
            rg_data_readdata[0] <= inputs.avm_readdata;
            rg_data_response[0] <= inputs.avm_response;
         end
      endmethod

      method Avalon_Outputs out;
         return Avalon_Outputs {
            avm_address    : rg_data_addr[0],
            avm_read       : rg_data_read[0] && rg_data_pending[0],
            avm_write      : rg_data_write[0] && rg_data_pending[0],
            avm_writedata  : rg_data_writedata[0],
            avm_byteenable : rg_data_byteenable[0]
         };
      endmethod
   endinterface

endmodule


endpackage: Near_Mem_Avalon
