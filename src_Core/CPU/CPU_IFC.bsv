// Copyright (c) 2016-2019 Bluespec, Inc. All Rights Reserved

package CPU_IFC;

// ================================================================
// BSV library imports

import GetPut       :: *;
import ClientServer :: *;

// ================================================================
// Project imports

import ISA_Decls       :: *;

`ifdef Near_Mem_Avalon
import Near_Mem_IFC :: *;
`else
import AXI4_Types  :: *;
import Fabric_Defs :: *;
`endif

`ifdef INCLUDE_DMEM_SLAVE
import AXI4_Lite_Types :: *;
`endif

`ifdef INCLUDE_GDB_CONTROL
import DM_CPU_Req_Rsp :: *;
`endif

`ifdef INCLUDE_TANDEM_VERIF
import TV_Info         :: *;
`elsif RVFI
import Verifier :: *;
import RVFI_DII :: *;
`endif

// ================================================================
// CPU interface

interface CPU_IFC;
   // Reset
   interface Server #(Bool, Bool)  hart0_server_reset;

   // ----------------
   // SoC fabric connections

`ifdef Near_Mem_Avalon
   // IMem to avalon
   (* always_ready *)  method Bit #(XLEN)         avm_instr_address;
   (* always_ready *)  method Bool                avm_instr_read;
   (* always_ready *)  method Bool                avm_instr_write;
   (* always_ready *)  method Bit #(XLEN)         avm_instr_writedata;
   (* always_ready *)  method Bit #(Bytes_per_WordXL) avm_instr_byteenable;
`else
   // IMem to Fabric master interface
   interface AXI4_Master_IFC #(Wd_Id, Wd_Addr, Wd_Data, Wd_User)  imem_master;
`endif

`ifdef Near_Mem_Avalon
   // DMem to avalon
   (* always_ready *)  method Bit #(XLEN)         avm_data_address;
   (* always_ready *)  method Bool                avm_data_read;
   (* always_ready *)  method Bool                avm_data_write;
   (* always_ready *)  method Bit #(XLEN)         avm_data_writedata;
   (* always_ready *)  method Bit #(Bytes_per_WordXL) avm_data_byteenable;
`else
   // DMem to Fabric master interface
   interface AXI4_Master_IFC #(Wd_Id, Wd_Addr, Wd_Data, Wd_User)  dmem_master;
`endif

   // ----------------------------------------------------------------
   // Optional AXI4-Lite D-cache slave interface

`ifdef INCLUDE_DMEM_SLAVE
   interface AXI4_Lite_Slave_IFC #(Wd_Addr, Wd_Data, Wd_User)  dmem_slave;
`endif

   // ----------------
   // External interrupts

   (* always_ready, always_enabled *)
   method Action  m_external_interrupt_req (Bool set_not_clear);

   (* always_ready, always_enabled *)
   method Action  s_external_interrupt_req (Bool set_not_clear);

   // ----------------
   // Software and timer interrupts (from Near_Mem_IO/CLINT)

   (* always_ready, always_enabled *)
   method Action  software_interrupt_req (Bool set_not_clear);

   (* always_ready, always_enabled *)
   method Action  timer_interrupt_req    (Bool set_not_clear);

   // ----------------
   // Non-maskable interrupt

   (* always_ready, always_enabled *)
   method Action  nmi_req (Bool set_not_clear);

   // ----------------
   // Set core's verbosity

   method Action  set_verbosity (Bit #(4)  verbosity, Bit #(64)  logdelay);

   // ----------------
   // Optional interface to Tandem Verifier

`ifdef RVFI_DII
   interface Flute_RVFI_DII_Server rvfi_dii_server;
`else
`ifdef INCLUDE_TANDEM_VERIF
   interface Get #(Trace_Data)  trace_data_out;
`endif
`ifdef RVFI
   interface Get #(Trace_Data)  trace_data_out;
`endif
`endif

   // ----------------
   // Optional interface to Debug Module

`ifdef INCLUDE_GDB_CONTROL
   // run-control, other
   interface Server #(Bool, Bool)  hart0_server_run_halt;
   interface Put #(Bit #(4))       hart0_put_other_req;

   // GPR access
   interface Server #(DM_CPU_Req #(5,  XLEN), DM_CPU_Rsp #(XLEN)) hart0_gpr_mem_server;

`ifdef ISA_F
   // FPR access
   interface Server #(DM_CPU_Req #(5,  FLEN), DM_CPU_Rsp #(FLEN)) hart0_fpr_mem_server;
`endif

   // CSR access
   interface Server #(DM_CPU_Req #(12, XLEN), DM_CPU_Rsp #(XLEN)) hart0_csr_mem_server;
`endif

   // ----------------------------------------------------------------
   // For ISA tests: watch memory writes to <tohost> addr

`ifdef WATCH_TOHOST
   method Action set_watch_tohost (Bool watch_tohost, Bit #(64) tohost_addr);
`endif

endinterface

// ================================================================

endpackage
