/*-
 * Copyright (c) 2010 Gregory A. Chadwick
 * Copyright (c) 2013 Jonathan Woodruff
 * All rights reserved.
 *
 * This software was developed by SRI International and the University of
 * Cambridge Computer Laboratory under DARPA/AFRL contract FA8750-10-C-0237
 * ("CTSRD"), as part of the DARPA CRASH research programme.
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
package Forwarding_RegFile;

//import MIPS::*;
import Debug::*;
import CPU_Globals::*;
import RegFile::*;
import DReg::*;
import VnD::*;
import FIFOF::*;
import FIFO::*;
import FF::*;
import SpecialFIFOs::*;
import Vector::*;
import ConfigReg :: *;

import GetPut       :: *;
import GetPut_Aux :: *;
import ClientServer :: *;
import ISA_Decls :: *;

//`define ReRegs 4

typedef Bit#(4) RenameReg; // A renamed destination register address, one of 4 in the current design

typedef struct {
  Bool    valid;
  regT register;
} SpecReg#(type regT) deriving (Bits, Eq, FShow);

typedef struct {
  Epoch  epoch;
  Bool   valid;
  idxT   regNum;
  Bool   pending;
} SpecRegTag#(type idxT) deriving (Bits, Eq, FShow);

typedef struct {
  Bool valid;
  Bool pending;
  RenameReg regNum;
} RenameReport deriving (Bits, Eq, FShow);

typedef struct {
  RenameReport a;
  RenameReport b;
  RenameReport old;
  ReadRegs#(regT) regFileVals;
  WriteReport#(regT, idxT) write;
} RegReadReport#(type regT, type idxT) deriving (Bits, Eq, FShow);

typedef struct {
  SpecReg#(regT)   specReg;
  RenameReg           regNum;
} RenameRegWrite#(type regT) deriving (Bits, Eq);

typedef struct {
  Bool    write;
  Bool    couldWrite;
  regT    data;
  idxT    regNum;
} RegWrite#(type regT, type idxT) deriving (Bits, Eq);

typedef struct {
  regType regA;
  regType regB;
} ReadRegs#(type regType) deriving (Bits, Eq, FShow);

typedef struct {
  WriteType wtype;
  Bool      doWrite; // Should the write happen (taking into account conditional write and whether the instruction committed.)
  RenameReg regNum;
  idxT      archRegNum;
  regT      data;
} WriteReport#(type regT, type idxT) deriving (Bits, Eq, FShow);

typedef struct {
  Epoch     epoch;
  idxT      a;
  idxT      b;
  WriteType write;
  idxT      dest;
  Bool      fromDebug;
  Bool      rawReq;
} ReadReq#(type idxT) deriving (Bits, Eq, FShow);

typedef enum {
  None,
  Simple,
  Conditional,
  Pending
} WriteType deriving (Bits, Eq, FShow);

typedef enum {Init, Serving} RegFileState deriving (Bits, Eq);

interface ForwardingPipelinedRegFileIFC#(type regT, type idxT, numeric type renameRegs);
  method Action reqRegs(ReadReq#(idxT) req);
  // These two methods, getRegs and writeRegSpeculative should be called in the
  // same rule, Execute.
  (* always_ready *)
  method ReadRegs#(regT) readRegs();
  method Action writeRegSpeculative(regT data, Bool write);
  method Action writeReg(regT data, Bool committing);
  method Action writeRaw(idxT regW, regT data);
  method Action readRawPut(idxT regA);
  method ActionValue#(regT) readRawGet();
  method Action putDebugRegs(regT a, regT b);
  method Action clearRegs(Bit#(TExp#(a__)) mask) provisos (Bits#(idxT, a__));
  (* always_ready *)
  method Bool reg_is_ready ();
  method Bool canWrite ();
  // Reset
  interface Server #(Token, Token) server_reset;
endinterface

module mkForwardingPipelinedRegFile#(regT defaultValue)(ForwardingPipelinedRegFileIFC#(regT,idxT,renameRegs))
  provisos(Bits#(regT, regT_sz), Bounded#(idxT), Bits#(idxT, a__), PrimIndex#(idxT, b__), FShow#(idxT), FShow#(Forwarding_RegFile::RegReadReport#(regT, idxT)));
  SpecRegTag#(idxT) initialTag = SpecRegTag{valid:False, epoch:?, regNum:?, pending:?};
  Reg#(Vector#(renameRegs,SpecRegTag#(idxT))) rnTags          <- mkConfigReg(replicate(initialTag));
  Vector#(renameRegs,Array#(Reg#(SpecReg#(regT)))) rnRegs     <- replicateM(mkCReg(2,?));
  RegFile3Port#(regT,idxT)                    regFile         <- mkRegFile3Port;
  Reg#(Bit#(TExp#(SizeOf#(idxT))))            regMask         <- mkConfigReg(0);
  FIFOF#(Bit#(TExp#(SizeOf#(idxT))))          regMaskUpdate   <- mkUGSizedFIFOF(4);


  FF#(void,renameRegs)                       limiter <- mkUGFFDebug("limiter");
  FIFO#(ReadReq#(idxT))                      readReq <- mkSizedFIFO(3);
  FF#(RegReadReport#(regT,idxT),1)        readReport <- mkLFF1;
  Reg#(VnD#(WriteReport#(regT,idxT)))  wbReRegWriteA <- mkDReg(VnD{v: False, d: ?});
  // This can be unguarded if it can hold "renameRegs" elements becuase this portion of the pipeline is guarded by "limiter".
  FF#(WriteReport#(regT,idxT),renameRegs) wbReRegWriteB <-mkUGFFDebug("wbReRegWriteB");
  WriteReport#(regT,idxT) wf = wbReRegWriteB.first;
  Reg#(WriteReport#(regT,idxT))  wbRegFileWriteWire <- mkConfigRegU;
  Reg#(WriteReport#(regT,idxT))    wbReRegWriteWire <- mkDWire(WriteReport{
                              wtype: None,
                              doWrite: False,
                              regNum: wf.regNum,
                              archRegNum: wf.archRegNum,
                              data: ?
                            });
  
  Reg#(RenameReg)       nextReReg               <- mkReg(0);

  Reg#(regT)            debugOpA                <- mkRegU;
  Reg#(regT)            debugOpB                <- mkRegU;
  
  FIFOF#(idxT)          readRawReg              <- mkFIFOF1;

  // These two wires force a priority of the pipelined read and write
  // methods over the raw versions to prevent extra ports being created
  // for the raw interfaces.
  Reg#(Bool)              writeRegUsed            <- mkDWire(False);

  FIFOF #(Token) f_reset_reqs <- mkFIFOF;
  FIFOF #(Token) f_reset_rsps <- mkFIFOF;

  //rule rl_regfile_debug;

  //endrule

  //rule rl_regfile_reset (f_reset_reqs.notEmpty);
  //  $display("forwarding regfile reset start");
  //  Bool write = ?;
  //  regT data = ?;
  //  WriteReport#(regT,idxT)  req = readReport.first.write;
  //  RenameReport old = readReport.first.old;
  //  readReport.deq();
  //  req.data = data;
  //  // If we were told that this was going to be an unconditional write, write anyway.
  //  req.doWrite = (case(req.wtype)
  //                    None: return False;
  //                    Simple: return True;
  //                    Conditional: return write;
  //                    Pending: return True;
  //                 endcase);

  //  // Update rename registers with this write value.
  //  SpecReg#(regT) invReg = SpecReg{ register: ?, valid: False};
  //  SpecReg#(regT) reregWrite = (case(req.wtype)
  //                            None:        return rnRegs[req.regNum][0];
  //                            Simple:      return SpecReg{ register: data, valid: True};
  //                            Conditional: begin
  //                                           if (write) return SpecReg{ register: data, valid: True};
  //                                           else return (old.valid) ? rnRegs[old.regNum][0]:invReg;
  //                                         end
  //                            Pending:     return invReg;
  //                         endcase);
  //  rnRegs[req.regNum][0] <= reregWrite;
  //  debug2("regfile", $display("Wrote rereg %d with %x, valid: %d", req.regNum, reregWrite.register, reregWrite.valid));
  //  wbReRegWriteA <= VnD{v: True, d: req};
  //  let tmp2 <- writeReg(?, False);
  //endrule

  //rule rl_regfile_reset2 (f_reset_reqs.notEmpty);
  //  $display("forwarding regfile reset2");
  //  let tmp <- writeReg(?, False);
  //endrule

  //rule rl_regfile_reset_finish (f_reset_reqs.notEmpty);
  //  $display("forwarding regfile reset finish");
  //  let tmp <- f_reset_reqs.deq;
  //  f_reset_rsps.enq(?);
  //endrule
  //(* descending_urgency = "rl_regfile_reset, rl_regfile_reset2, rl_regfile_reset_finish" *)

  rule rl_register_debug;
    $display("forwarding regfile stats:");
    $display("readReq.first: ", fshow(readReq.first));
    //$display("readReport.first: ", fshow(readReport.first));
    $display("limiter.notFull ", limiter.notFull);
    $display("limiter.notEmpty ", limiter.notEmpty);
  endrule

  function Action fa_reset;
    action
    rnTags <= replicate(initialTag);
    // TODO generalise this
    rnRegs[0][1] <= ?;
    rnRegs[1][1] <= ?;
    rnRegs[2][1] <= ?;
    rnRegs[3][1] <= ?;
    limiter.clear();
    readReq.clear();
    readReport.clear();
    wbReRegWriteA <= VnD{v: False, d: ?};
    wbReRegWriteB.clear();
    wbRegFileWriteWire <= ?;
    wbReRegWriteWire <= WriteReport {wtype: None,
                                     doWrite: False,
                                     regNum: wf.regNum,
                                     archRegNum: wf.archRegNum,
                                     data: ?
                                    };
    nextReReg <= 0;
    debugOpA <= ?;
    debugOpB <= ?;
    readRawReg.clear();
    writeRegUsed <= False;
    endaction
  endfunction

  rule readRegFilesRaw(readRawReg.notEmpty);
    trace($display("Did Read Raw on reg %x", readRawReg.first));
    ReadReq#(idxT) req = ?;
    req.a = readRawReg.first;
    readRawReg.deq;
    req.rawReq = True;
    readReq.enq(req);
  endrule
  
  ReadReq#(idxT) rq = readReq.first;
  rule readRegFiles(!rq.rawReq && limiter.notFull);
    $display("forwarding regfile readregfiles");
    readReq.deq();

    ReadRegs#(regT) ret = ?;
    ret.regA <- regFile.readA(rq.a);
    ret.regB <- regFile.readB(rq.b);
    if (regMask[rq.a]==1'b0) ret.regA = defaultValue;
    if (regMask[rq.b]==1'b0) ret.regB = defaultValue;

    if (rq.fromDebug) begin
      if (rq.a==0) ret.regA = debugOpA;
      if (rq.b==0) ret.regB = debugOpB;
    end 
    
    debug2("regfile", $display("Read values from register file BRAM: A:%x B:%x, regMask: %x", ret.regA, ret.regB, regMask));
    debug2("regfile", $display("read addresses: A:%0d B:%0d", rq.a, rq.b));

    // Detect any dependencies on renamed registers and setup for forwarding in
    // the readRegs method.
    RegReadReport#(regT,idxT) report = RegReadReport{
      a:   RenameReport{ valid: False, regNum: ?, pending: False },
      b:   RenameReport{ valid: False, regNum: ?, pending: False },
      old: RenameReport{ valid: False, regNum: ?, pending: False },
      regFileVals: ret,
      write: WriteReport{
        wtype: rq.write,
        doWrite: ?,
        regNum: nextReReg,
        archRegNum: rq.dest,
        data: ?
      }
    };

    function SpecRegTag#(idxT) cleanOld(SpecRegTag#(idxT) st) =
      (st.epoch == rq.epoch) ? st : SpecRegTag{valid:False, epoch:st.epoch, regNum:st.regNum, pending:st.pending};
    Vector#(renameRegs, SpecRegTag#(idxT)) newReTags = map(cleanOld,rnTags);
    
    for (Integer i=0; i<valueOf(renameRegs); i=i+1) begin
      SpecRegTag#(idxT) srt = newReTags[i];
      RenameReport renameReport = RenameReport{
        valid: True,
        regNum: fromInteger(i),
        pending: srt.pending
      };
      if (srt.valid) begin
        if (srt.regNum == rq.a) begin
          report.a = renameReport;
          debug2("regfile", $display("Reading A from rereg %d", i));
        end
        if (srt.regNum == rq.b) begin
          report.b = renameReport;
          debug2("regfile", $display("Reading B from rereg %d", i));
        end
        // Remember and invalidate an old mapping of our destination register.
        if (srt.regNum == rq.dest) begin
          report.old = renameReport;
          debug2("regfile", $display("Old Register is %d", i));
          // Also invalidate a mapping if we will get a new one.
          if (rq.write != None) srt.valid = False;
        end
      end
      newReTags[i] = srt;
    end
    if (rq.write != None) begin
      newReTags[nextReReg] = SpecRegTag{
        valid: True,
        regNum: rq.dest,
        epoch: rq.epoch,
        pending: rq.write==Pending
      };
      debug2("regfile", $display("Rename register %d allocated for next write", nextReReg, fshow(newReTags[nextReReg])));
      nextReReg <= (nextReReg + 1 == fromInteger(valueOf(renameRegs))) ? 0:nextReReg + 1;
    end
    limiter.enq(?);
    rnTags <= newReTags;
    readReport.enq(report);
  endrule

  // Some booleans to help with composing the conditions for the readRegs method.
  // ReadRegs needs to wait until any pending operands that it needs are ready.
  RegReadReport#(regT,idxT) topRpt = readReport.first;
  Bool a_is_pending = topRpt.a.valid &&
                      topRpt.a.pending &&
                      !rnRegs[topRpt.a.regNum][0].valid;
  Bool b_is_pending = topRpt.b.valid &&
                      topRpt.b.pending &&
                      !rnRegs[topRpt.b.regNum][0].valid;
  Bool old_is_pending = topRpt.write.wtype == Conditional &&
                        topRpt.old.pending &&
                        !rnRegs[topRpt.old.regNum][0].valid;
  Bool pipeEmpty = !wbReRegWriteA.v && !wbReRegWriteB.notEmpty;
  Bool read_is_ready = (!a_is_pending && !b_is_pending && !old_is_pending)
                        || pipeEmpty;
                       
  rule doWriteRegFile;
    WriteReport#(regT,idxT) wr = wbRegFileWriteWire;
    if (wr.doWrite) begin
      regFile.write(wr.archRegNum,wr.data);
      debug2("regfile", $display("Wrote register %d", wr.archRegNum));
    end
  endrule
  
  rule doWriteReReg;
    WriteReport#(regT,idxT) wr = wbReRegWriteWire;
    if (wr.wtype==Pending) begin
      rnRegs[wr.regNum][1] <= SpecReg{valid: wr.doWrite, register: wr.data };
    end
  endrule
  
  rule moveWbReRegWrite(wbReRegWriteA.v);
    wbReRegWriteB.enq(wbReRegWriteA.d);
  endrule

  method Action reqRegs(ReadReq#(idxT) req) if (!readRawReg.notEmpty);
    $display("forwarding regfile readreq enq");
    readReq.enq(req);
  endmethod

  method ReadRegs#(regT) readRegs() if (read_is_ready);
  //method ActionValue#(ReadRegs#(regT)) readRegs();
    RegReadReport#(regT,idxT) report = readReport.first(); //Dequeued by writeRegSpeculative
    ReadRegs#(regT) ret = report.regFileVals;
    // Return renamed register values if necessary
    if (report.a.valid && rnRegs[report.a.regNum][0].valid) begin
      ret.regA = rnRegs[report.a.regNum][0].register;
      //debug2("regfile", $display("Forwarding operand A from rereg %d", report.a.regNum));
    end
    if (report.b.valid && rnRegs[report.b.regNum][0].valid) begin
      ret.regB = rnRegs[report.b.regNum][0].register;
      //debug2("regfile", $display("Forwarding operand B from rereg %d", report.b.regNum));
    end
    //debug2("regfile", $display("Delivering operand A: %x, operand B: %x", ret.regA, ret.regB));
    return ret;
  endmethod

  method Action writeRegSpeculative(regT data, Bool write);
    WriteReport#(regT,idxT)  req = readReport.first.write;
    RenameReport old = readReport.first.old;
    readReport.deq();
    req.data = data;
    // If we were told that this was going to be an unconditional write, write anyway.
    req.doWrite = (case(req.wtype)
                      None: return False;
                      Simple: return True;
                      Conditional: return write;
                      Pending: return True;
                   endcase);

    // Update rename registers with this write value.
    SpecReg#(regT) invReg = SpecReg{ register: ?, valid: False};
    SpecReg#(regT) reregWrite = (case(req.wtype)
                              None:        return rnRegs[req.regNum][0];
                              Simple:      return SpecReg{ register: data, valid: True};
                              Conditional: begin
                                             if (write) return SpecReg{ register: data, valid: True};
                                             else return (old.valid) ? rnRegs[old.regNum][0]:invReg;
                                           end
                              Pending:     return invReg;
                           endcase);
    rnRegs[req.regNum][0] <= reregWrite;
    debug2("regfile", $display("Wrote rereg %d with %x, valid: %d", req.regNum, reregWrite.register, reregWrite.valid));
    wbReRegWriteA <= VnD{v: True, d: req};
  endmethod

  method Action writeReg(regT data, Bool committing) 
                            if (wbReRegWriteB.notEmpty);
    WriteReport#(regT,idxT) wr = wf;//wbReRegWriteB.first;
    wbReRegWriteB.deq();
    wr.doWrite = (wr.doWrite && committing);
    wr.data = data;
    wr.data = (wr.wtype==Pending) ? data:wr.data;
    wbRegFileWriteWire <= wr;
    // Do pending write to rename register if necessary
    wbReRegWriteWire <= WriteReport{
      regNum: wr.regNum,
      wtype: wr.wtype,
      doWrite: wr.doWrite,
      data: data,
      archRegNum: ?
    };

    Bit#(TExp#(SizeOf#(idxT))) newRegMask = regMask;
    if (regMaskUpdate.notEmpty) begin
      newRegMask = (regMaskUpdate.first & newRegMask);
      debug2("regfile", $display("Applied register mask %x", newRegMask));
      regMaskUpdate.deq;
    end
    if (wr.doWrite) newRegMask[wr.archRegNum] = 1'b1;
    
    //rnRegs[wr.regNum][1] <= SpecReg{ valid: True, register: writeData };
    limiter.deq();
    regMask <= newRegMask;
    writeRegUsed <= True;
  endmethod
  
  method Action writeRaw(idxT regW, regT data) if (!writeRegUsed);
    regMask[regW] <= 1'b1;
    wbRegFileWriteWire <= WriteReport{
        wtype: Simple,
        doWrite: True,
        regNum: ?,
        archRegNum: regW,
        data: data
      };
  endmethod
  
  method Action readRawPut(idxT regA);
    readRawReg.enq(regA);
  endmethod
  
  method ActionValue#(regT) readRawGet() if (rq.rawReq);
    regT ret <- regFile.readA(rq.a);
    debug2("regfile", $display("readRawGot %x", ret));
    readReq.deq();
    return ret;
  endmethod

  method Action putDebugRegs(regT a, regT b);
    debugOpA <= a;
    debugOpB <= b;
  endmethod
  
  method Action clearRegs(Bit#(TExp#(SizeOf#(idxT))) mask);
    debug2("regfile", $display("Enqued register mask %x", mask));
    regMaskUpdate.enq(mask);
  endmethod

  method Bool reg_is_ready ();
    return read_is_ready;
  endmethod

  method Bool canWrite ();
    return wbReRegWriteB.notEmpty;
  endmethod

  // Reset
  interface Server server_reset;
    interface Put request;
      method Action put (Token token);
        // This response is placed here, and not in rl_reset_loop, because
        // reset_loop can happen on power-up, where no response is expected.
        //f_reset_rsps.enq (?);
        fa_reset();
        $display("forwarding regfile reset request");
      endmethod
    endinterface
    interface Get response;
      //method ActionValue #(Token) get if (f_reset_rsps.notEmpty);
      method ActionValue #(Token) get;
        //let token <- pop (f_reset_rsps);
        $display("forwarding regfile reset response");
        return ?;
      endmethod
    endinterface
  endinterface


endmodule


interface RegFile3Port#(type regT, type idxT);
  method Action  write(idxT regW, regT data);
  method ActionValue#(regT) readA(idxT regNum);
  method ActionValue#(regT) readB(idxT regNum);
endinterface

module mkRegFile3Port(RegFile3Port#(regT,idxT))
  provisos(Bits#(regT, regT_sz), Bounded#(idxT), Bits#(idxT, a__));
  RegFile#(idxT,regT) regFile <- mkRegFile(minBound, maxBound);//(2**valueOf(SizeOf#(idxT))-1)); // BRAM
  
  method Action write(idxT regW, regT data);
    regFile.upd(regW,data);
  endmethod
  method ActionValue#(regT) readA(idxT regNum);
    return regFile.sub(regNum);
  endmethod
  method ActionValue#(regT) readB(idxT regNum);
    return regFile.sub(regNum);
  endmethod
endmodule

endpackage
