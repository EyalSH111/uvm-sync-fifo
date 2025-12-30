`include "uvm_macros.svh"
import uvm_pkg::*;

// Environment
//============================================================
class fifo_env extends uvm_env;
  `uvm_component_utils(fifo_env)
  
  fifo_driver     drv;
  fifo_monitor    mon;
  fifo_scoreboard sb;
  fifo_coverage   cov;
  uvm_sequencer #(fifo_item) seqr;

  function new(string name, uvm_component parent);
    super.new(name,parent);
  endfunction

  function void build_phase(uvm_phase phase);
    super.build_phase(phase);
    drv  = fifo_driver    ::type_id::create("drv", this);
    mon  = fifo_monitor   ::type_id::create("mon", this);
    sb   = fifo_scoreboard::type_id::create("sb",  this);
    cov  = fifo_coverage  ::type_id::create("cov", this);
    seqr = uvm_sequencer#(fifo_item)::type_id::create("seqr",this);
  endfunction

  function void connect_phase(uvm_phase phase);
    super.connect_phase(phase);
    drv.seq_item_port.connect(seqr.seq_item_export);
    mon.wr_ap.connect(sb.wr_imp);
    mon.rd_ap.connect(sb.rd_imp);
  endfunction
endclass

