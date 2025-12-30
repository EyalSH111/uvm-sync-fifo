`include "uvm_macros.svh"
import uvm_pkg::*;

//============================================================
// Basic directed sequence: write then read
//============================================================
class fifo_basic_seq extends uvm_sequence #(fifo_item);
  `uvm_object_utils(fifo_basic_seq)

  function new(string name="fifo_basic_seq");
    super.new(name);
  endfunction

  task body();
    fifo_item it;

    // write
    it = fifo_item::type_id::create("wr");
    start_item(it);
      it.do_write = 1;
      it.do_read  = 0;
      it.wdata    = 8'hA5;
    finish_item(it);

    // read
    it = fifo_item::type_id::create("rd");
    start_item(it);
      it.do_write = 0;
      it.do_read  = 1;
      it.wdata    = '0;
    finish_item(it);
  endtask
endclass


//============================================================
// Base test
//============================================================
class fifo_base_test extends uvm_test;
  `uvm_component_utils(fifo_base_test)

  fifo_env env;

  function new(string name="fifo_base_test", uvm_component parent=null);
    super.new(name, parent);
  endfunction

  function void build_phase(uvm_phase phase);
    super.build_phase(phase);
    env = fifo_env::type_id::create("env", this);
  endfunction

  task run_phase(uvm_phase phase);
    fifo_basic_seq seq;

    phase.raise_objection(this);

    seq = fifo_basic_seq::type_id::create("seq");
    seq.start(env.seqr);

    // allow pending read to flush
    repeat (3) @(env.drv.vif.cb_drv);

    phase.drop_objection(this);
  endtask
endclass
