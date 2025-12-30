`include "uvm_macros.svh"
import uvm_pkg::*;

// ============================================================
// Random stress sequence
// ============================================================
class fifo_random_seq extends uvm_sequence #(fifo_item);
  `uvm_object_utils(fifo_random_seq)

  int N = 5000;

  function new(string name="fifo_random_seq");
    super.new(name);
  endfunction

  task body();
    fifo_item it;
    repeat (N) begin
      it = fifo_item::type_id::create("rand_it");
      start_item(it);
        it.do_write = $urandom_range(0,1);
        it.do_read  = $urandom_range(0,1);
        it.wdata    = $urandom;
      finish_item(it);
    end
  endtask
endclass


// ============================================================
// Drain sequence (used at end of test)
// ============================================================
class fifo_drain_seq extends uvm_sequence #(fifo_item);
  `uvm_object_utils(fifo_drain_seq)

  int N = 10;

  function new(string name="fifo_drain_seq");
    super.new(name);
  endfunction

  task body();
    fifo_item it;
    repeat (N) begin
      it = fifo_item::type_id::create("drain_it");
      start_item(it);
        it.do_write = 0;
        it.do_read  = 1;
        it.wdata    = '0;
      finish_item(it);
    end
  endtask
endclass


// ============================================================
// Random test 
// ============================================================
class fifo_random_test extends uvm_test;
  `uvm_component_utils(fifo_random_test)

  fifo_env env;

  function new(string name, uvm_component parent);
    super.new(name,parent);
  endfunction

  function void build_phase(uvm_phase phase);
    super.build_phase(phase);
    env = fifo_env::type_id::create("env", this);
  endfunction

  task run_phase(uvm_phase phase);
    fifo_random_seq seq;
    fifo_drain_seq  drain_seq;

    phase.raise_objection(this);

    // main random traffic
    seq = fifo_random_seq::type_id::create("seq");
    seq.start(env.seqr);

    // drain FIFO at end
    drain_seq = fifo_drain_seq::type_id::create("drain_seq");
    drain_seq.start(env.seqr);

    phase.drop_objection(this);
  endtask
endclass
