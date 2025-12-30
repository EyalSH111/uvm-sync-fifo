`include "uvm_macros.svh"
import uvm_pkg::*;

// ============================================================
// Sequence: Fill FIFO to full
// ============================================================
class fifo_fill_seq extends uvm_sequence #(fifo_item);
  `uvm_object_utils(fifo_fill_seq)

  int depth;

  function new(string name="fifo_fill_seq");
    super.new(name);
  endfunction

  task body();
    fifo_item it;
    if (!uvm_config_db#(int)::get(null,"","DEPTH",depth))
      depth = 4;

    for (int i = 0; i < depth; i++) begin
      it = fifo_item::type_id::create($sformatf("wr_%0d",i));
      start_item(it);
        it.do_write = 1;
        it.do_read  = 0;
        it.wdata    = i;
      finish_item(it);
    end
  endtask
endclass

// ============================================================
// Sequence: Drain FIFO to empty
// ============================================================
class fifo_drain_seq extends uvm_sequence #(fifo_item);
  `uvm_object_utils(fifo_drain_seq)

  int depth;

  function new(string name="fifo_drain_seq");
    super.new(name);
  endfunction

  task body();
    fifo_item it;
    if (!uvm_config_db#(int)::get(null,"","DEPTH",depth))
      depth = 4;

    for (int i = 0; i < depth; i++) begin
      it = fifo_item::type_id::create($sformatf("rd_%0d",i));
      start_item(it);
        it.do_write = 0;
        it.do_read  = 1;
      finish_item(it);
    end
  endtask
endclass

// ============================================================
// Directed test
// ============================================================
class fifo_directed_test extends uvm_test;
  `uvm_component_utils(fifo_directed_test)

  fifo_env env;

  function new(string name="fifo_directed_test", uvm_component parent=null);
    super.new(name,parent);
  endfunction

  function void build_phase(uvm_phase phase);
    env = fifo_env::type_id::create("env",this);
  endfunction

  task run_phase(uvm_phase phase);
    fifo_fill_seq  fill;
    fifo_drain_seq drain;

    phase.raise_objection(this);

    fill  = fifo_fill_seq ::type_id::create("fill");
    drain = fifo_drain_seq::type_id::create("drain");

    fill.start(env.seqr);
    drain.start(env.seqr);

    phase.drop_objection(this);
  endtask
endclass
