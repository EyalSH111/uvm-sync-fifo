`include "uvm_macros.svh"
import uvm_pkg::*;

class fifo_reset_mid_test extends uvm_test;
  `uvm_component_utils(fifo_reset_mid_test)

  fifo_env env;
  virtual fifo_if vif;

  function new(string name, uvm_component parent);
    super.new(name,parent);
  endfunction

  function void build_phase(uvm_phase phase);
    super.build_phase(phase);
    env = fifo_env::type_id::create("env", this);

    if (!uvm_config_db#(virtual fifo_if)::get(this,"","vif",vif))
      `uvm_fatal("NOVIF","reset_mid_test: no vif in config_db")
  endfunction

  task run_phase(uvm_phase phase);
    // --------- ALL DECLARATIONS MUST BE FIRST ----------
    fifo_random_seq seq;
    fifo_drain_seq  dseq;
    // --------------------------------------------------

    phase.raise_objection(this);

    // 1) run some random traffic
    seq = fifo_random_seq::type_id::create("seq");
    seq.N = 1000;
    seq.start(env.seqr);

    // 2) assert reset mid-traffic
    vif.cb_drv.rst_n <= 1'b0;
    vif.cb_drv.wr_en <= 1'b0;
    vif.cb_drv.rd_en <= 1'b0;
    repeat (4) @(vif.cb_drv);
    vif.cb_drv.rst_n <= 1'b1;

    // settle
    repeat (3) @(vif.cb_drv);

    // 3) flush scoreboard model
    env.sb.reset_model();

    // 4) run again briefly
    seq = fifo_random_seq::type_id::create("seq2");
    seq.N = 1000;
    seq.start(env.seqr);

    // 5) drain FIFO to avoid pending reads
    dseq = fifo_drain_seq::type_id::create("dseq");
    dseq.N = 2 * 4;   
    dseq.start(env.seqr);

    repeat (2) @(vif.cb_drv);

    phase.drop_objection(this);
  endtask
endclass
