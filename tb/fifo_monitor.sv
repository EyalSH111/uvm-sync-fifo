`include "uvm_macros.svh"
import uvm_pkg::*;

// Monitor transactions
//============================================================
class fifo_write_tr extends uvm_sequence_item;
  byte unsigned data;
  `uvm_object_utils(fifo_write_tr)
  function new(string name="fifo_write_tr"); super.new(name); endfunction
endclass

class fifo_read_tr extends uvm_sequence_item;
  byte unsigned data;
  `uvm_object_utils(fifo_read_tr)
  function new(string name="fifo_read_tr"); super.new(name); endfunction
endclass


//============================================================
// Monitor (samples via cb_mon; supports back-to-back operations)
// For registered read: sample data_out in cycle AFTER accepted read
// We do this by queueing a "pending read" and consuming next cb_mon tick.
//============================================================
class fifo_monitor extends uvm_component;
  `uvm_component_utils(fifo_monitor)

  virtual fifo_if vif;
  uvm_analysis_port #(fifo_write_tr) wr_ap;
  uvm_analysis_port #(fifo_read_tr)  rd_ap;

  bit pending_read;

  function new(string name, uvm_component parent);
    super.new(name,parent);
    wr_ap = new("wr_ap",this);
    rd_ap = new("rd_ap",this);
  endfunction

  function void build_phase(uvm_phase phase);
    if (!uvm_config_db#(virtual fifo_if)::get(this,"","vif",vif))
      `uvm_fatal("NOVIF","monitor has no vif")
  endfunction

  task run_phase(uvm_phase phase);
    fifo_write_tr wtr;
    fifo_read_tr  rtr;

    pending_read = 0;

    forever begin
      @(vif.cb_mon);

      // First, if we had an accepted read last cycle, publish its data now
      if (pending_read) begin
        rtr = fifo_read_tr::type_id::create("rtr");
        rtr.data = vif.cb_mon.data_out;
        rd_ap.write(rtr);
        pending_read = 0;
      end

      // Write accepted this cycle
      if (vif.cb_mon.wr_en && !vif.cb_mon.full) begin
        wtr = fifo_write_tr::type_id::create("wtr");
        wtr.data = vif.cb_mon.data_in;
        wr_ap.write(wtr);
      end

      // Read accepted this cycle -> data will be valid next cycle (registered)
      if (vif.cb_mon.rd_en && !vif.cb_mon.empty) begin
        pending_read = 1;
      end
    end
  endtask
endclass