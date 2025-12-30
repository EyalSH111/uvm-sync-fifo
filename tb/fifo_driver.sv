`include "uvm_macros.svh"
import uvm_pkg::*;

// Driver (uses cb_drv to avoid race)
// One transaction = 1-cycle pulse of wr_en/rd_en (or none if blocked)
//============================================================
class fifo_driver extends uvm_driver #(fifo_item);
  `uvm_component_utils(fifo_driver)

  virtual fifo_if vif;

  function new(string name, uvm_component parent);
    super.new(name,parent);
  endfunction

  function void build_phase(uvm_phase phase);
    if (!uvm_config_db#(virtual fifo_if)::get(this,"","vif",vif))
      `uvm_fatal("NOVIF","driver has no vif")
  endfunction

  task run_phase(uvm_phase phase);
    fifo_item it;

    // default drives
    vif.cb_drv.wr_en   <= 0;
    vif.cb_drv.rd_en   <= 0;
    vif.cb_drv.data_in <= '0;

    // wait reset release
    wait (vif.rst_n == 1);

    forever begin
      seq_item_port.get_next_item(it);

      // default for this cycle
      vif.cb_drv.wr_en   <= 0;
      vif.cb_drv.rd_en   <= 0;
      vif.cb_drv.data_in <= '0;

      @(vif.cb_drv);

      if (it.do_write && !vif.cb_drv.full) begin
        vif.cb_drv.wr_en   <= 1;
        vif.cb_drv.data_in <= it.wdata;
      end

      if (it.do_read && !vif.cb_drv.empty) begin
        vif.cb_drv.rd_en <= 1;
      end

      // deassert next cycle
      @(vif.cb_drv);
      vif.cb_drv.wr_en <= 0;
      vif.cb_drv.rd_en <= 0;

      seq_item_port.item_done();
    end
  endtask
endclass