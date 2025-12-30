`timescale 1ns/1ps
`include "uvm_macros.svh"
`include "fifo_assertions.sv"
import uvm_pkg::*;

//============================================================
// Top
//============================================================
module top_tb;

  // ------------------------------------
  // Parameters
  // ------------------------------------
  localparam int DATA_W = 8;
  localparam int DEPTH  = 4;

  // ------------------------------------
  // Clock
  // ------------------------------------
  logic clk;
  initial clk = 0;
  always #5 clk = ~clk;

  // ------------------------------------
  // Interface
  // ------------------------------------
  fifo_if #(.DATA_W(DATA_W)) fifo_if_i (.clk(clk));

  // ------------------------------------
  // Assertions (SVA)
  // ------------------------------------
  fifo_assertions #(
    .DATA_W(DATA_W),
    .DEPTH (DEPTH)
  ) fifo_asrt (
    .vif(fifo_if_i)
  );

  // ------------------------------------
  // DUT
  // ------------------------------------
  fifo_sync #(
    .DATA_W (DATA_W),
    .DEPTH  (DEPTH)
  ) dut (
    .clk      (clk),
    .rst_n    (fifo_if_i.rst_n),
    .wr_en    (fifo_if_i.wr_en),
    .data_in  (fifo_if_i.data_in),
    .full     (fifo_if_i.full),
    .rd_en    (fifo_if_i.rd_en),
    .data_out (fifo_if_i.data_out),
    .empty    (fifo_if_i.empty)
  );

  // ------------------------------------
  // Reset
  // ------------------------------------
  initial begin
    fifo_if_i.rst_n   = 0;
    fifo_if_i.wr_en   = 0;
    fifo_if_i.rd_en   = 0;
    fifo_if_i.data_in = '0;
    repeat (5) @(posedge clk);
    fifo_if_i.rst_n   = 1;
  end

  // ------------------------------------
  // Waves (optional)
  // ------------------------------------
  initial begin
    $dumpfile("dump.vcd");
    $dumpvars(0, top_tb);
  end

  // ------------------------------------
  // UVM config + run
  // ------------------------------------
  initial begin
    uvm_config_db#(virtual fifo_if)::set(null, "*", "vif", fifo_if_i);
    uvm_config_db#(int)::set(null, "*", "DEPTH", DEPTH);

    run_test("fifo_random_test");
  end

endmodule
