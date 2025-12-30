`timescale 1ns/1ps

interface fifo_if #(
  parameter int DATA_W = 8
)(
  input logic clk
);
  logic rst_n;
  logic wr_en;
  logic [DATA_W-1:0] data_in;
  logic full;
  logic rd_en;
  logic [DATA_W-1:0] data_out;
  logic empty;

  clocking cb_drv @(posedge clk);
    default input #1step output #0;
    output rst_n, wr_en, rd_en, data_in;
    input  full, empty, data_out;
  endclocking

  clocking cb_mon @(posedge clk);
    default input #1step output #0;
    input rst_n, wr_en, rd_en, data_in, data_out, full, empty;
  endclocking

  property p_read_data_known;
    @(posedge clk) disable iff (!rst_n)
      (cb_mon.rd_en && !cb_mon.empty) |=> !$isunknown(cb_mon.data_out); //|=> next clock
  endproperty

  a_read_data_known: assert property (p_read_data_known);
endinterface
