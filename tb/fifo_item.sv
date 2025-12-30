`include "uvm_macros.svh"
import uvm_pkg::*;

// Transaction
//============================================================
class fifo_item extends uvm_sequence_item;
  rand bit do_write;
  rand bit do_read;
  rand byte unsigned wdata;

  `uvm_object_utils(fifo_item)

  function new(string name="fifo_item");
    super.new(name);
  endfunction
endclass