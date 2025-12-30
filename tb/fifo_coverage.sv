`include "uvm_macros.svh"
import uvm_pkg::*;

// ============================================================
// FIFO Functional Coverage
// - Occupancy coverage
// - Operation types
// - Overflow / Underflow attempts
// - Cross coverage
// ============================================================
class fifo_coverage extends uvm_component;
  `uvm_component_utils(fifo_coverage)

  // Interface
  virtual fifo_if vif;

  // Parameters
  int DEPTH = 4;

  // Derived state
  int occupancy;
  bit overflow_attempt;
  bit underflow_attempt;

  typedef enum int {OP_NONE, OP_WR, OP_RD, OP_BOTH} op_t;
  op_t op;

  // ------------------------------------------------------------
  // Covergroup
  // ------------------------------------------------------------
  covergroup fifo_cg;

    // Occupancy bins
    cp_occ : coverpoint occupancy {
      bins empty      = {0};
      bins one        = {1};
      bins mid        = {[2:DEPTH-2]};
      bins almost_f   = {DEPTH-1};
      bins full       = {DEPTH};
    }

    // Operation type
    cp_op : coverpoint op {
      bins none  = {OP_NONE};
      bins wr    = {OP_WR};
      bins rd    = {OP_RD};
      bins both  = {OP_BOTH};
    }

    // Overflow / underflow attempts
    cp_overflow  : coverpoint overflow_attempt { bins yes = {1}; }
    cp_underflow : coverpoint underflow_attempt { bins yes = {1}; }

    // Crosses (important!)
    cx_occ_op        : cross cp_occ, cp_op;
    cx_occ_overflow  : cross cp_occ, cp_overflow;
    cx_occ_underflow : cross cp_occ, cp_underflow;

  endgroup

  // ------------------------------------------------------------
  // Constructor
  // ------------------------------------------------------------
  function new(string name, uvm_component parent);
    super.new(name,parent);
    fifo_cg = new();
  endfunction

  // ------------------------------------------------------------
  // Build phase
  // ------------------------------------------------------------
  function void build_phase(uvm_phase phase);
    super.build_phase(phase);

    if (!uvm_config_db#(virtual fifo_if)::get(this,"","vif",vif))
      `uvm_fatal("NOVIF","fifo_coverage has no vif")

    void'(uvm_config_db#(int)::get(this,"","DEPTH",DEPTH));
  endfunction

  // ------------------------------------------------------------
  // Sample every cycle
  // ------------------------------------------------------------
  task run_phase(uvm_phase phase);
    occupancy = 0;

    forever begin
      @(vif.cb_mon);

      // -------- operation decoding --------
      if (!vif.cb_mon.wr_en && !vif.cb_mon.rd_en)
        op = OP_NONE;
      else if (vif.cb_mon.wr_en && !vif.cb_mon.rd_en)
        op = OP_WR;
      else if (!vif.cb_mon.wr_en && vif.cb_mon.rd_en)
        op = OP_RD;
      else
        op = OP_BOTH;

      // -------- overflow / underflow attempts --------
      overflow_attempt  = vif.cb_mon.wr_en && vif.cb_mon.full;
      underflow_attempt = vif.cb_mon.rd_en && vif.cb_mon.empty;

      // -------- update occupancy model --------
      case ({(vif.cb_mon.wr_en && !vif.cb_mon.full),
             (vif.cb_mon.rd_en && !vif.cb_mon.empty)})
        2'b10: occupancy++;
        2'b01: occupancy--;
        default: occupancy = occupancy;
      endcase

      // -------- clamp safety --------
      if (occupancy < 0)      occupancy = 0;
      if (occupancy > DEPTH)  occupancy = DEPTH;

      // -------- sample --------
      fifo_cg.sample();
    end
  endtask

endclass
