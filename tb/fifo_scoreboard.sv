`include "uvm_macros.svh"
import uvm_pkg::*;

// ============================================================
// Analysis implementation declarations
// ============================================================
`uvm_analysis_imp_decl(_wr)
`uvm_analysis_imp_decl(_rd)

// ============================================================
// FIFO Scoreboard
// ============================================================
class fifo_scoreboard extends uvm_component;
  `uvm_component_utils(fifo_scoreboard)

  // ------------------------------------
  // Analysis ports
  // ------------------------------------
  uvm_analysis_imp_wr #(fifo_write_tr, fifo_scoreboard) wr_imp;
  uvm_analysis_imp_rd #(fifo_read_tr,  fifo_scoreboard) rd_imp;

  // ------------------------------------
  // Reference model (FIFO queue)
  // ------------------------------------
  byte unsigned model_q[$];

  // ------------------------------------
  // Parameters
  // ------------------------------------
  int DEPTH = 4;

  // ------------------------------------
  // Statistics
  // ------------------------------------
  int push_cnt  = 0;
  int match_cnt = 0;
  int error_cnt = 0;

  // ------------------------------------
  // Constructor
  // ------------------------------------
  function new(string name, uvm_component parent);
    super.new(name, parent);
    wr_imp = new("wr_imp", this);
    rd_imp = new("rd_imp", this);
  endfunction

  // ------------------------------------
  // Build phase
  // ------------------------------------
  function void build_phase(uvm_phase phase);
    super.build_phase(phase);
    void'(uvm_config_db#(int)::get(this, "", "DEPTH", DEPTH));
  endfunction

  // ------------------------------------
  // Write accepted → update model
  // ------------------------------------
  function void write_wr(fifo_write_tr t);
    if (model_q.size() == DEPTH) begin
      error_cnt++;
      `uvm_error("SB", "Model overflow: write accepted while full")
      return;
    end

    model_q.push_back(t.data);
    push_cnt++;
  endfunction

  // ------------------------------------
  // Read accepted → compare with model
  // ------------------------------------
  function void write_rd(fifo_read_tr t);
    byte unsigned exp;

    if (model_q.size() == 0) begin
      error_cnt++;
      `uvm_error("SB", "Read accepted while model empty")
      return;
    end

    exp = model_q.pop_front();

    if (t.data !== exp) begin
      error_cnt++;
      `uvm_error("SB",
        $sformatf("MISMATCH: exp=0x%0h got=0x%0h", exp, t.data))
    end
    else begin
      match_cnt++;
    end
  endfunction

  // ------------------------------------
  // Reset handling (called by reset-mid test)
  // ------------------------------------
  function void reset_model();
    model_q.delete();
    `uvm_info("SB_RST",
              "Scoreboard reference model flushed due to reset",
              UVM_MEDIUM)
  endfunction

  // ------------------------------------
  // Final summary
  // ------------------------------------
  function void report_phase(uvm_phase phase);
    `uvm_info("SB_SUMMARY",
      $sformatf(
        "SUMMARY: pushes=%0d matches=%0d errors=%0d remaining=%0d",
        push_cnt, match_cnt, error_cnt, model_q.size()
      ),
      UVM_MEDIUM
    )

    if (error_cnt == 0 && model_q.size() == 0)
      `uvm_info("SB_SUMMARY", "FIFO SCOREBOARD: PASS", UVM_MEDIUM)
    else
      `uvm_error("SB_SUMMARY", "FIFO SCOREBOARD: FAIL")
  endfunction

endclass
