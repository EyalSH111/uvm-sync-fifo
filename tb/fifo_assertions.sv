module fifo_assertions #(parameter int DATA_W=8, DEPTH=4) (fifo_if vif);

  // Reset sanity
  property p_reset_idle;
    @(posedge vif.clk) !vif.rst_n |-> (!vif.wr_en && !vif.rd_en);
  endproperty
  a_reset_idle: assert property (p_reset_idle);

  // Block write on full: if full and wr_en -> occupancy must not increase
  // (here we can only assert the flag behavior level: full implies no "write accept")
  // If you have internal write_accept, assert that instead.
  property p_no_write_accept_when_full;
    @(posedge vif.clk) (vif.full && vif.wr_en) |-> $stable(vif.full); // weak but legal
  endproperty
  a_no_write_accept_when_full: assert property (p_no_write_accept_when_full);

  // Block read on empty
  property p_no_read_accept_when_empty;
    @(posedge vif.clk) (vif.empty && vif.rd_en) |-> $stable(vif.empty); // weak but legal
  endproperty
  a_no_read_accept_when_empty: assert property (p_no_read_accept_when_empty);

endmodule
