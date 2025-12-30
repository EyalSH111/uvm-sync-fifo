`timescale 1ns/1ps

// ============================================================
// Synchronous FIFO – Registered Read
// Spec:
// - Single clock
// - Parameterized DATA_W, DEPTH
// - Block write when full
// - Block read when empty
// - Registered read: data_out valid 1 cycle after rd_en && !empty
// ============================================================

module fifo_sync #(
  parameter int DATA_W = 8,
  parameter int DEPTH  = 4
)(
  input  logic               clk,
  input  logic               rst_n,

  // Write side
  input  logic               wr_en,
  input  logic [DATA_W-1:0]  data_in,
  output logic               full,

  // Read side
  input  logic               rd_en,
  output logic [DATA_W-1:0]  data_out,
  output logic               empty
);

  // ------------------------------------------------------------
  // Internal parameters
  // ------------------------------------------------------------
  localparam int ADDR_W = (DEPTH <= 1) ? 1 : $clog2(DEPTH);

  // ------------------------------------------------------------
  // Storage and pointers
  // ------------------------------------------------------------
  logic [DATA_W-1:0] mem [0:DEPTH-1];
  logic [ADDR_W-1:0] wr_ptr, rd_ptr;
  logic [ADDR_W:0]   count;

  // ------------------------------------------------------------
  // Write logic
  // ------------------------------------------------------------
  always_ff @(posedge clk or negedge rst_n) begin
    if (!rst_n) begin
      wr_ptr <= '0;
    end
    else if (wr_en && !full) begin
      mem[wr_ptr] <= data_in;
      wr_ptr      <= wr_ptr + 1'b1;
    end
  end

  // ------------------------------------------------------------
  // Read logic (registered read)
  // ------------------------------------------------------------
  always_ff @(posedge clk or negedge rst_n) begin
    if (!rst_n) begin
      rd_ptr   <= '0;
      data_out <= '0;
    end
    else if (rd_en && !empty) begin
      data_out <= mem[rd_ptr];
      rd_ptr   <= rd_ptr + 1'b1;
    end
  end

  // ------------------------------------------------------------
  // Occupancy counter
  // ------------------------------------------------------------
  always_ff @(posedge clk or negedge rst_n) begin
    if (!rst_n) begin
      count <= '0;
    end
    else begin
      case ({(wr_en && !full), (rd_en && !empty)})
        2'b10: count <= count + 1'b1; // write only
        2'b01: count <= count - 1'b1; // read only
        default: count <= count;      
      endcase
    end
  end

  // ------------------------------------------------------------
  // Flags
  // ------------------------------------------------------------
  assign empty = (count == 0);
  assign full  = (count == DEPTH);

endmodule
