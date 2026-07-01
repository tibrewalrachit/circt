// Trivial 8-bit wrapping counter with synchronous reset and enable.
// M0 round-trip design: SystemVerilog -> circt-verilog -> hw/comb/seq MLIR.
// The hand-written Lean twin lives in veda/Tests/Main.lean (Tests.counter8).
module counter (
    input  logic       clk,
    input  logic       rst,
    input  logic       en,
    output logic [7:0] count
);
  logic [7:0] count_q;

  always_ff @(posedge clk) begin
    if (rst) count_q <= 8'd0;
    else if (en) count_q <= count_q + 8'd1;
  end

  assign count = count_q;
endmodule
