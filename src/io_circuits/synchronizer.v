module synchronizer #(parameter WIDTH = 1) (
    input [WIDTH-1:0] async_signal,
    input clk,
    output [WIDTH-1:0] sync_signal
);
    // TODO: Create your 2 flip-flop synchronizer here
    // This module takes in a vector of WIDTH-bit asynchronous
    // (from a different clock domain or not clocked, such as button press)
    // signals and should output a vector of WIDTH-bit synchronous signals
    // that are synchronized to the input clk
    reg [WIDTH-1:0] q_to_d = 0;
    reg [WIDTH-1:0] q = 0;
    always @(posedge clk) begin
	    q_to_d <= async_signal;
	    q <= q_to_d;
    end
    assign sync_signal = q;

endmodule
