module edge_detector #(
    parameter WIDTH = 1
)(
    input clk,
    input [WIDTH-1:0] signal_in,
    output [WIDTH-1:0] edge_detect_pulse
);
    // TODO: Implement a multi-bit edge detector that detects a rising edge of 'signal_in[x]'
    // and outputs a one-cycle pulse 'edge_detect_pulse[x]' starting at the next clock edge
    reg [WIDTH-1:0] intermediate = 0;
    reg [WIDTH-1:0] flag = 0;

    genvar i;

    generate
	    for(i = 0; i < WIDTH; i = i + 1) begin
    		always @(posedge clk) begin
			flag[i] <= signal_in[i];
			intermediate[i] <= (~flag[i]) & signal_in[i];
		end
	    end
    endgenerate

    assign edge_detect_pulse = intermediate;
endmodule
