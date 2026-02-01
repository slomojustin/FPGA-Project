module debouncer #(
    parameter WIDTH              = 1,
    parameter SAMPLE_CNT_MAX     = 62500,
    parameter PULSE_CNT_MAX      = 200,
    parameter WRAPPING_CNT_WIDTH = $clog2(SAMPLE_CNT_MAX),
    parameter SAT_CNT_WIDTH      = $clog2(PULSE_CNT_MAX) + 1
) (
    input clk,
    input [WIDTH-1:0] glitchy_signal,
    output [WIDTH-1:0] debounced_signal
);
    // TODO: Fill in the necessary logic to implement the wrapping counter and the saturating counters
    // Some initial code has been provided to you, but feel free to change it however you like
    // One global wrapping counter is required
    // One saturating counter is needed for each bit of glitchy_signal
    // You need to think of the conditions for resetting, clock enable, etc.
    // Refer to the block diagram in the spec

    // Remove this line once you create your debouncer

    reg [SAT_CNT_WIDTH-1:0] saturating_counter [WIDTH-1:0];
    reg [WRAPPING_CNT_WIDTH-1:0] wrapping_counter [WIDTH-1:0];

    genvar i;


    generate
	    for(i = 0; i < WIDTH; i = i + 1) begin
    		initial begin
			saturating_counter[i] = 'b0;	
			wrapping_counter[i] = 'b0;
    		end

    		always @(posedge clk) begin
	    		wrapping_counter[i] <= wrapping_counter[i] + 1;
	    		if ((wrapping_counter[i] == SAMPLE_CNT_MAX) && glitchy_signal[i]) begin
		    		if (saturating_counter[i] == PULSE_CNT_MAX) begin
			    		saturating_counter[i] <= PULSE_CNT_MAX;
		    		end else begin
			    		saturating_counter[i] <= saturating_counter[i] + 1; 
		    		end
	    		end else if (!glitchy_signal[i]) begin
		    		saturating_counter[i] <= 'b0;
	    		end
			if (wrapping_counter[i] == SAMPLE_CNT_MAX) begin
				wrapping_counter[i] <= 'b0;
			end
    		end
		
		assign debounced_signal[i] = (saturating_counter[i] == PULSE_CNT_MAX);
	    end
    endgenerate


endmodule
