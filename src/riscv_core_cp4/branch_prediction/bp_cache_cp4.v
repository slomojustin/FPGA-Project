module bp_cache_cp4 #(
    parameter AWIDTH = 30,  // Address bit width after shifting (PC_WIDTH - 2)
    parameter DWIDTH = 2,   // Data bit width (saturating counter width)
    parameter LINES = 8     // Number of cache lines
) (
    input clk,
    input reset,

    // IO for 1st read port
    input [AWIDTH-1:0] ra0,
    output reg [DWIDTH-1:0] dout0,
    output reg hit0,

    // IO for 2nd read port
    input [AWIDTH-1:0] ra1,
    output reg [DWIDTH-1:0] dout1,
    output reg hit1,

    // IO for write port
    input [AWIDTH-1:0] wa,
    input [DWIDTH-1:0] din,
    input we
);

    // Cache memory structure
    localparam INDEX_BITS = $clog2(LINES);
    localparam TAG_WIDTH = AWIDTH - INDEX_BITS;

    reg [TAG_WIDTH-1:0] tags [0:LINES-1];
    reg valid [0:LINES-1];
    reg [DWIDTH-1:0] data [0:LINES-1];

    // Index extraction
    wire [INDEX_BITS-1:0] index0 = ra0[INDEX_BITS-1:0];
    wire [INDEX_BITS-1:0] index1 = ra1[INDEX_BITS-1:0];
    wire [INDEX_BITS-1:0] write_index = wa[INDEX_BITS-1:0];

    // Tag extraction
    wire [TAG_WIDTH-1:0] tag0 = ra0[AWIDTH - 1 : INDEX_BITS];
    wire [TAG_WIDTH-1:0] tag1 = ra1[AWIDTH - 1 : INDEX_BITS];
    wire [TAG_WIDTH-1:0] write_tag = wa[AWIDTH - 1 : INDEX_BITS];

    // Read port 0
    always @(*) begin
        if (valid[index0] && tags[index0] == tag0) begin
            dout0 = data[index0];
            hit0 = 1'b1;
            // $display("Read hit on port 0: index=%0d, tag=%h, data=%h", index0, tag0, data[index0]);
        end else begin
            dout0 = 'd0;
            hit0 = 1'b0;
            // $display("Read miss on port 0: index=%0d, tag=%h", index0, tag0);
        end
    end

    // Read port 1
    always @(*) begin
        if (valid[index1] && tags[index1] == tag1) begin
            dout1 = data[index1];
            hit1 = 1'b1;
            // $display("Read hit on port 1: index=%0d, tag=%h, data=%h", index1, tag1, data[index1]);
        end else begin
            dout1 = 'd0;
            hit1 = 1'b0;
            // $display("Read miss on port 1: index=%0d, tag=%h", index1, tag1);
        end
    end

    // Write to cache and reset logic
    integer i;
    always @(posedge clk) begin
        if (reset) begin
            // Reset cache
            for (i = 0; i < LINES; i = i + 1) begin
                valid[i] = 1'b0;
                tags[i] = 'd0;
                data[i] = 'd0;
                // $display("Resetting cache line %0d: valid=0", i);
            end
        end else if (we) begin
            // Write to cache
            tags[write_index] <= write_tag;
            data[write_index] <= din;
            valid[write_index] <= 1'b1;
            // $display("Writing to cache line %0d: tag=%h, data=%h", write_index, write_tag, din);
        end
    end

endmodule
