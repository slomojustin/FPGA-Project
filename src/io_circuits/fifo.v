module fifo #(
    parameter WIDTH = 8,
    parameter DEPTH = 32,
    parameter POINTER_WIDTH = $clog2(DEPTH)
) (
    input clk, rst,

    // Write side
    input wr_en,
    input [WIDTH-1:0] din,
    output full,

    // Read side
    input rd_en,
    output [WIDTH-1:0] dout,
    output empty
);

    reg [WIDTH-1:0] memory [DEPTH-1:0];
    reg [POINTER_WIDTH:0] wr_ctr;
    reg [POINTER_WIDTH:0] rd_ctr;
    reg [POINTER_WIDTH:0] rd_wr_difference;
    reg [WIDTH-1:0] rd_out;

    always @ (posedge clk) begin
        if (rst) begin
            wr_ctr <= 0;
            rd_ctr <= 0;
            rd_wr_difference <= 0;
            rd_out <= 0;
        end else begin
            if (wr_en && !full && !rd_en) begin
                memory[wr_ctr] <= din;
                if (wr_ctr < DEPTH - 1) wr_ctr <= wr_ctr + 1;
                else wr_ctr <= 0;
                rd_wr_difference <= rd_wr_difference + 1;
            end
            if (rd_en && !empty && !wr_en) begin
                rd_out <= memory[rd_ctr];
                if (rd_ctr < DEPTH - 1) rd_ctr <= rd_ctr + 1;
                else rd_ctr <= 0;
                rd_wr_difference <= rd_wr_difference - 1;
            end
            if (wr_en && rd_en && !full && !empty) begin
                memory[wr_ctr] <= din;
                if (wr_ctr < DEPTH - 1) wr_ctr <= wr_ctr + 1;
                else wr_ctr <= 0;
                rd_out <= memory[rd_ctr];
                if (rd_ctr < DEPTH - 1) rd_ctr <= rd_ctr + 1;
                else rd_ctr <= 0;
            end
        end
    end

    assign full = ((wr_ctr == rd_ctr) && (rd_wr_difference == DEPTH)) ? 1 : 0;
    assign empty = ((wr_ctr == rd_ctr) && (rd_wr_difference == 0)) ? 1 : 0;
    assign dout = rd_out;

    /*
    assert 
        property (
            @(posedge clk) disable iff (rst) 
            (full && wr_en) |-> $stable(wr_ctr)
        )
        else 
            $error("Write pointer changed while FIFO was full");
    assert 
        property (
            @(posedge clk) disable iff (rst) 
            (empty && rd_en) |-> $stable(rd_ctr)
        )
        else
            $error("Read pointer changed while FIFO was empty");
    assert 
        property (
            @(posedge clk) 
            rst |-> (!$countones(wr_ctr) && !$countones(rd_ctr))
        )
        else
            $error("Read and Write Pointer not set to 0 on reset");
    assert 
        property (
            @(posedge clk) 
            rst |=> !full
        )
        else
            $error("full not deasserted on reset");
    */
endmodule
