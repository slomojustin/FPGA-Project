module mux4 (
    input [1:0] sel,
    input [31:0] in_data0, in_data1, in_data2, in_data3,
    output [31:0] out_data
);
    reg [31:0] out_temp;
    always @(*) begin
        out_temp = 32'd0;
        case(sel)
            2'd0: out_temp = in_data0;
            2'd1: out_temp = in_data1;
            2'd2: out_temp = in_data2;
            2'd3: out_temp = in_data3;
        endcase    
    end
    assign out_data = out_temp;
endmodule