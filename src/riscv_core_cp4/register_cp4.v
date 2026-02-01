module register_cp4 (
    input [31:0] din, dreset,
    input clk,
    input rst,
    output reg [31:0] dout
);
    always @(posedge clk) begin
        if (rst) dout <= dreset;
        else dout <= din;
    end
    
endmodule