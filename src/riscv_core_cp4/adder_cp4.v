module adder_cp4 #(
    parameter WIDTH = 32
)(
    input enable, imm_signed,
    input [WIDTH-1:0] din1, din2,
    output [WIDTH-1:0] dout
);
    
    assign dout[1:0] = din1[1:0] + din2[1:0];
    assign dout[WIDTH-1:2] = din1[WIDTH-1:2] + din2[WIDTH-1:2];
endmodule