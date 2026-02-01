module adder_constant #(
    parameter VALUE = 4
)(
    input [31:0] din,
    output [31:0] dout
);
    assign dout = din + VALUE;
endmodule