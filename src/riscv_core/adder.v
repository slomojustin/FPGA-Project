module adder (
    input [31:0] din1, din2,
    output [31:0] dout
);
    assign dout = din1 + din2;
endmodule