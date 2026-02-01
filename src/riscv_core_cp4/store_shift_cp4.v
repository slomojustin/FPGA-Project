module store_shift_cp4 (
    input [31:0] memory_data,
    input [1:0] shift,
    output [31:0] shifted_data
);
    assign shifted_data = memory_data << (shift*8);

endmodule