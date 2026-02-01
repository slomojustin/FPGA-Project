module mux2_cp4 (
    input sel,
    input [31:0] in_data0, in_data1,
    output [31:0] out_data
);
    assign out_data = (sel) ? in_data1 : in_data0;
endmodule