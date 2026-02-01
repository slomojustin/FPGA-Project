/*
A saturating incrementer/decrementer.
Adds +/-1 to the input with saturation to prevent overflow.
*/

module sat_updn #(
    parameter WIDTH = 2
) (
    input  [WIDTH-1:0] in,
    input              up,
    input              dn,

    output [WIDTH-1:0] out
);
    // Saturating increment/decrement logic
    reg [WIDTH-1:0] out_tmp;

    always @(*) begin
        if (up && !dn) begin
            if (in == {WIDTH{1'b1}}) // Maximum value
                out_tmp = in;
            else
                out_tmp = in + 1;
        end else if (!up && dn) begin
            if (in == {WIDTH{1'b0}}) // Minimum value
                out_tmp = in;
            else
                out_tmp = in - 1;
        end else begin
            // No change if both signals are asserted or neither is asserted
            out_tmp = in;
        end
    end

    assign out = out_tmp;

endmodule
