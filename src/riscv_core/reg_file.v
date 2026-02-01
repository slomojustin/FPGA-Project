module reg_file (
    input clk,
    input we,
    input [4:0] ra1, ra2, wa,
    input [31:0] wd,
    output [31:0] rd1, rd2
);
    parameter DEPTH = 32;
    reg [31:0] mem [31:0];
    
    // Synchronous Write, Only writes when we is asserted and wa is not zero.
    always @ (posedge clk) begin
        mem[0] = 32'b0;
        if (we && (wa != 5'b0)) mem[wa] <= wd;
    end
    // Asynchronous Read, passes data at ra1 and ra2 to rd1 and rd2 respectively.
    assign rd1 = mem[ra1];
    assign rd2 = mem[ra2];

    // System verilog
    // Assertion 4: The x0 register should always be 0.
    /*
    assert
        property (
            @(posedge clk)
            we |-> $stable(mem[0])
        )
        else 
            $error("Register x0's value changedfrom 0");
    */
endmodule
