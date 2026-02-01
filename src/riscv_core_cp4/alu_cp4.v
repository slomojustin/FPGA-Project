module alu_cp4 (
    input [31:0] Asel,
    input [31:0] Bsel,
    input [3:0] alu_op,
    output reg [31:0] rd,
    output zero //zero flag  
);

assign zero = (rd == 32'b0); //zero flag

    localparam
        add     = 4'b0000,  // Addition, 
        sub     = 4'b1000,  // Subtraction (Changed from 1100 to 1000)
        and_op  = 4'b0111,  // Bitwise AND, 'and' is a reserved keyword
        or_op   = 4'b0110,  // Bitwise OR, 'or' is a reserved keyword
        xor_op   = 4'b0100, // Bitwise XOR 
        sll   = 4'b0001,    // Shift Left Logical 
        srl   = 4'b0101,    // Shift Right Logical, changed code because conflict with op_op
        sra   = 4'b1101,    // Shift Right Arithmetic 
        slt   = 4'b0010,    // Set Less Than
        sltu = 4'b0011,     // Set Less Than Unsigned
        pass_b = 4'b1111;    // Pass Value at Mux B

    always @(*) begin
        case(alu_op)
            add:  rd = Asel + Bsel; 
            sub:  rd = Asel - Bsel;
            and_op:  rd = Asel & Bsel;
            or_op:   rd = Asel | Bsel;
            xor_op:  rd = Asel ^ Bsel;
            sll:  rd = Asel << Bsel[4:0]; // Shift amount lower 5 bits
            srl:  rd = Asel >> Bsel[4:0];
            sra:  rd = $signed(Asel) >>> Bsel[4:0]; // Arithmetic shift right (preserves sign)
            slt:  rd = ($signed(Asel) < $signed(Bsel)) ? 32'b1 : 32'b0;
            sltu: rd = Asel < Bsel ? 32'b1 : 32'b0;
            pass_b: rd = Bsel;
            default: rd = 32'b0;
        endcase
    end
endmodule