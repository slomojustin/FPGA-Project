module immediate_generator (
    input [31:0] instruction,
    input [2:0] imm_type,
    output reg [31:0] imm_out
);

    always @(*) begin
        case (imm_type)
            // I-Type immediate, JALR instruction
            3'b000: begin 
                imm_out = {{20{instruction[31]}}, instruction[31:20]};
            end
            3'b001: begin // S-Type immediate
                imm_out = {{20{instruction[31]}}, instruction[31:25], instruction[11:7]};
            end
            3'b010: begin // B-Type immediate
                imm_out = {{19{instruction[31]}}, instruction[31], instruction[7], instruction[30:25], instruction[11:8], 1'b0};
            end
            3'b011: begin // U-Type immediate
                imm_out = {instruction[31:12], 12'd0};
            end
            3'b100: begin // J-Type immediate, JAL instruction
                imm_out = {{12{instruction[31]}}, instruction[19:12], instruction[20], instruction[30:21], 1'b0};
            end
            3'b101: begin // CSR Type immediate
                imm_out = {27'd0 ,instruction[19:15]};
            end
            default: begin
                imm_out = 32'd0; 
            end
        endcase
    end
endmodule