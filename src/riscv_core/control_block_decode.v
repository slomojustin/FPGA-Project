`include "opcode.vh"

module control_block_decode (
    input [31:0] inst_decode, inst_execute, inst_memory, 
    input br_pred_taken,
    output reg [2:0] imm_sel,
    output reg [1:0] rd1_forward, rd2_forward, pc_sel, 
    output reg is_br
);
    reg [6:0] opcode_decode, opcode_execute, opcode_memory, funct7_decode;
    reg [2:0] funct3_decode;
    reg inst_30_decode;
    reg [4:0] memory_rd, execute_rd, decode_rs1, decode_rs2;

always @(*) begin
        // Instruction Types Extraction
        opcode_decode = inst_decode[6:0];
        opcode_memory = inst_memory[6:0];
        opcode_execute = inst_execute[6:0];
        funct3_decode = inst_decode[14:12];
        funct7_decode = inst_decode[31:25];
        inst_30_decode = inst_decode[30];
        // Instruction Registers
        memory_rd = inst_memory[11:7];
        execute_rd = inst_execute[11:7];
        decode_rs1 = inst_decode[19:15];
        decode_rs2 = inst_decode[24:20];

        // Assignment to avoid latch synthesis (All output signals start at 0)
        pc_sel = 2'd0;
        imm_sel = 3'd0;
        //csr_sel = 1'b0;
        //csr_we = 1'b0;
        rd1_forward = 1'b0;
        rd2_forward = 1'b0;
        is_br = 1'b0;

        case(opcode_decode) 
            // R-type instructions (Updated signals: ) 
            `OPC_ARI_RTYPE: begin 
                rd1_forward = execute_rd == decode_rs1 && execute_rd != 5'd0 && (opcode_execute != `OPC_STORE && opcode_execute != `OPC_BRANCH) ? 2'd2 : (memory_rd == decode_rs1 && memory_rd != 5'd0 && (opcode_memory != `OPC_STORE && opcode_memory != `OPC_BRANCH) ? 2'd1 : 2'd0);
                rd2_forward = execute_rd == decode_rs2 && execute_rd != 5'd0 && (opcode_execute != `OPC_STORE && opcode_execute != `OPC_BRANCH) ? 2'd2 : (memory_rd == decode_rs2 && memory_rd != 5'd0 && (opcode_memory != `OPC_STORE && opcode_memory != `OPC_BRANCH) ? 2'd1 : 2'd0);
            end
                 
            // ARI I-type instructions (Updated signals: )
            `OPC_ARI_ITYPE: begin
                rd1_forward = execute_rd == decode_rs1 && execute_rd != 5'd0 && (opcode_execute != `OPC_STORE && opcode_execute != `OPC_BRANCH) ? 2'd2 : (memory_rd == decode_rs1 && memory_rd != 5'd0 && (opcode_memory != `OPC_STORE && opcode_memory != `OPC_BRANCH) ? 2'd1 : 2'd0);
                rd2_forward = execute_rd == decode_rs2 && execute_rd != 5'd0 && (opcode_execute != `OPC_STORE && opcode_execute != `OPC_BRANCH) ? 2'd2 : (memory_rd == decode_rs2 && memory_rd != 5'd0 && (opcode_memory != `OPC_STORE && opcode_memory != `OPC_BRANCH) ? 2'd1 : 2'd0);
            end

            // Load I-type instructions (Updated signals: , )
            `OPC_LOAD: begin
                rd1_forward = execute_rd == decode_rs1 && execute_rd != 5'd0 && (opcode_execute != `OPC_STORE && opcode_execute != `OPC_BRANCH) ? 2'd2 : (memory_rd == decode_rs1 && memory_rd != 5'd0 && (opcode_memory != `OPC_STORE && opcode_memory != `OPC_BRANCH) ? 2'd1 : 2'd0);
                rd2_forward = execute_rd == decode_rs2 && execute_rd != 5'd0 && (opcode_execute != `OPC_STORE && opcode_execute != `OPC_BRANCH) ? 2'd2 : (memory_rd == decode_rs2 && memory_rd != 5'd0 && (opcode_memory != `OPC_STORE && opcode_memory != `OPC_BRANCH) ? 2'd1 : 2'd0);    
            end

            // JALR I-type instruction (Updated signals:, )
            `OPC_JALR: begin
                rd1_forward = execute_rd == decode_rs1 && execute_rd != 5'd0 && (opcode_execute != `OPC_STORE && opcode_execute != `OPC_BRANCH) ? 2'd2 : (memory_rd == decode_rs1 && memory_rd != 5'd0 && (opcode_memory != `OPC_STORE && opcode_memory != `OPC_BRANCH) ? 2'd1 : 2'd0);
                rd2_forward = execute_rd == decode_rs2 && execute_rd != 5'd0 && (opcode_execute != `OPC_STORE && opcode_execute != `OPC_BRANCH) ? 2'd2 : (memory_rd == decode_rs2 && memory_rd != 5'd0 && (opcode_memory != `OPC_STORE && opcode_memory != `OPC_BRANCH) ? 2'd1 : 2'd0);
            end

            // S-type instructions (Updated signals: None)
            `OPC_STORE: begin
                rd1_forward = execute_rd == decode_rs1 && execute_rd != 5'd0 && (opcode_execute != `OPC_STORE && opcode_execute != `OPC_BRANCH) ? 2'd2 : (memory_rd == decode_rs1 && memory_rd != 5'd0 && (opcode_memory != `OPC_STORE && opcode_memory != `OPC_BRANCH) ? 2'd1 : 2'd0);
                rd2_forward = execute_rd == decode_rs2 && execute_rd != 5'd0 && (opcode_execute != `OPC_STORE && opcode_execute != `OPC_BRANCH) ? 2'd2 : (memory_rd == decode_rs2 && memory_rd != 5'd0 && (opcode_memory != `OPC_STORE && opcode_memory != `OPC_BRANCH) ? 2'd1 : 2'd0);
                imm_sel = 3'd1;
            end

            // B-type instructions (Updated signals: None)
            `OPC_BRANCH: begin
                rd1_forward = execute_rd == decode_rs1 && execute_rd != 5'd0 && (opcode_execute != `OPC_STORE && opcode_execute != `OPC_BRANCH) ? 2'd2 : (memory_rd == decode_rs1 && memory_rd != 5'd0 && (opcode_memory != `OPC_STORE && opcode_memory != `OPC_BRANCH) ? 2'd1 : 2'd0);
                rd2_forward = execute_rd == decode_rs2 && execute_rd != 5'd0 && (opcode_execute != `OPC_STORE && opcode_execute != `OPC_BRANCH) ? 2'd2 : (memory_rd == decode_rs2 && memory_rd != 5'd0 && (opcode_memory != `OPC_STORE && opcode_memory != `OPC_BRANCH) ? 2'd1 : 2'd0);     
                imm_sel = 3'b010;                       // B-Type immediate
                is_br = 1'b1;
                pc_sel = {br_pred_taken, 1'b0};                                
            end

            // J-type instruction (Updated signals: , )
            `OPC_JAL: begin
                rd1_forward = execute_rd == decode_rs1 && execute_rd != 5'd0 && (opcode_execute != `OPC_STORE && opcode_execute != `OPC_BRANCH) ? 2'd2 : (memory_rd == decode_rs1 && memory_rd != 5'd0 && (opcode_memory != `OPC_STORE && opcode_memory != `OPC_BRANCH) ? 2'd1 : 2'd0);
                rd2_forward = execute_rd == decode_rs2 && execute_rd != 5'd0 && (opcode_execute != `OPC_STORE && opcode_execute != `OPC_BRANCH) ? 2'd2 : (memory_rd == decode_rs2 && memory_rd != 5'd0 && (opcode_memory != `OPC_STORE && opcode_memory != `OPC_BRANCH) ? 2'd1 : 2'd0);
                imm_sel = 3'b100;                                       // J-Type immediate
            end

            // U-Type instruction (Updated signals: )
            `OPC_AUIPC: begin
                rd1_forward = execute_rd == decode_rs1 && execute_rd != 5'd0 && (opcode_execute != `OPC_STORE && opcode_execute != `OPC_BRANCH) ? 2'd2 : (memory_rd == decode_rs1 && memory_rd != 5'd0 && (opcode_memory != `OPC_STORE && opcode_memory != `OPC_BRANCH) ? 2'd1 : 2'd0);
                rd2_forward = execute_rd == decode_rs2 && execute_rd != 5'd0 && (opcode_execute != `OPC_STORE && opcode_execute != `OPC_BRANCH) ? 2'd2 : (memory_rd == decode_rs2 && memory_rd != 5'd0 && (opcode_memory != `OPC_STORE && opcode_memory != `OPC_BRANCH) ? 2'd1 : 2'd0);
                imm_sel = 3'b011;                                       // U-Type immediate
            end

            // U-Type instruction (Updated signals: )
            `OPC_LUI: begin 
                rd1_forward = execute_rd == decode_rs1 && execute_rd != 5'd0 && (opcode_execute != `OPC_STORE && opcode_execute != `OPC_BRANCH) ? 2'd2 : (memory_rd == decode_rs1 && memory_rd != 5'd0 && (opcode_memory != `OPC_STORE && opcode_memory != `OPC_BRANCH) ? 2'd1 : 2'd0);
                rd2_forward = execute_rd == decode_rs2 && execute_rd != 5'd0 && (opcode_execute != `OPC_STORE && opcode_execute != `OPC_BRANCH) ? 2'd2 : (memory_rd == decode_rs2 && memory_rd != 5'd0 && (opcode_memory != `OPC_STORE && opcode_memory != `OPC_BRANCH) ? 2'd1 : 2'd0);     
                imm_sel = 3'b011;                                       // U-Type immediate                                     
            end

            `OPC_CSR: begin
                rd1_forward = execute_rd == decode_rs1 && execute_rd != 5'd0 && (opcode_execute != `OPC_STORE && opcode_execute != `OPC_BRANCH) ? 2'd2 : (memory_rd == decode_rs1 && memory_rd != 5'd0 && (opcode_memory != `OPC_STORE && opcode_memory != `OPC_BRANCH) ? 2'd1 : 2'd0);
                rd2_forward = execute_rd == decode_rs2 && execute_rd != 5'd0 && (opcode_execute != `OPC_STORE && opcode_execute != `OPC_BRANCH) ? 2'd2 : (memory_rd == decode_rs2 && memory_rd != 5'd0 && (opcode_memory != `OPC_STORE && opcode_memory != `OPC_BRANCH) ? 2'd1 : 2'd0);
                imm_sel = 3'b101;                                       // CSR Type immediate
                //csr_sel = funct3_decode[2];
                //csr_we = 1'b1;
            end        
            default: begin
                
            end
        endcase
    end
endmodule