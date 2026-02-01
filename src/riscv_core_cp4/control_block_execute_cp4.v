`include "opcode.vh"

module control_block_execute_cp4 (
    input [31:0] inst_execute, inst_memory, mem_addr, pc_decode,
    input bp_en, br_eq, br_lt, br_pred_taken,
    output reg br_un,
    output reg [3:0] alu_sel,
    output reg [1:0] a_sel, b_sel, shift, pc_sel,
    output reg br_forward, mem_forward, is_br, br_taken, execute_hazard,
    output reg bios_reb, uart_rx_data_out_r, csr_sel, csr_we, dmem_re, imem_re
);
    reg [6:0] opcode_execute, opcode_memory, funct7_execute;
    reg [2:0] funct3_execute;
    reg inst_30_execute;
    reg [4:0] memory_rd, execute_rs1, execute_rs2;
    reg [1:0] execute_hazard_rs1, execute_hazard_rs2;

    // Two options: Large case statement for all outputs or assign each output using structural verilog and gate logic.
    // If second option, need to rework previous logic to account for branch prediction and forwarding, bios, and possibly uart
    // logic that needs to change: a_sel, b_sel
    // logic that needs to be added: inst_sel, br_forward, mem_forward, csr_sel, imem_we

    always @(*) begin
        // Instruction Types Extraction
        opcode_execute = inst_execute[6:0];
        opcode_memory = inst_memory[6:0];
        funct3_execute = inst_execute[14:12];
        funct7_execute = inst_execute[31:25];
        inst_30_execute = inst_execute[30];
        // Instruction Registers
        memory_rd = inst_memory[11:7];
        execute_rs1 = inst_execute[19:15];
        execute_rs2 = inst_execute[24:20];

        // Assignment to avoid latch synthesis (All output signals start at 0)
        pc_sel = 2'd0;                          // PC+4
        alu_sel = 4'd0;                         // Add
        execute_hazard = 1'd0;                      // Next Instruction
        a_sel = 2'd0;                           // rs1
        b_sel = 2'd0;                           // rs2
        br_forward = 1'b0;                      // rs1
        mem_forward = 1'b0;                     // rs2      
        br_un = 1'b0;
        dmem_re = 1'b1;
        imem_re = 1'b0;
        bios_reb = 1'b0;
        shift = 2'b0;
        //io_reset = 1'b0;
        uart_rx_data_out_r = 1'b0;
        is_br = 1'b0;
        br_taken = 1'b0;

        csr_sel = 1'b0;
        csr_we = 1'b0;

        execute_hazard_rs1 = 2'd0;
        execute_hazard_rs2 = 2'd0;
        

        case(opcode_execute) 
            // R-type inst*/ructions (Updated signals: alu_sel, wb_sel) (Potential Forwarding: a_sel, b_sel)
            `OPC_ARI_RTYPE: begin 
                alu_sel = {inst_30_execute, funct3_execute};                            
                //a_sel = (memory_rd == execute_rs1 && memory_rd != 5'd0 && (opcode_memory != `OPC_STORE && opcode_memory != `OPC_BRANCH)) ? 1'd1 : 2'd0;        // rs1 or Forward data
                //b_sel = (memory_rd == execute_rs2 && memory_rd != 5'd0 && (opcode_memory != `OPC_STORE && opcode_memory != `OPC_BRANCH)) ? 1'd1 : 2'd0;        // rs2 or Forward data
                execute_hazard_rs1 = (memory_rd == execute_rs1 && memory_rd != 5'd0 && (opcode_memory != `OPC_STORE && opcode_memory != `OPC_BRANCH)) ? 1'd1 : 2'd0;
                execute_hazard_rs2 = (memory_rd == execute_rs2 && memory_rd != 5'd0 && (opcode_memory != `OPC_STORE && opcode_memory != `OPC_BRANCH)) ? 1'd1 : 2'd0;
                execute_hazard = execute_hazard_rs1 | execute_hazard_rs2;
            end
                 
            // ARI I-type instructions (Updated signals: imm_sel, b_sel, alu_sel, wb_sel) (Potential Forwarding: a_sel)
            `OPC_ARI_ITYPE: begin
                if (funct3_execute == `FNC_SLL || funct3_execute == `FNC_SRL_SRA) begin
                    alu_sel = {inst_30_execute, funct3_execute};
                end else alu_sel = {1'b0, funct3_execute};
                //a_sel = (memory_rd == execute_rs1 && memory_rd != 5'd0 && (opcode_memory != `OPC_STORE && opcode_memory != `OPC_BRANCH)) ? 1'd1 : 2'd0;        // rs1 or Forward data
                b_sel = 2'd1;                                           // Immediate Generator
                execute_hazard_rs1 = (memory_rd == execute_rs1 && memory_rd != 5'd0 && (opcode_memory != `OPC_STORE && opcode_memory != `OPC_BRANCH)) ? 1'd1 : 2'd0;
                execute_hazard = execute_hazard_rs1;
            end

            // Load I-type instructions (Updated signals: imm_sel, b_sel, dmem_re) (Potential Forwarding: a_sel)
            `OPC_LOAD: begin
                //a_sel = (memory_rd == execute_rs1 && memory_rd != 5'd0 && (opcode_memory != `OPC_STORE && opcode_memory != `OPC_BRANCH)) ? 1'd1 : 2'd0;        // rs1 or Forward data
                b_sel = 2'd1;                                           // Immediate Generator
                //dmem_re = 1'b1;                                         // Enable DMEM Read
                bios_reb = 1'b1;
                uart_rx_data_out_r = (mem_addr == 32'h80000004) ? 1'b1 : 1'b0;
                execute_hazard_rs1 = (memory_rd == execute_rs1 && memory_rd != 5'd0 && (opcode_memory != `OPC_STORE && opcode_memory != `OPC_BRANCH)) ? 1'd1 : 2'd0;
                execute_hazard = execute_hazard_rs1;
            end

            // JALR I-type instructions (Updated signals:b_sel, pc_sel, imm_sel) (Potential Forwarding:a_sel)
            `OPC_JALR: begin
                //a_sel = (memory_rd == execute_rs1 && memory_rd != 5'd0 && (opcode_memory != `OPC_STORE && opcode_memory != `OPC_BRANCH)) ? 1'd1 : 2'd0;        // rs1 or Forward data
                b_sel = 2'd1;                                           // Immediate Generator
                execute_hazard_rs1 = (memory_rd == execute_rs1 && memory_rd != 5'd0 && (opcode_memory != `OPC_STORE && opcode_memory != `OPC_BRANCH)) ? 1'd1 : 2'd0;
                pc_sel = 1'd1;
            end

            // S-type instructions (Updated signals: imm_sel, b_sel, dmem_we, imem_we) (Potential forwarding: a_sel, mem_forward)
            `OPC_STORE: begin 
                //a_sel = (memory_rd == execute_rs1 && memory_rd != 5'd0 && (opcode_memory != `OPC_STORE && opcode_memory != `OPC_BRANCH)) ? 1'd1 : 2'd0;        // rs1 or Forward data
                //mem_forward = ((memory_rd == execute_rs2) && (opcode_memory != `OPC_STORE && opcode_memory != `OPC_BRANCH) && memory_rd != 5'd0) ? 1'b1 : 1'b0;  // rs2 or Forward data
                execute_hazard_rs1 = (memory_rd == execute_rs1 && memory_rd != 5'd0 && (opcode_memory != `OPC_STORE && opcode_memory != `OPC_BRANCH)) ? 1'd1 : 2'd0;
                execute_hazard_rs2 = (memory_rd == execute_rs2 && memory_rd != 5'd0 && (opcode_memory != `OPC_STORE && opcode_memory != `OPC_BRANCH)) ? 1'd1 : 2'd0;
                execute_hazard = execute_hazard_rs1 | execute_hazard_rs2;
                b_sel = 2'd1;                                           
                //io_reset = (mem_addr == 32'h80000018) ? 1'b1 : 1'b0;
                imem_re = pc_decode[30];
            end

            `OPC_BRANCH: begin //(Updated signals: a_sel, b_sel, br_un) (Potential forwarding: br_forward, mem_forward)       
                a_sel = 2'd1;                                                           // PC+4
                b_sel = 2'd1;                                                           // Immediate Generator
                //br_forward = (memory_rd == execute_rs1 && memory_rd != 5'd0 && (opcode_memory != `OPC_STORE && opcode_memory != `OPC_BRANCH)) ? 1'b1 : 1'b0;                   // rs1 or Forward data               
                //mem_forward = (memory_rd == execute_rs2 && memory_rd != 5'd0 && (opcode_memory != `OPC_STORE && opcode_memory != `OPC_BRANCH)) ? 1'b1 : 1'b0;                  // rs2 or Forward data
                execute_hazard_rs1 = (memory_rd == execute_rs1 && memory_rd != 5'd0 && (opcode_memory != `OPC_STORE && opcode_memory != `OPC_BRANCH)) ? 1'd1 : 2'd0;
                execute_hazard_rs2 = (memory_rd == execute_rs2 && memory_rd != 5'd0 && (opcode_memory != `OPC_STORE && opcode_memory != `OPC_BRANCH)) ? 1'd1 : 2'd0;
                execute_hazard = execute_hazard_rs1 | execute_hazard_rs2;
                br_un = (funct3_execute == `FNC_BLTU || funct3_execute == `FNC_BGEU);     // Unsigned if BLTU/BGEU                
                is_br = 1'b1;
                case(funct3_execute)                                                     // PC dependent on branch comparator
                    `FNC_BEQ: pc_sel = br_eq;
                    `FNC_BNE: pc_sel = !br_eq;
                    `FNC_BLT: pc_sel = !br_eq & br_lt;
                    `FNC_BGE: pc_sel = br_eq | !br_lt;
                    `FNC_BLTU: pc_sel = !br_eq & br_lt;
                    `FNC_BGEU: pc_sel = br_eq | !br_lt;
                endcase
            
                // case(funct3_execute)                                                     // PC dependent on branch comparator
                //     `FNC_BEQ: br_taken = br_eq;
                //     `FNC_BNE: br_taken = !br_eq;
                //     `FNC_BLT: br_taken = !br_eq & br_lt;
                //     `FNC_BGE: br_taken = br_eq | !br_lt;
                //     `FNC_BLTU: br_taken = !br_eq & br_lt;
                //     `FNC_BGEU: br_taken = br_eq | !br_lt;
                // endcase
                // pc_sel[1] = ((bp_en & br_pred_taken & !br_taken) ? 1'b1 : 1'b0);
            end

            `OPC_JAL: begin
                pc_sel = 1'd1;                                          // ALU
                a_sel = 2'd1;                                           // PC+4
                b_sel = 2'd1;                                           // Immediate Generator                   
                
            end

            `OPC_AUIPC: begin
                a_sel = 2'd1;                                           // PC+4
                b_sel = 2'd1;                                           // Immediate Generator
                
            end

            `OPC_LUI: begin
                alu_sel = 4'b1111;                                      // Pass B
                b_sel = 2'd1;                                           // Immediate Generator
                                                               
            end

            `OPC_CSR: begin
                //a_sel = (memory_rd == execute_rs1 && memory_rd != 5'd0 && (opcode_memory != `OPC_STORE && opcode_memory != `OPC_BRANCH)) ? 1'd1 : 2'd0;        // rs1 or Forward data
                execute_hazard_rs1 = (memory_rd == execute_rs1 && memory_rd != 5'd0 && (opcode_memory != `OPC_STORE && opcode_memory != `OPC_BRANCH)) ? 1'd1 : 2'd0;
                execute_hazard = execute_hazard_rs1;
                csr_sel = funct3_execute[2];
                csr_we = 1'b1;
            end        
            default: begin
                
            end
        endcase
    end

    
endmodule
