`include "opcode.vh"

module control_block_memory_cp4 (
    input [31:0] inst_memory, mem_addr,
    
    output reg [2:0] load_type,
    output reg [1:0] wb_sel, byte_addr,
    output reg [1:0] mem_sel, io_sel, counter_sel,
    output reg reg_we, uart_tx_data_in_v, io_reset
);
    reg [6:0] opcode_memory, funct7_memory;
    reg [2:0] funct3_memory;
    reg inst_30_memory;

    // Two options: Large case statement for all outputs or assign each output using structural verilog and gate logic.
    // If second option, need to rework previous logic to account for branch prediction and forwarding, bios, and possibly uart
    // logic that needs to change: a_sel, b_sel
    // logic that needs to be added: inst_sel, br_forward, mem_forward, csr_sel, imem_we

    always @(*) begin
        // Instruction Types Extraction
        opcode_memory = inst_memory[6:0];
        funct3_memory = inst_memory[14:12];
        funct7_memory = inst_memory[31:25];
        inst_30_memory = inst_memory[30];
        // Instruction Registers

        // Assignment to avoid latch synthesis (All output signals start at 0)
        wb_sel = 2'd1;      // ALU writeback
        mem_sel = 2'd0;     // DMEM
        reg_we = 1'b0;   
        load_type = 3'd0;
        byte_addr = 2'd0;
        io_sel = 2'd0;
        uart_tx_data_in_v= 1'd0;
        counter_sel = 2'd0;
        io_reset = 1'b0;

        case(opcode_memory) 
            // R-type instructions (Updated signals: reg_we) 
            `OPC_ARI_RTYPE: begin 
                reg_we = 1'd1;                                          // Register Write Enable
            end
                 
            // ARI I-type instructions (Updated signals: reg_we)
            `OPC_ARI_ITYPE: begin
                reg_we = 1'd1;                                          // Register Write Enable
            end

            // Load I-type instructions (Updated signals: wb_sel, reg_we)
            `OPC_LOAD: begin
                wb_sel = 2'd0;                                          // Mem writeback
                reg_we = 1'b1;                                          // Register Write Enable
                load_type = funct3_memory;
                byte_addr = mem_addr[1:0];
                mem_sel = (mem_addr[31:28] == 4'b1000) ? 2'd2 : ((mem_addr[31:28] == 4'b0100) ? 2'd1 : 2'd0);
                case(mem_addr)
                    32'h80000000: io_sel = 2'd0;                        // UART Control
                    32'h80000004: io_sel = 2'd1;                        // UART Receiver
                    32'h80000010: begin                                 // Cycle Counter
                        io_sel = 2'd2;
                        counter_sel = 2'd0;    
                    end                    
                    32'h80000014: begin                                 // Instruction Counter
                        io_sel = 2'd2;
                        counter_sel = 2'd1;     
                    end                                 
                    32'h8000001c: begin                                 // Branch Counter
                        io_sel = 2'd2;  
                        counter_sel = 2'd2;   
                    end          
                    32'h80000020: begin                                 // Accuracy Counter
                        io_sel = 2'd2; 
                        counter_sel = 2'd3;    
                    end          
                endcase

            end

            // JALR I-type instruction (Updated signals:wb_sel, reg_we)
            `OPC_JALR: begin
                wb_sel = 2'd2;                                          // PC+4 writeback
                reg_we = 1'b1;                                          // Register Write Enable
            end

            // S-type instructions (Updated signals: None)
            `OPC_STORE: begin 
                uart_tx_data_in_v = (mem_addr == 32'h80000008) ? 1'b1 : 1'b0;
                io_reset = (mem_addr == 32'h80000018) ? 1'b1 : 1'b0;
            end

            // B-type instructions (Updated signals: None)
            `OPC_BRANCH: begin     
                
            end

            // J-type instruction (Updated signals: wb_sel, reg_we)
            `OPC_JAL: begin
                wb_sel = 2'd2;                                          // PC+4 writeback
                reg_we = 1'b1;                                          // Register Write Enable
            end

            // U-Type instruction (Updated signals: reg_we)
            `OPC_AUIPC: begin
                reg_we = 1'b1;                                          // Register Write Enable
            end

            // U-Type instruction (Updated signals: reg_we)
            `OPC_LUI: begin
                reg_we = 1'b1;                                          // Register Write Enable                                               
            end

            `OPC_CSR: begin
                
            end        
            default: begin
                
            end
        endcase
    end
endmodule