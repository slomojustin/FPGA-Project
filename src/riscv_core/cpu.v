`include "opcode.vh"

module cpu_cp3 #(
    parameter CPU_CLOCK_FREQ = 50_000_000,
    parameter RESET_PC = 32'h4000_0000,
    parameter BAUD_RATE = 115200
) (
    input clk,
    input rst,
    input bp_enable,
    input serial_in,
    output serial_out
);

    // BIOS Memory
    // Synchronous read: read takes one cycle
    // Synchronous write: write takes one cycle
    wire [11:0] bios_addra, bios_addrb;
    wire [31:0] bios_douta, bios_doutb;
    wire bios_ena, bios_enb;
    bios_mem bios_mem (
      .clk(clk),
      .ena(bios_ena),
      .addra(bios_addra),
      .douta(bios_douta),
      .enb(bios_enb),
      .addrb(bios_addrb),
      .doutb(bios_doutb)
    );

    // Data Memory
    // Synchronous read: read takes one cycle
    // Synchronous write: write takes one cycle
    // Write-byte-enable: select which of the four bytes to write
    wire [13:0] dmem_addr;
    wire [31:0] dmem_din, dmem_dout;
    wire [3:0] dmem_we;
    wire dmem_en;
    dmem dmem (
      .clk(clk),
      .en(dmem_en),
      .we(dmem_we),
      .addr(dmem_addr),
      .din(dmem_din),
      .dout(dmem_dout)
    );

    // Instruction Memory
    // Synchronous read: read takes one cycle
    // Synchronous write: write takes one cycle
    // Write-byte-enable: select which of the four bytes to write
    wire [31:0] imem_dina, imem_doutb;
    wire [13:0] imem_addra, imem_addrb;
    wire [3:0] imem_wea;
    wire imem_ena;
    imem imem (
      .clk(clk),
      .ena(imem_ena),
      .wea(imem_wea),
      .addra(imem_addra),
      .dina(imem_dina),
      .addrb(imem_addrb),
      .doutb(imem_doutb)
    );

    // Register file
    // Asynchronous read: read data is available in the same cycle
    // Synchronous write: write takes one cycle
    wire we;
    wire [4:0] ra1, ra2, wa;
    wire [31:0] wd;
    wire [31:0] rd1, rd2;
    reg_file rf (
        .clk(clk),
        .we(we),
        .ra1(ra1), .ra2(ra2), .wa(wa),
        .wd(wd),
        .rd1(rd1), .rd2(rd2)
    );

    // On-chip UART
    //// UART Receiver
    wire [7:0] uart_rx_data_out;
    wire uart_rx_data_out_valid;
    wire uart_rx_data_out_ready;
    //// UART Transmitter
    wire [7:0] uart_tx_data_in;
    wire uart_tx_data_in_valid;
    wire uart_tx_data_in_ready;
    uart #(
        .CLOCK_FREQ(CPU_CLOCK_FREQ),
        .BAUD_RATE(BAUD_RATE)
    ) on_chip_uart (
        .clk(clk),
        .reset(rst),

        .serial_in(serial_in),
        .data_out(uart_rx_data_out),
        .data_out_valid(uart_rx_data_out_valid),
        .data_out_ready(uart_rx_data_out_ready),

        .serial_out(serial_out),
        .data_in(uart_tx_data_in),
        .data_in_valid(uart_tx_data_in_valid),
        .data_in_ready(uart_tx_data_in_ready)
    );

    reg [31:0] tohost_csr = 0;

    // TODO: Your code to implement a fully functioning RISC-V core
    reg [31:0] pc;
    reg [31:0] pc_pipeline_decode;
    reg [31:0] pc_pipeline_execute;
    reg [31:0] pc_4_pipeline_memory;
    reg [31:0] alu_pipeline_memory;
    reg [31:0] rd1_pipeline;
    reg [31:0] rd2_pipeline;
    reg [31:0] immediate_pipeline_execute;
    reg [31:0] instruction_memory;
    reg [31:0] instruction_execute_initial;
    reg [1:0] prev_pc_sel = 2'd0;

    // Wires
    // Decode Control
    wire [1:0] rd1_forward, rd2_forward, pc_sel, pc_sel_decode, pc_sel_exe;
    wire [2:0] imm_sel;
    wire csr_sel, inst_sel, csr_we;

    // Execute Control
    wire [3:0] alu_sel;
    wire [1:0] a_sel, b_sel, shift;
    wire br_un, br_forward, mem_forward, bubble_sel;

    // Memory Control
    wire [2:0] load_type;
    wire [1:0] wb_sel, byte_addr, mem_sel, io_sel, counter_sel;
    wire reg_we; 

    // Module Output Wires
    wire [31:0] dmem_dout_masked;
    wire [31:0] bios_dout_masked;
    wire [31:0] imm_dout;
    wire [31:0] alu_dout;
    wire [31:0] mem_data_shifted;
    wire zero_flag;
    wire br_eq, br_lt;

    // Mux Output Wires
    wire [31:0] pc_4, next_pc;
    wire [31:0] initial_instruction;
    wire [31:0] instruction_decode;
    wire [31:0] instruction_execute;
    wire [31:0] rd1_data;
    wire [31:0] rd2_data;
    wire [31:0] a_data;
    wire [31:0] b_data;
    wire [31:0] br_data;
    wire [31:0] mem_data;
    wire [31:0] csr_data;
    wire [31:0] mem_dout;
    wire [31:0] wb_data;
    wire [31:0] io_data;
    wire [31:0] counter_data;

    // Pipeline Wires
    wire [31:0] pc_4_pipeline_execute;

    // I/O Registers
    reg [31:0] cycle_counter;
    reg [31:0] instruction_counter;
    reg [31:0] branch_counter;
    reg [31:0] br_accuracy_counter;
    reg [31:0] uart_control;
    reg [31:0] uart_rx_data;
    reg [31:0] uart_tx_data;

    // I/O Wires
    wire io_reset;

    // Branch Prediction
    wire [31:0] bp_pc;

    wire [31:0] pc_guess;
    wire [31:0] pc_check;
    wire is_br_guess;
    wire is_br_check;
    wire br_taken_check;
    wire br_pred_taken;

    reg prev_br_pred_taken;

    // Multiplexors

    // PC Mux
    mux4 PC_Mux (
        .sel(pc_sel),
        .in_data0(pc_4),
        .in_data1(alu_dout),
        .in_data2(bp_pc),
        .in_data3(RESET_PC),       
        .out_data(next_pc)
    );

    // Instruction Mux
    mux2 inst_Mux (
        .sel(pc_pipeline_decode[30]),                 //Pipelined PC Decode
        .in_data0(imem_doutb),
        .in_data1(bios_douta),
        .out_data(initial_instruction)
    );

    mux2 bubble_decode_Mux (
        .sel(prev_pc_sel[1] | prev_pc_sel[0]),
        .in_data0(initial_instruction),
        .in_data1(32'h00000013),
        .out_data(instruction_decode)
    );


    mux2 bubble_exe_Mux (
        .sel(prev_pc_sel[0]),             
        .in_data0(instruction_execute_initial),
        .in_data1(32'h00000013),          // addi x0 x0 0
        .out_data(instruction_execute)
    );

    // RD1 Forward Mux
    mux4 RD1_Mux (
        .sel(rd1_forward),
        .in_data0(rd1),
        .in_data1(wb_data),
        .in_data2(alu_dout),
        .in_data3(32'd0),
        .out_data(rd1_data)
    );

    // RD2 Forward Mux
    mux4 RD2_Mux (
        .sel(rd2_forward),
        .in_data0(rd2),
        .in_data1(wb_data),
        .in_data2(alu_dout),
        .in_data3(32'd0),
        .out_data(rd2_data)
    );

    // A Mux
    mux4 A_Mux (
        .sel(a_sel),
        .in_data0(rd1_pipeline),                     // Register File
        .in_data1(pc_pipeline_execute),      // PC
        .in_data2(wb_data),                 // Forward Data
        .in_data3(32'd0),
        .out_data(a_data)
    );

    // B Mux
    mux4 B_Mux (
        .sel(b_sel),
        .in_data0(rd2_pipeline),                // Register File 
        .in_data1(immediate_pipeline_execute),           // Immediate Generator
        .in_data2(wb_data),            // Forawrd Data
        .in_data3(32'd0),
        .out_data(b_data)
    );

    // Branch Mux
    mux2 Branch_Mux (
        .sel(br_forward),
        .in_data0(rd1_pipeline),                // Register File
        .in_data1(wb_data),            // Forward Data
        .out_data(br_data)
    );

    // Memory Mux
    mux2 Memory_Mux (
        .sel(mem_forward),
        .in_data0(rd2_pipeline),                // Register File
        .in_data1(wb_data),            // Foward Data
        .out_data(mem_data)
    );

    // CSR Mux
    mux2 CSR_Mux (
        .sel(csr_sel),
        .in_data0(a_data),         // Register File
        .in_data1(immediate_pipeline_execute),     // Immediate Generator
        .out_data(csr_data)
    );

    // Counter Mux
    mux4 counter_mux (
        .sel(counter_sel),
        .in_data0(cycle_counter),
        .in_data1(instruction_counter),
        .in_data2(branch_counter),
        .in_data3(br_accuracy_counter),
        .out_data(counter_data)
    );

    // I/O Mux
    mux4 io_mux (
        .sel(io_sel),
        .in_data0(uart_control),
        .in_data1(uart_rx_data),
        .in_data2(counter_data),
        .in_data3(32'd0),
        .out_data(io_data)
    );

    // Memory Data Mux
    mux4 Mem_Data_Mux (
        .sel(mem_sel),
        .in_data0(dmem_dout_masked),
        .in_data1(bios_dout_masked),
        .in_data2(io_data),
        .in_data3(32'd0),
        .out_data(mem_dout)
    );

    // Writeback Mux
    mux4 WriteBack_Mux (
        .sel(wb_sel),
        .in_data0(mem_dout),
        .in_data1(alu_pipeline_memory),
        .in_data2(pc_4_pipeline_memory),
        .in_data3(32'd0),
        .out_data(wb_data)
    );

    // End of Multiplexer Instantiation

    // Fetch Control
    control_block_fetch fetch_control (
        .pc(pc),
        .bios_ena(bios_ena)
    );

    control_block_decode decode_control (
        .inst_decode(instruction_decode),
        .inst_execute(instruction_execute),
        .inst_memory(instruction_memory),
        .br_pred_taken(br_pred_taken),           //TODO: Modify for Branch Prediction
        .is_br(is_br_guess),
        .imm_sel(imm_sel),
        .rd1_forward(rd1_forward),
        .rd2_forward(rd2_forward),
        .pc_sel(pc_sel_decode)
    
    );
    
    control_block_execute exe_control (
        .inst_execute(instruction_execute),
        .inst_memory(instruction_memory),
        .mem_addr(alu_dout),
        .pc_decode(pc_pipeline_decode),
        .bp_en(bp_enable),
        .br_eq(br_eq), 
        .br_lt(br_lt),
        .br_pred_taken(prev_br_pred_taken),           //TODO: Modify for Branch Prediction
        .br_un(br_un),
        .alu_sel(alu_sel),
        .a_sel(a_sel),
        .b_sel(b_sel),
        .shift(shift),
        .pc_sel(pc_sel_exe),
        .bubble_sel(bubble_sel),
        .br_forward(br_forward),
        .mem_forward(mem_forward),
        .csr_sel(csr_sel),
        .csr_we(csr_we),
        .imem_we(imem_wea),
        .dmem_we(dmem_we),
        .dmem_re(dmem_en),
        .imem_re(imem_ena),
        .bios_reb(bios_enb),        
        .io_reset(io_reset),
        .uart_rx_data_out_r(uart_rx_data_out_ready),
        .is_br(is_br_check),
        .br_taken(br_taken_check)
    );

    
    control_block_memory mem_control (
        .inst_memory(instruction_memory),
        .mem_addr(alu_pipeline_memory),
        .load_type(load_type),
        .byte_addr(byte_addr),
        .wb_sel(wb_sel),
        .mem_sel(mem_sel),
        .counter_sel(counter_sel),
        .io_sel(io_sel),
        .reg_we(we),
        .uart_tx_data_in_v(uart_tx_data_in_valid)
    );

    // PC Loop Adder
    adder_constant #(
        .VALUE(4)
    ) pc_adder (
        .din(pc),
        .dout(pc_4)
    );

    // PC Pipeline Adder
    adder_constant #(
        .VALUE(4)
    ) pc_pipeline_adder (
        .din(pc_pipeline_execute),
        .dout(pc_4_pipeline_execute)
    );

    // Branch Predictor
    branch_predictor bp (
        .clk(clk),
        .reset(rst),
        .pc_guess(pc_guess),                // PC Value Decode
        .is_br_guess(is_br_guess),          // Decode Control
        .pc_check(pc_check),                // PC Value Execute
        .is_br_check(is_br_check),          // Execute Control
        .br_taken_check(br_taken_check),    // Execute Control
        .br_pred_taken(br_pred_taken)       // Output
    );

    adder branch_adder (
        .din1(pc_pipeline_decode),
        .din2(imm_dout),
        .dout(bp_pc)
    );

    // Immediate Generator
    immediate_generator imm_gen (
      .instruction(instruction_decode),
      .imm_type(imm_sel),
      .imm_out(imm_dout)
    );

    // ALU
    alu alu(
      .Asel(a_data),
      .Bsel(b_data),
      .alu_op(alu_sel),
      .rd(alu_dout),
      .zero(zero_flag)
    );

    // Branch Comparator
    branch_comparator br_comp (
      .br_un(br_un),
      .rd1(br_data),
      .rd2(mem_data),
      .br_eq(br_eq),
      .br_lt(br_lt)
    );

    //Store Shifting
    store_shift store_shift (
        .memory_data(mem_data),
        .shift(shift),
        .shifted_data(mem_data_shifted)
    );

    // DMEM Load Masking
    masked dmem_mask (
        .mem_data(dmem_dout),
        .load_type(load_type),
        .byte_offset(byte_addr),
        .masked_data(dmem_dout_masked)
    );

    // BIOS Load Masking
    masked bios_mask (
        .mem_data(bios_doutb),
        .load_type(load_type),
        .byte_offset(byte_addr),
        .masked_data(bios_dout_masked)
    );

    // PC Register
    always @(posedge clk or posedge rst) begin
        if (rst) pc <= RESET_PC;
        else pc <= next_pc;
    end

    // PC Pipeline Registers
    always @(posedge clk or posedge rst) begin
        if (rst) pc_pipeline_decode <= pc;
        pc_pipeline_decode <= pc;
    end

    always @(posedge clk or posedge rst) begin
        if (rst) pc_pipeline_execute <= pc;
        pc_pipeline_execute <= pc_pipeline_decode;
    end

    always @(posedge clk) begin
        pc_4_pipeline_memory <= pc_4_pipeline_execute;
    end

    // rd1 Pipeline Register
    always @(posedge clk) begin
        rd1_pipeline <= rd1_data;
    end

    // rd2 Pipeline Register
    always @(posedge clk) begin
        rd2_pipeline <= rd2_data;
    end

    // Immediate Pipeline Register
    always @(posedge clk) begin
        immediate_pipeline_execute <= imm_dout;
    end

    // ALU Pipeline Register
    always @(posedge clk) begin
        alu_pipeline_memory <= alu_dout;
    end

    // Instruction Pipeline Register
    always @(posedge clk or posedge rst) begin
        if (rst) instruction_execute_initial <= 32'd0;
        instruction_execute_initial <= instruction_decode;
    end

    always @(posedge clk or posedge rst) begin
        if (rst) instruction_memory <= 32'd0;
        instruction_memory <= instruction_execute;
    end

    always @(posedge clk) begin
        if (csr_we) tohost_csr <= csr_data;
    end

    always @(posedge clk) begin
        prev_pc_sel <= pc_sel;
    end
    always @(posedge clk) begin
        prev_br_pred_taken <= br_pred_taken;
    end

    // Cycle Counter
    always @(posedge clk or posedge rst) begin
        if (rst | io_reset) cycle_counter <= 32'd0;
        else cycle_counter <= cycle_counter + 32'd1;
    end

    // Instruction Counter
    always @(posedge clk or posedge rst) begin
        if (rst | io_reset) instruction_counter <= 32'd0;
        else if (instruction_execute != 32'h00000013) instruction_counter <= instruction_counter + 32'd1; 
    end

    // Branch Counter
    always @(posedge clk or posedge rst) begin
        if (rst | io_reset) branch_counter <= 32'd0;
        else if (is_br_check) branch_counter <= branch_counter + 32'd1; 
    end

    // Accuracy Counter
    always @(posedge clk or posedge rst) begin
        if (rst | io_reset) br_accuracy_counter <= 32'd0;
        else if (bp_enable & prev_br_pred_taken & br_taken_check) br_accuracy_counter <= br_accuracy_counter + 32'd1; 
    end

    // UART control register
    always @(posedge clk or posedge rst) begin
        if (rst) uart_control <= 32'd0;
        else uart_control <= {30'd0, uart_rx_data_out_valid, uart_tx_data_in_ready};
    end

    // UART Receiver register
    always @(posedge clk or posedge rst) begin
        if (rst) uart_rx_data <= 32'd0;
        else uart_rx_data<= {24'd0, uart_rx_data_out};
    end

    // UART Transmitter register
    always @(posedge clk or posedge rst) begin
        if (rst) uart_tx_data <= 32'd0;
        else uart_tx_data <= {24'd0, mem_data[7:0]};
    end

    assign uart_tx_data_in = uart_tx_data[7:0];
    assign wa = instruction_memory[11:7];
    assign ra1 = instruction_decode[19:15];
    assign ra2 = instruction_decode[24:20];
    assign wd = wb_data;
    assign bios_addra = pc[13:2];
    assign imem_addrb = pc[15:2];
    assign bios_addrb = alu_dout[13:2];
    assign dmem_addr = alu_dout[15:2];
    assign imem_addra = alu_dout[15:2];
    assign dmem_din = mem_data_shifted;
    assign imem_dina = mem_data_shifted;

    // Branch Prediction
    assign pc_sel = bp_enable ? 
                (br_pred_taken | (br_taken_check & prev_br_pred_taken) ? pc_sel_decode : pc_sel_exe) : 
                pc_sel_exe;
    assign pc_guess = pc_pipeline_decode;
    assign pc_check = pc_pipeline_execute;
    

    // Add as many modules as you want
    // Feel free to move the memory modules around


    // SYSTEM VERILOG ASSERTIONS
    // Assertion 1: Upon reset, the program counter should become RESET_PC
    /*
    Assertion1:
        assert
            property (
                @(posedge clk)
                rst |-> (pc == RESET_PC)
            )
            else 
                $error("Program counter was not RESET_PC on reset");


    // Assertion 2: For store instructions, the write enable mask should have the appropriate
    // number of ones depending on whether the instruction is sb, sh, or sw.
    assert
        property (
            @(posedge clk) disable iff (rst)
            ((instruction_decode[6:0] == 7'b0100011) && (instruction_decode[14:12]) == 3'b000) |-> ($countones(dmem_we) == 1)
        )
        else 
            $error("Store Byte write enable mask does not have 1 one");
    assert
        property (
            @(posedge clk) disable iff (rst)
            ((instruction_decode[6:0] == 7'b0100011) && (instruction_decode[14:12]) == 3'b001) |-> ($countones(dmem_we) == 2)
        )
        else 
            $error("Store Byte write enable mask does not have 2 one");
    assert
        property (
            @(posedge clk) disable iff (rst)
            ((instruction_decode[6:0] == 7'b0100011) && (instruction_decode[14:12]) == 3'b010) |-> ($countones(dmem_we) == 4)
        )
        else 
            $error("Store Byte write enable mask does not have 4 one");



    // Assertion 3: For lb instructions, the upper 24 bits of data written to the regfile
    // should be all 0s or all 1s. For lh instructions, the upper 16 bits should be all 0s or all 1s.
    assert
        property (
            @(posedge clk) disable iff (rst)
            ((instruction_memory[6:0] == 7'b0000011) && (instruction_memory[14:12]) == 3'b000) |-> ((wd[31:8] == 24'd0) || (wd[31:8] == 24'd16777215))
        )
        else 
            $error("Upper 24 bits were not all 0s or 1s for lb");
    assert
        property (
            @(posedge clk) disable iff (rst)
            ((instruction_memory[6:0] == 7'b0000011) && (instruction_memory[14:12]) == 3'b001) |-> ((wd[31:16] == 16'd0) || (wd[31:16] == 16'd65535))
        )
        else 
            $error("Upper 16 bits were not all 0s or 1s for lh");  
    */  
endmodule
