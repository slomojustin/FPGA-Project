module uart_transmitter #(
    parameter CLOCK_FREQ = 125_000_000,
    parameter BAUD_RATE = 115_200)
(
    input clk,
    input reset,

    input [7:0] data_in,
    input data_in_valid,
    output data_in_ready,

    output serial_out
);
    // See diagram in the lab guide
    localparam  SYMBOL_EDGE_TIME    =   CLOCK_FREQ / BAUD_RATE;
    localparam  CLOCK_COUNTER_WIDTH =   $clog2(SYMBOL_EDGE_TIME);
    
    wire symbol_edge;
    wire start;
    wire tx_running;

    reg [CLOCK_COUNTER_WIDTH:0] clock_counter;
    reg [9:0] tx_shift;
    reg [3:0] bit_counter;

    // Assignments
    assign symbol_edge = clock_counter == (SYMBOL_EDGE_TIME - 1);
    assign start = data_in_valid && !tx_running;
    assign tx_running = bit_counter != 4'd0;

    // Reset
    always @ (posedge clk) begin
        if (start ||reset || symbol_edge) begin
            clock_counter <= 0;
        end else
            clock_counter <= clock_counter + 1;
        end

    // Count for 10 bits of transmission
    always @ (posedge clk) begin
        if (reset) begin
            bit_counter <= 0;
        end else if (start) begin
            bit_counter <= 10;
        end else if (symbol_edge && tx_running) begin
            bit_counter <= bit_counter - 1;
        end
    end

    always @ (posedge clk) begin
        if (start) begin
            tx_shift <= {1'b1, data_in[7:0], 1'b0};
        end else if (tx_running && symbol_edge) begin
            tx_shift <= tx_shift >> 1;
        end
    end

    assign serial_out = (tx_running) ? tx_shift[0] : 1'b1;
    assign data_in_ready = !tx_running;

    // SYSTEM VERILOG ASSERTS
    //assert 
    //    property (
    //        @(posedge clk) 
    //        !tx_running |-> data_in_ready
    //    )
    //   else 
    //        $error("Ready is low while not transmitting");
    //assert 
    //    property (
    //       @(posedge clk) 
    //        !tx_running |-> serial_out
    //    )
    //    else 
    //        $error("Serial Output is low while not transmitting");
    //assert 
    //    property (
    //        @(posedge clk) 
    //        tx_running |-> ##[0:SYMBOL_EDGE_TIME*10] !data_in_ready
    //    ) 
    //    else 
    //        $error("Ready signal went high before CLOCK_FREQ/BAUD_RATE*10 cycles passed");


endmodule
