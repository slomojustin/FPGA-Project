module masked (
    input [31:0] mem_data,
    input [2:0] load_type,      
    input [1:0] byte_offset,    // Lower 2 bits of our address to identify the byte/halfword
    output reg [31:0] masked_data // Our masked and shifted data
);

    localparam LB  = 3'b000; // Load Byte (signed)
    localparam LBU = 3'b100; // Load Byte Unsigned
    localparam LH  = 3'b001; // Load Halfword (signed)
    localparam LHU = 3'b101; // Load Halfword Unsigned
    localparam LW  = 3'b010; // Load Word

    always @(*) begin
        case (load_type)
            LB: begin // Load Byte (signed)
                case (byte_offset)
                    2'b00: masked_data = {{24{mem_data[7]}}, mem_data[7:0]};  // Byte 0
                    2'b01: masked_data = {{24{mem_data[15]}}, mem_data[15:8]}; // Byte 1
                    2'b10: masked_data = {{24{mem_data[23]}}, mem_data[23:16]}; // Byte 2
                    2'b11: masked_data = {{24{mem_data[31]}}, mem_data[31:24]}; // Byte 3
                endcase
            end

            LBU: begin // Load Byte Unsigned
                case (byte_offset)
                    2'b00: masked_data = {24'b0, mem_data[7:0]};  // Byte 0
                    2'b01: masked_data = {24'b0, mem_data[15:8]}; // Byte 1
                    2'b10: masked_data = {24'b0, mem_data[23:16]}; // Byte 2
                    2'b11: masked_data = {24'b0, mem_data[31:24]}; // Byte 3
                endcase
            end

            LH: begin // Load Halfword (signed)
                case (byte_offset[1]) // Only check the most significant bit of offset
                    1'b0: masked_data = {{16{mem_data[15]}}, mem_data[15:0]};   // Halfword 0 (lower 16 bits)
                    1'b1: masked_data = {{16{mem_data[31]}}, mem_data[31:16]};  // Halfword 1 (upper 16 bits)
                endcase
            end

            LHU: begin // Load Halfword Unsigned
                case (byte_offset[1])
                    1'b0: masked_data = {16'b0, mem_data[15:0]};   // Halfword 0 (lower 16 bits)
                    1'b1: masked_data = {16'b0, mem_data[31:16]};  // Halfword 1 (upper 16 bits)
                endcase
            end

            LW: begin // Load Word, no masking here
                masked_data = mem_data;
            end

            default: begin // Undefined load type just in case
                masked_data = 32'b0;
            end
        endcase
    end
endmodule
