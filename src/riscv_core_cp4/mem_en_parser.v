module mem_en_parser (
    input [5:0] mem_addr,
    input [2:0] funct3_execute,
    input enable,
    output reg [3:0] dmem_we, imem_we, 
    output reg dmem_re
);
    

    always @(*) begin
        imem_we = 4'd0;
        dmem_we = 4'd0;
        dmem_re = 1'b0;
        if (enable) begin
        case(mem_addr[5:2])
                    4'b0001: begin
                        dmem_re = 1'b1; 
                        case(funct3_execute[1:0])                                // Memory Write Enable logic (DMEM Only)
                            2'b00: begin
                                case(mem_addr[1:0])
                                    2'b00: dmem_we = 4'b0001; 
                                    2'b01: dmem_we = 4'b0010;
                                    2'b10: dmem_we = 4'b0100;
                                    2'b11: dmem_we = 4'b1000;
                                endcase
                            end
                            2'b01: begin
                                dmem_we = (mem_addr[1:0] == 2'b00) ? 4'b0011 : 4'b1100;
                            end
                            2'b10: dmem_we = 4'b1111;
                        endcase
                    end
                    4'b0010: begin 
                        case(funct3_execute[1:0])                                // Memory Write Enable logic (IMEM Only)
                        2'b00: begin
                                case(mem_addr[1:0])
                                    2'b00: imem_we = 4'b0001; 
                                    2'b01: imem_we = 4'b0010;
                                    2'b10: imem_we = 4'b0100;
                                    2'b11: imem_we = 4'b1000;
                                endcase
                            end
                            2'b01: begin
                                imem_we = (mem_addr[1:0] == 2'b00) ? 4'b0011 : 4'b1100;
                            end
                            2'b10: imem_we = 4'b1111;
                        endcase
                    end
                    4'b0011: begin
                        dmem_re = 1'b1; 
                        case(funct3_execute[1:0])                                // Memory Write Enable logic (DMEM and IMEM)
                            2'b00: begin
                                case(mem_addr[1:0])
                                    2'b00: begin
                                        dmem_we = 4'b0001;
                                        imem_we = 4'b0001;
                                    end
                                    2'b01: begin
                                        dmem_we = 4'b0010;
                                        imem_we = 4'b0010;
                                    end
                                    2'b10: begin
                                        dmem_we = 4'b0100;
                                        imem_we = 4'b0100;
                                    end
                                    2'b11: begin
                                        dmem_we = 4'b1000;
                                        imem_we = 4'b1000;
                                    end
                                endcase
                            end
                            2'b01: begin
                                dmem_we = (mem_addr[1:0] == 2'b00) ? 4'b0011 : 4'b1100;
                                imem_we = (mem_addr[1:0] == 2'b00) ? 4'b0011 : 4'b1100;
                            end
                            2'b10: begin
                                dmem_we = 4'b1111;
                                imem_we = 4'b1111;
                            end    
                        endcase
                    end
        endcase
        end

    end
    

endmodule