module branch_comparator_cp4 (
    input br_un,
    input [31:0] rd1, rd2,
    output br_eq, br_lt
);
    reg lt;
    always @(*) begin
        if (br_un) begin
            lt = rd1 < rd2;
        end else begin
            // 4'b0111 > 4'b1111
            if (!rd1[31] && rd2[31]) lt = 1'b0;
            // 4'b1111 < 4'b0001     
            else if (rd1[31] && !rd2[31]) lt = 1'b1; 
            // 4'b0001 < 4'b0111 or 4'b1000 < 4'b1111  
            else lt = rd1[30:0] < rd2[30:0];
        end    
    end
    assign br_eq = rd1 == rd2;
    assign br_lt = lt;
endmodule