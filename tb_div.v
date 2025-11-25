`timescale 1ns/1ps


module tb_div();

    reg [31:0] i_dividend;
    reg [31:0] i_divisor;
    wire [31:0] o_quotient;
    wire [31:0] o_remainder;


    divider_unsigned uut (
        .i_dividend(i_dividend), 
        .i_divisor(i_divisor), 
        .o_quotient(o_quotient), 
        .o_remainder(o_remainder)
    );

    initial begin
    
        i_dividend = 0;
        i_divisor = 1;
        #50; 
        
        i_dividend = 100;
        i_divisor  = 10;
        #50; 

        i_dividend = 100;
        i_divisor  = 30;
        #50;

        i_dividend = 7;
        i_divisor  = 15;
        #50;


        i_dividend = 32'hF0F0F0F0;
        i_divisor  = 32'hF;
        #50;

        i_dividend = 12345;
        i_divisor  = 1;
        #50;

        $finish;
    end

endmodule