`timescale 1ns/1ps


module divu_1iter (
    input  [31:0] i_remainder, //remainder from previous step
    input  [31:0] i_dividend, //dividend from previous step
    input  [31:0] i_divisor,  
    input  [31:0] i_quotient,  

    output [31:0] o_quotient,
    output [31:0] o_remainder, //remainder to next step
    output        o_quotient_bit,  //current quotient bit
    output [31:0] o_dividend   //Bit shifted dividend
);

    wire [31:0] new_remainder;
    wire [31:0] subtracted_remainder;
    wire        can_subtract;

    //Shift left the remainder and bring down the next bit of the dividend
    //{A, B} is the concatenation of A and B
    assign new_remainder = {i_remainder[30:0], i_dividend[31]};

    //Compare new_remainder with divisor
    assign can_subtract = (new_remainder >= i_divisor);

    assign subtracted_remainder = new_remainder - i_divisor;
    
    //Update remainder_out and quotient bit
    assign o_remainder = can_subtract ? subtracted_remainder : new_remainder;
    assign o_quotient_bit = can_subtract;

    //Shift left the dividend
    assign o_dividend = i_dividend <<1;

    assign o_quotient = (i_quotient <<1) | {31'b0, o_quotient_bit};  

endmodule
