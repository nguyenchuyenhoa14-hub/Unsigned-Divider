`timescale 1ns/1ps


module divider_unsigned (
    input [31:0] i_dividend,
    input [31:0] i_divisor,
    output [31:0] o_quotient,
    output [31:0] o_remainder  
);

    //wire arrays connect 32 divu_liter modules
    //need 33 wires for remainders (0 to 32)
    //32 output values for dividends
    wire [31:0] rem_wire [0:32];
    wire [31:0] div_wire [0:32];
    // collect 32 quotient bits in a packed vector so we can assign to quotient
    wire [31:0] quo_bits;

    //Initial assignments
    assign rem_wire[0] = 32'b0; //initial remainder is 0
    assign div_wire[0] = i_dividend; //initial dividend is input dividend

    //use generate to create 32 instances of divu_liter
    genvar i;
    generate
    for (i = 0; i < 32; i = i + 1) begin : stage
            divu_1iter u_divu_1iter (
                .i_remainder (rem_wire[i]),
                .i_dividend  (div_wire[i]),
                .i_divisor      (i_divisor),
                .o_remainder (rem_wire[i+1]),
                .o_quotient_bit (quo_bits[31-i]),
                .o_dividend (div_wire[i+1]),

                .i_quotient (),
                .o_quotient ()
            );
        end
    endgenerate

    assign o_quotient = quo_bits;
    assign o_remainder = rem_wire[32];
endmodule