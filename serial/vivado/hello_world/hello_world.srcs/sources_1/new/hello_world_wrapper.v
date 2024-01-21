module hello_world_wrapper(
   input wire clk, rst, trigger,
   output wire tx, tx_debug, busy
);

    wire clk_internal;
    
    clock_wrapper clock_wrapper(
        .clk_in(clk),
        .clk_out(clk_internal)
    );

    assign tx_debug = tx;

    hello_world hello_world(
        .clk(clk_internal),
        .rst(rst),
        .trigger(trigger),
        .tx(tx),
        .busy(busy)
    );

endmodule