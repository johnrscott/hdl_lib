module hello_world_wrapper(
   input wire clk, rst, trigger,
   output wire tx, busy
);

    hello_world hello_world(
        .clk(clk),
        .rst(rst),
        .trigger(trigger),
        .tx(tx),
        .busy(busy)
    );

endmodule