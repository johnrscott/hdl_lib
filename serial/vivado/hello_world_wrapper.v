module hello_world_wrapper(
   input wire clk, rst, trigger,
   output wire tx, tx_debug, busy
);

    wire clk_internal;

   // Signal names as documented in IP documentation for clocking wizard?
   clk_wiz_0 clk_wiz_0(
      .clk_in1(clk),
      .clk_out1(clk_internal)
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
