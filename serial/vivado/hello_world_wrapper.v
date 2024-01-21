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

   // Copied from instantiation template
   // clk_wiz_0 instance_name (
   //    // Clock out ports
   //    .clk_out1(clk_internal),     // output clk_out1
   //    // Status and control signals
   //    .reset(reset), // input reset
   //    .locked(locked),       // output locked
   //    // Clock in ports
   //    .clk_in1(clk)      // input clk_in1
   // );
   
   
    assign tx_debug = tx;

    hello_world hello_world(
        .clk(clk_internal),
        .rst(rst),
        .trigger(trigger),
        .tx(tx),
        .busy(busy)
    );

endmodule
