import types::rgb_led_t;

module top_wrapper(
    input	       clk_i, rstn_i,
    input [3:0]	       buttons, switches,
    output logic [3:0] green_leds,
    output rgb_led_t [3:0] rgb_leds
);

   // Convert the active-low Arty A7 reset pin to
   // active-high
   logic rst_i;
   assign rst_i = !rstn_i;
   
   wire clk_internal;
   
   // Signal names as documented in IP documentation for clocking wizard?
   clk_wiz_0 clk_wiz_0(
      .clk_in1(clk),
      .clk_out1(clk_internal)
   );

   buttons_to_leds buttons_to_leds(.*);

endmodule
