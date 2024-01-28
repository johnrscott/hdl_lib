import types::rgb_led_t;

module top(
   // Always present for every design
   input	      clk_ext, rstn_i,

   // List of other ports (varies by example)
   input [3:0]	      buttons, switches,
   output logic [3:0] green_leds,
   output	      rgb_led_t [3:0] rgb_leds
);

   // Convert the active-low Arty A7 reset pin to
   // active-high
   logic rst_i;
   assign rst_i = !rstn_i;
   
   wire clk_i;
   
   // Signal names as documented in IP documentation for clocking wizard?
   clk_wiz_0 clk_wiz_0(
      .clk_in1(clk_ext),
      .clk_out1(clk_i)
   );

   // Instantiate example here. Can use wildcards to match
   // all named ports.
   buttons_to_leds buttons_to_leds(.*);

endmodule
