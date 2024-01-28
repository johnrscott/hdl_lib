import types::rgb_led_t;

module buttons_to_leds(
   input	      clk_i, rst_i,
   input [3:0]	      buttons, switches,
   output logic [3:0] green_leds[],
   output	      rgb_led_t [3:0] rgb_leds
);

   localparam DEBOUNCE_PERIOD = 5_000_000;
   
   wishbone wb(.clk_i, .rst_i);
   debug_buttons debug_buttons(.buttons, .switches, .wb);
   led_output led_output(.green_leds, .rgb_leds, .wb);
   
endmodule
