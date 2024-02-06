import types::rgb_led_t;

`ifndef DEBOUNCE_PERIOD
 `define DEBOUNCE_PERIOD 5_000_000
`endif

module buttons_to_leds(
   input	      clk_i, rst_i,
   input [3:0]	      buttons, switches,
   output logic [3:0] green_leds,
   output	      rgb_led_t [3:0] rgb_leds
);

   wishbone_classic wb(.clk_i, .rst_i);
   buttons #(.DEBOUNCE_PERIOD(`DEBOUNCE_PERIOD)) btns(.buttons, .switches, .wb);
   leds leds(.green_leds, .rgb_leds, .wb);
   
endmodule
