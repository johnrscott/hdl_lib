import types::rgb_led_t;

module buttons_to_leds(
   input	      clk_i, rst_i,
   input [3:0]	      buttons, switches,
   output logic [3:0] green_leds,
   output	      rgb_led_t [3:0] rgb_leds
);

   localparam DEBOUNCE_PERIOD = 5;//5_000_000;
   
   wishbone_classic wb(.clk_i, .rst_i);
   buttons #(.DEBOUNCE_PERIOD(DEBOUNCE_PERIOD)) btns(.buttons, .switches, .wb);
   leds leds(.green_leds, .rgb_leds, .wb);
   
endmodule
