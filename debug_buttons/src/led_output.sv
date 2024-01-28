typedef struct packed {
   logic red;
   logic green;
   logic blue;
} rgb_led_t;
  
module led_output(
   output logic [3:0] green_leds,
   output	      rgb_led_t [3:0] rgb_leds,
   wishbone.device    wb
);

   

endmodule
