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

   assign wb.stall_o = 0;
   assign wb.err_o = 0;
   assign wb.rty_o = 0;

   logic [7:0] state;

   assign green_leds = state[3:0];
   assign rgb_leds = state[7:4];
   
   always_ff @(posedge wb.clk_i) begin: wishbone_response
      if (wb.rst_i)
	 wb.ack_o <= 0;
      else if (wb.cyc_o && wb.stb_o)
	state <= wb.dat_i;
   end

endmodule
