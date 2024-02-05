import types::rgb_led_t;
  
module leds(
   output logic [3:0]	   green_leds,
   output		   rgb_led_t [3:0] rgb_leds,
   wishbone_classic.device wb
);

   logic update_leds;
   logic [7:0] new_leds_state, state;

   assign green_leds = state[3:0];
   assign rgb_leds = state[7:4];

   wishbone_dev_classic wb_dev(
      .ack(1'b1),
      .request(update_leds),
      .write_data(new_led_state),
      .wb
   );
   
   always_ff @(posedge wb.clk_i) begin: update_from_wishbone
      if (wb.rst_i)
	 state <= 0;
      else if (update_leds)
	 state <= new_led_state;
   end

`ifdef FORMAL

   default clocking @(posedge wb.clk_i);
   endclocking //

   default disable iff (wb.rst_i);

   // 1. Establish correct behaviour

   correct_state_stored: assert property ((wb.cyc_i && wb.stb_i && !wb.ack_o) |=> (state == $past(wb.dat_i)));

   // 2. Provide examples of behaviour
     
   respond_to_request: cover property (!update_leds[*10]
      ##1 (update_leds && (new_led_state != state))
      ##1 !update_leds[*10]);

`endif
   
endmodule

module leds_formal(input clk_i, rst_i);

   logic [3:0] green_leds;
   rgb_led_t [3:0] rgb_leds;
   
   wishbone_classic wb(.clk_i, .rst_i);
   leds leds(.*);
   
endmodule
