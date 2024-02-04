module buttons #(
   // 50 ms debouncing (mainly for slide switches) assuming 100MHz clock
   parameter DEBOUNCE_PERIOD = 5//_000_000
)(
   input [3:0]	       buttons, switches,
   wishbone_classic.controller wb
);

   // After one flip-flop, *_meta may be metastable,
   // and after second flip-flop, *_sync should be
   // synchronous with the wb.clk_i
   logic [3:0] buttons_meta = 0, buttons_sync = 0;
   logic [3:0] switches_meta = 0, switches_sync = 0;

   // This design will debounce the whole 8-bit input
   // simultaneously, by only storing changes to the
   // debounced register when it has been stable for
   // at least DEBOUNCE_PERIOD
   logic [31:0]	debounce_counter = 0;
   logic [7:0]	input_sync, input_tmp = 0, input_debounce = 0;
   assign input_sync = { switches_sync, buttons_sync };

   // Signal to trigger a wishbone transaction. Set for one
   // clock cycle if the state of the input changes (this
   // means changes in the input state while a previous
   // wishbone transaction is happening will be ignored --
   // there is no queuing mechanism.
   logic trigger_wishbone = 0;

   // Simple Wishbone classic controller -- send the state
   // of input_debounce on input change
   wishbone_ctrl_classic wb_ctrl(
      .write_en(1'b1),
      .start(trigger_wishbone),
      .write_data(input_debounce),
      .wb
   );
   
   always_ff @(posedge wb.clk_i) begin: synchronize
      if (wb.rst_i) begin
	 buttons_meta <= 0;
	 buttons_sync <= 0;
	 switches_meta <= 0;
	 switches_sync <= 0;
      end
      else begin
	 buttons_meta <= buttons;
	 buttons_sync <= buttons_meta;
	 switches_meta <= switches;
	 switches_sync <= switches_meta;  
      end
   end
   
   always_ff @(posedge wb.clk_i) begin: debounce
      if (wb.rst_i) begin
	 input_debounce <= 0;
	 debounce_counter <= 0;
      end
      else if (debounce_counter == DEBOUNCE_PERIOD) begin
	 debounce_counter <= 0;
	 if (input_sync == input_tmp) begin
	    input_debounce <= input_tmp;
	    trigger_wishbone <= 1;
	 end
      end
      else if (debounce_counter != 0)
	debounce_counter <= debounce_counter + 1;
      else if (input_sync != input_debounce) begin
	 debounce_counter <= 1;
	 input_tmp <= input_sync;
      end
      else
	trigger_wishbone <= 0;
   end

`ifdef FORMAL

   default clocking @(posedge wb.clk_i);
   endclocking //

   default disable iff (wb.rst_i);

   sequence bounce(signal, n);
      $changed(signal)[*n];
   endsequence
   
   sequence input_change(signal, old_value, new_value, bounces);
      (signal == old_value)[*20] ##1 bounce(signal, bounces) ##1 (signal == new_value)[*40];
   endsequence

   property bounce_and_change;
      (input_change(buttons, 0, 1, 3) and input_change(switches, 2, 4, 2)) |->
	##[0:60] $changed(input_debounce) ##1 (input_debounce[7:4] == 4);
   endproperty

   // Cover a simple case showing the debouncing for both button and switch
   // inputs at the same time
   bounce_test: cover property (bounce_and_change);

   // Check the debounce counter never exceeds its period
   counter_in_range: assert property (debounce_counter <= DEBOUNCE_PERIOD);

   sequence inputs_stable(n);
      ($stable(buttons) and $stable(switches))[*n];
   endsequence

   function logic [7:0] concat_inputs(logic [3:0] buttons, switches);
      return {switches, buttons};
   endfunction
   
   // Check that button/switch stability for longer than the synchronisation
   // and debounce period results in a change in the input_debounce. To make
   // this work, the inputs are set for longer than the time to set the output,
   // so that the output can be compared directly to the inputs
   assert property (inputs_stable(20) |->
	     ##[0:10] (input_debounce == concat_inputs(buttons, switches)));
   
`endif
   
endmodule
  
