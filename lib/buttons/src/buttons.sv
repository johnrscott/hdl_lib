module buttons #(
   // 50 ms debouncing (mainly for slide switches) assuming 100MHz clock
   parameter DEBOUNCE_PERIOD = 5//_000_000
)(
   input [3:0]	       buttons, switches,
   wishbone.controller wb
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

   /// High if device returns acknowledge, retry, or
   /// error responses
   function logic dev_response();
      return (wb.ack_i || wb.rty_i || wb.err_i);
   endfunction
   
   // State of cycle
   enum {
      IDLE, // cyc_o is low, transaction not in progress
      START_CYCLE, // cyc_o and stb_o set, stays here until stall_i is low
      AWAIT_DEV_RESPONSE // cyc_o set, stb_o cleared, wait for ack/err/rty  
   } state = IDLE;

   assign wb.we_o = 1;
   
   always_ff @(posedge wb.clk_i) begin: wishbone_transaction
      if (wb.rst_i) begin
	 wb.cyc_o <= 0;
	 wb.stb_o <= 0;
      end
      else
	case (state)
	  IDLE: if (trigger_wishbone) begin
	     wb.dat_o <= input_debounce;
	     wb.cyc_o <= 1;
	     wb.stb_o <= 1;
	     state <= START_CYCLE;
	  end
	  START_CYCLE: if (!wb.stall_i) begin
	     wb.stb_o <= 0;
	     state <= AWAIT_DEV_RESPONSE;
	  end
	  AWAIT_DEV_RESPONSE: if (dev_response()) begin
	     wb.cyc_o <= 0;
	     state <= IDLE;
	  end
	endcase
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
  