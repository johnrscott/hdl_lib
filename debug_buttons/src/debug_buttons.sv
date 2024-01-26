module debug_buttons #(
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
   logic [7:0]	input_sync, input_tmp = 0, input_debounce = 0;;
   assign input_sync = { switches_sync, buttons_sync };
   
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
	 if (input_sync == input_tmp)
	   input_debounce <= input_tmp;
      end
      else if (debounce_counter != 0)
	debounce_counter <= debounce_counter + 1;
      else if (input_sync != input_debounce) begin
	 debounce_counter <= 1;
	 input_tmp <= input_sync;
      end
   end


`ifdef FORMAL

   default clocking @(posedge wb.clk_i);
   endclocking //

   default disable iff (wb.rst_i);

   sequence button_change_no_bounce;
      $stable(switches) throughout ($stable(buttons)[*25] ##1 $changed(buttons) ##1 $stable(buttons)[*25]) 
   endsequence
   
   no_bounce_change: cover property (button_change_no_bounce |-> ##[0:55] $changed(input_debounce));

   
`endif
   
endmodule
  
