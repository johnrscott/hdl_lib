/// UART unbuffered transmitter
///
/// 
///
module uart_tx #(
   // How many clock ticks make up one bit (divide
   // clk rate by baud rate). Default gives a baud
   // rate of 115200 at a clock rate of 100 MHz
   parameter CLOCKS_PER_BIT = 4,
   // How many bits of data are in the UART data frame.
   parameter DAT_WIDTH = 8
)(
   wishbone.device wb,
);

   logic [31:0]	baud_counter = 0;
   logic [3:0] bit_counter = 0; 

   logic	load, shift, tx_done;
   tx_shift_reg tx_shift_reg(.clk, .rst, .load, .shift, .data, .tx);

   // Assert shift on the rising clock edge beginning the last baud
   // tick
   assign shift = (baud_counter == (CLOCKS_PER_BIT - 1));

   // Assert transmission done on the rising clock edge beginning
   // the last baud tick of the final bit. Note: adding 2 to the
   // DAT_WIDTH for start/stop bit.
   assign tx_done = shift && (bit_counter == (DAT_WIDTH + 1));

   // Load is the same as requesting a send while a transmission
   // is not in progress. Load will immediately be deasserted,
   // since busy goes high. busy remains high until the last
   // baud tick of the last bit (the stop bit), at which point
   // it falls and another load can happen. The user must ensure
   // data is present when send is asserted.
   assign load = !busy && send;
   
   // Update main state variable (busy)
   always_ff @(posedge clk) begin: output_and_busy_state
      if (rst)
	busy <= 0;
      else if (load)
	busy <= 1;
      else if (tx_done)
	busy <= 0;
   end

   // Increment bit counter if in the DATA state, or reset
   always_ff @(posedge clk) begin: increment_bit_count
      if (rst || load || tx_done)
	bit_counter <= 0;
      else if (shift)
	bit_counter <= bit_counter + 1;
   end

   // Increment the baud counter in the DATA state, or reset
   always_ff @(posedge clk) begin: increment_baud_count
      if (rst || !busy || shift)
	baud_counter <= 0;
      else
	baud_counter <= baud_counter + 1;
   end

`ifdef FORMAL

   // Properties of the external interface
   
   // When reset is asserted, tx (data out) is
   // set high and the module is not busy on the
   // next clock edge.
   sequence reset_outputs;
      tx && !busy;
   endsequence // reset_outputs
   
   reset: assert property (@(posedge clk) rst |=> reset_outputs);

   // If the device is not busy, then tx is high
   tx_default_high: assert property (@(posedge clk) !busy |-> tx); 
   
   // If the module is not busy/reset, asserting send causes the
   // beginning of the start bit on the next clock edge (tx
   // falls), which lasts for CLOCKS_PER_BIT.
   sequence send_condition;
      !rst && !busy && send;
   endsequence // send_condition
   
   property start_bit_on_send;
      @(posedge clk) send_condition |=> $fell(tx);
   endproperty // start_bit_begins
   
   start_bit: assert property (start_bit_on_send);   

   // Each tx bit lasts for CLOCKS_PER_BIT clock
   // cycles before changing (i.e. the output baud
   // rate is correct)
   property baud_rate;
      @(posedge clk) disable iff (rst)
	(busy && $changed(tx)) |-> ##1 $stable(tx)[*(CLOCKS_PER_BIT-1)];
   endproperty // baud_rate
   
   baud_rate_correct: assert property (baud_rate);

   // The stop bit should be asserted after the data has been
   // transmitted
   property stop_bit;
      @(posedge clk) disable iff (rst)
	send_condition |-> ##(9*CLOCKS_PER_BIT + 1) tx;
   endproperty // stop_bit

   stop_bit_correct: assert property (stop_bit);
   
   // Properties of the internal implementation

   // The baud counter is never out of range
   baud_counter_valid: assert property (@(posedge clk) baud_counter < CLOCKS_PER_BIT);

   // The bit counter is never out of range (note +2 for start/stop bit)
   bit_counter_valid: assert property (@(posedge clk) bit_counter < (DAT_WIDTH + 2));
   
`endif
   
endmodule
