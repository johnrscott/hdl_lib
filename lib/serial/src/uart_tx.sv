/// UART unbuffered transmitter
///
/// The module accepts a byte of data from a Wishbone
/// controller and sends it over UART. The Wishbone
/// classic mode is used, and the ack signal is
/// delayed if a wishbone cycle is requested but a byte
/// is already being sent.
///
/// Data is outputted on the uart_tx line.
///
module uart_tx #(
   // How many clock ticks make up one bit (divide
   // clk rate by baud rate). Default gives a baud
   // rate of 115200 at a clock rate of 100 MHz
   parameter CLOCKS_PER_BIT = 868,
   // How many bits of data are in the UART data frame.
   parameter DAT_WIDTH = 8
)(
   wishbone_classic.device wb,
   output logic uart_tx
);

   logic [7:0] write_data;
   
   logic [31:0]	baud_counter = 0;
   logic [3:0] bit_counter = 0; 

   logic	send, load, busy = 0, shift, tx_done;
   tx_shift_reg tx_shift_reg(
      .clk(wb.clk_i),
      .rst(wb.rst_i),
      .load,
      .shift,
      .data(write_data),
      .uart_tx
   );

   // The tx_done signal can be used as the wishbone ACK response
   wishbone_dev_classic wb_dev(
      .ack(tx_done),
      .request(send),
      .write_data,
      .wb
   );
   
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
   always_ff @(posedge wb.clk_i) begin: output_and_busy_state
      if (wb.rst_i)
	busy <= 0;
      else if (load)
	busy <= 1;
      else if (tx_done)
	busy <= 0;
   end

   // Increment bit counter if in the DATA state, or reset
   always_ff @(posedge wb.clk_i) begin: increment_bit_count
      if (wb.rst_i || load || tx_done)
	bit_counter <= 0;
      else if (shift)
	bit_counter <= bit_counter + 1;
   end

   // Increment the baud counter in the DATA state, or reset
   always_ff @(posedge wb.clk_i) begin: increment_baud_count
      if (wb.rst_i || !busy || shift)
	baud_counter <= 0;
      else
	baud_counter <= baud_counter + 1;
   end

`ifdef FORMAL

   // Properties of the external interface
   default clocking @(posedge wb.clk_i);
   endclocking

   default disable iff (wb.rst_i);

   // When reset is asserted, tx (data out) is
   // set high and the module is not busy on the
   // next clock edge.
   sequence reset_outputs;
      uart_tx && !wb.ack_o;
   endsequence // reset_outputs

   // Cover a simple transaction
   transmit_char: cover property (wb.cyc_i && wb.stb_i);
   
   // This should follow from the logic, but putting it here
   // for now to stop induction failing
   baud_counter_valid: assert property (baud_counter < CLOCKS_PER_BIT);
      
   reset: assert property (
      disable iff (0)
      wb.rst_i |=> reset_outputs);

   // If the device is not busy, then tx is high
   tx_default_high: assert property (!busy |-> uart_tx); 

   // This is a synchronous wishbone device -- ack cannot occur
   // immediately when cyc and stb rise, it occurs one cycle later
   // at the earliest
   sync_ack: assert property ($rose(wb.cyc_i && wb.stb_i) |-> !wb.ack_o);
   
   // Somewhat duplicates sequences in the main wishbone classic interface.
   // Would be good to deduplicate.
   logic request;
   assign request = wb.cyc_i && wb.stb_i;
   sequence cycle_start();
      $rose(request) or (request && $fell(wb.ack_o));
   endsequence
   
   // If the module is not busy/reset, asserting send causes the
   // beginning of the start bit on the next clock edge (tx
   // falls), which lasts for CLOCKS_PER_BIT.
   start_bit: assert property (
      cycle_start |=> ($fell(uart_tx) and !uart_tx[*CLOCKS_PER_BIT]));
   
   // Each tx bit lasts for CLOCKS_PER_BIT clock
   // cycles before changing (i.e. the output baud
   // rate is correct)
   baud_rate_correct: assert property (
      (busy && $changed(uart_tx)) |=> $stable(uart_tx)[*(CLOCKS_PER_BIT-1)]);

   // The stop bit should be asserted after the data has been
   // transmitted
   stop_bit_correct: assert property (
      cycle_start |=> ##(9*CLOCKS_PER_BIT) uart_tx[*CLOCKS_PER_BIT]);
   
   // Properties of the internal implementation

   // The bit counter is never out of range (note +2 for start/stop bit)
   bit_counter_valid: assert property (bit_counter < (DAT_WIDTH + 2));
       
`endif
   
endmodule

module uart_tx_formal();

   logic clk_i, rst_i, uart_tx;
   wishbone_classic wb(.*);
   uart_tx #(.CLOCKS_PER_BIT(4)) u0(.*);

endmodule
