/// UART unbuffered transmitter
///
/// The module accepts a byte of data from a Wishbone
/// controller and sends it over UART. The Wishbone
/// pipelined mode is used, and the stall_o signal is
/// set if a wishbone cycle is requested but a byte
/// is already being sent.
///
/// Data is outputted on the uart_tx line.
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
   output logic uart_tx
);

   logic [31:0]	baud_counter = 0;
   logic [3:0] bit_counter = 0; 

   logic	send, load, busy, shift, tx_done;
   tx_shift_reg tx_shift_reg(
      .clk(wb.clk_i),
      .rst(wb.rst_i),
      .load,
      .shift,
      .data(wb.dat_i),
      .uart_tx
   );

   // A transmission is requested when the Wishbone controller asserts
   // cyc_i and stb_i. This may cause a stall if the module is currently
   // sending a byte.
   assign send = wb.cyc_i && wb.stb_i;
   
   // Assert shift on the rising clock edge beginning the last baud
   // tick
   assign shift = (baud_counter == (CLOCKS_PER_BIT - 1));

   // Assert transmission done on the rising clock edge beginning
   // the last baud tick of the final bit. Note: adding 2 to the
   // DAT_WIDTH for start/stop bit.
   assign tx_done = shift && (bit_counter == (DAT_WIDTH + 1));

   // Set the stall_o signal if the device is busy and the wishbone
   // controller is requesting a new transaction.
   assign wb.stall_o = wb.cyc_i && wb.stb_i && busy;
   
   // Load is the same as requesting a send while a transmission
   // is not in progress. Load will immediately be deasserted,
   // since busy goes high. busy remains high until the last
   // baud tick of the last bit (the stop bit), at which point
   // it falls and another load can happen. The user must ensure
   // data is present when send is asserted.
   assign load = !busy && send;

   // The tx_done signal can be used as the wishbone ACK response
   // (which is the only response this device gives)
   assign wb.ack_o = tx_done;

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

   // This should follow from the logic, but putting it here
   // for now to stop induction failing
   baud_counter_valid: assume property (baud_counter < CLOCKS_PER_BIT);
   
   // When reset is asserted, tx (data out) is
   // set high and the module is not busy on the
   // next clock edge.
   sequence reset_outputs;
      uart_tx && !wb.ack_o;
   endsequence // reset_outputs
   
   reset: assert property (
      disable iff (0)
      wb.rst_i |=> reset_outputs);

   // If the device is not busy, then tx is high
   tx_default_high: assert property (!busy |-> uart_tx); 

   // Define Wishbone transactions
   sequence wishbone_request;
      wb.cyc_i && wb.stb_i;
   endsequence // wishbone_request

   sequence wishbone_finishes;
      wb.cyc_i && wb.ack_o;
   endsequence // wishbone_finishes

   // Assume that cyc_o lasts for full wishbone cycle (start -> ack)
   wishbone_cycle: assume property (
      wishbone_request |-> (wb.cyc_i s_until wb.ack_o));

   // After controller has initiated a transaction, device accepts
   // by clearing stall_o while cyc_i and stb_i are set
   sequence wishbone_device_accepts;
     wishbone_request and !wb.stall_o
   endsequence

   // Assume that the wishbone controller maintains request until
   // device accepts   
   wishbone_ctrl_maintains_request: assume property (
	wishbone_request |->
	(wishbone_request s_until wishbone_device_accepts) 
     );

   // If the cycle signal is low, no wishbone transaction is happening
   // and all other signals are undefined
   sequence wishbone_idle;
      !wb.cyc_i
   endsequence // wishbone_idle
   
   // Check that every Wishbone transaction completes successfully   
   wishbone_completes: assert property(wishbone_request |-> 
      ##[1:$] wishbone_finishes);

   // Provide an example wishbone transaction
   wishbone_example: cover property(
      (wishbone_idle and !busy)
      ##10 wishbone_request 
      ##[1:$] wishbone_finishes
      ##[1:$] wishbone_request);
   
   /*
    
   // If the module is not busy/reset, asserting send causes the
   // beginning of the start bit on the next clock edge (tx
   // falls), which lasts for CLOCKS_PER_BIT.
   sequence send_condition;
      !busy && send;
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
    */
       
`endif
   
endmodule
