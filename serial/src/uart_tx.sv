module uart_tx(
   input logic	     clk, rst, send,
   input logic [7:0] data,
   output logic	     busy, tx
);

   parameter CLOCK_RATE_HZ = 3;
   parameter BITS_PER_TRANSFER = 8;
   parameter BAUD_RATE_HZ = 1;// 115_200;
   parameter CLOCKS_PER_BAUD = CLOCK_RATE_HZ / BAUD_RATE_HZ;

   logic [31:0]	baud_counter = 0;
   logic [3:0] bit_counter = 0; 

   logic	load, shift, tx_done;
   tx_shift_reg tx_shift_reg(.clk, .rst, .load, .shift, .data, .tx);

   // Assert shift on the rising clock edge beginning the last baud
   // tick
   assign shift = (baud_counter == (CLOCKS_PER_BAUD - 1));

   // Assert transmission done on the rising clock edge beginning
   // the last baud tick of the final bit. Note: adding 2 to the
   // BITS_PER_TRANSFER for start/stop bit.
   assign tx_done = shift && (bit_counter == (BITS_PER_TRANSFER + 1));

   // Load is the same ass requesting a send while a transmission
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
      if (rst || !busy)
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
	       
endmodule
