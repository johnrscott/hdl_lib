module uart_tx(
   input logic	     clk, rst, write,
   input logic [7:0] data,
   output logic	     busy, tx
);

   parameter CLOCK_RATE_HZ = 100_000_000;
   parameter BAUD_RATE_HZ = 50_000_000;// 115_200;
   parameter CLOCKS_PER_BAUD = CLOCK_RATE_HZ / BAUD_RATE_HZ;

   logic [31:0]	baud_counter = CLOCKS_PER_BAUD - 1; // counts down, bit sent on zero
   logic	baud_stb; // bit sent when set
   assign baud_stb = (baud_counter == 0);
   
   // Bit 0 is mapped to tx. Initially outputs 1,
   // then changes to 0 (start bit) when transit
   // begins. At end, reset to all ones and bit
   // zero becomes stop bit.
   logic [9:0] tx_data = '1;
   assign tx = tx_data[0];

   enum /*[4:0]*/ { IDLE, START_BIT, DATA[8], STOP_BIT } state = IDLE;

   //initial { busy, state } = { 1'b0, IDLE };

   assign busy = (state != IDLE);
   
   always_ff @(posedge clk) begin
      if (write && !busy)
	// If transmit starts, reset baud counter
	baud_counter <= CLOCKS_PER_BAUD - 1;
      else if (baud_counter > 0)
	baud_counter <= baud_counter - 1;
      else if (busy)
	// If transmitting, then restart baud counter
	baud_counter <= CLOCKS_PER_BAUD - 1;
   end
   
   always_ff @(posedge clk) begin
      if (write && !busy) begin
	 // Load new data to transmit
	 tx_data <= { 1'b1, data, 1'b0 };
	 // Start a new transmission
	 state <= START_BIT;
      end
      else if (baud_stb) begin
	 // Only update state on baud strobe
	 if (busy && (state < STOP_BIT)) begin
	    tx_data <= { 1'b1, tx_data[9:1] };
	    state <= state + 1;
	 end
	 else begin
	    // Back to idle
	    state <= IDLE;
	    tx_data <= '1;
	 end
      end // if (baud_stb)
   end
	       
	       
endmodule
