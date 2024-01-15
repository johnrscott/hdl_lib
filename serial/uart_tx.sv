module uart_tx(
   input logic	     clk, rst, send,
   input logic [7:0] data,
   output logic	     busy, tx
);

   parameter CLOCK_RATE_HZ = 100_000_000;
   parameter BAUD_RATE_HZ = 50_000_000;// 115_200;
   parameter CLOCKS_PER_BAUD = CLOCK_RATE_HZ / BAUD_RATE_HZ;

   logic [31:0]	baud_counter = 0;
   
   // Bit 0 is mapped to tx. Initially outputs 1,
   // then changes to 0 (start bit) when transit
   // begins. At end, reset to all ones and bit
   // zero becomes stop bit.
   logic [9:0] shift_register = '1, shift_register_init = '1;
   assign tx = shift_register[0];

   // For the purposes of state, DATA includes the start
   // bit.
   enum [4:0] { IDLE, DATA, STOP } state = IDLE, next_state = IDLE;
   logic [3:0] bit_counter = 0; 

   assign busy = (state != IDLE);

   always_comb begin: output_and_next_state
      case (state)
	IDLE: if (send) begin
	   shift_register_init = { 1'b1, tx_data, 1'b0 }
	   next_state = DATA;
	end
	DATA: ;
	STOP: ;
      endcase
   end

   // Update the shift register on a new
   // transaction, or reset
   always_ff @(posedge clk) begin: update_shift_reg
      if (rst)
	shift_register <= '1;
      else if (busy )
	shift_register 

   end
   
   // Update state or reset
   always_ff @(posedge clk) begin: update_state
      if (rst) begin
	 state <= IDLE;
      end else
	state <= next_state;
   end

   // Increment bit counter if in the DATA state,
   // or reset
   always_ff @(posedge clk) begin: increment_bit_count
      if (rst)
	bit_counter <= 0;
      else if (state == DATA)
	bit_counter <= bit_counter + 1;
   end

   // Increment the baud counter 

     
   /*
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
	    */   
	       
endmodule
