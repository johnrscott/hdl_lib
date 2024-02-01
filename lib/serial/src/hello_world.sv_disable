//`default_nettype none

module hello_world(
   input logic clk, rst, trigger,
   output logic tx, busy
);

   parameter CLOCK_RATE = 100_000_000;
   parameter BAUD_RATE = 115_200;
   parameter CLOCKS_PER_BIT = CLOCK_RATE / BAUD_RATE;

   
   logic [7:0] message[13];

   initial begin
      message[0] = "H";
      message[1] = "e";
      message[2] = "l";
      message[3] = "l";
      message[4] = "o";
      message[5] = ",";
      message[6] = " ";
      message[7] = "W";
      message[8] = "o";
      message[9] = "r";
      message[10] = "l";
      message[11] = "d";
      message[12] = "!";
   end

   enum logic [2:0] { IDLE, LOAD, SEND } state;
   
   logic       send, char_busy;
   logic [7:0] data;

   logic [3:0] char_counter = 0;
   assign data = message[char_counter];
   
   uart_tx uart_tx(
      .clk, .rst, .send, .data, .busy(char_busy), .tx);

   always_ff @(posedge clk) begin: update_state
      if (rst) begin
	 state <= IDLE;
	 send <= 0;
	 char_counter <= 0;
      end
      else
	case (state)
	  IDLE: if (trigger && !busy) begin
	     busy <= 1;
	     state <= LOAD;
	  end
	  else begin
	     busy <= 0;
	     send <= 0;
	  end
	  LOAD: begin
	     send <= 1;
	     state <= SEND;
	  end
	  SEND: begin
	     send <= 0;
	     if (!send && !char_busy) begin
		if (char_counter == 12) begin
		   char_counter <= 0;
		   busy <= 0;
		   state <= IDLE;
		end
		else begin
		   char_counter <= char_counter + 1;
		   state <= LOAD;
		end
	     end // if (!send && !char_busy)
	  end
	
endcase	
   end
   
endmodule
