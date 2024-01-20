`default_nettype none

module hello_world(
   input logic clk, rst, trigger,
   output logic tx, sending
);

   parameter CLOCK_RATE = 100_000_000;
   parameter BAUD_RATE = 115_200;
   parameter CLOCKS_PER_BIT = CLOCK_RATE / BAUD_RATE;

   
   logic [7:0] message[2] = '{ default: 0 };

   logic       send, busy;
   logic [7:0] data;

   logic char_counter = 0;
   assign data = message[char_counter];

   assign send = sending && !busy;
   
   uart_tx #(.CLOCKS_PER_BIT(CLOCKS_PER_BIT)) uart_tx(
      .clk, .rst, .send, .data, .busy, .tx);

   always_ff @(posedge clk) begin
      if (rst)
	char_counter <= 0;
      else if (trigger && !sending) begin
	 char_counter <= 0;
	 sending <= 1;
      end
      else if (sending && !busy)
	if (char_counter == 10)
	  char_counter <= 0;
	else
	  char_counter <= char_counter + 1;
   end
   
   
   
endmodule