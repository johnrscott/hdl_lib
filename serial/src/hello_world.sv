`default_nettype none

module hello_world(
   input logic clk, rst, trigger,
   output logic tx, sending
);

   parameter CLOCK_RATE = 5;//100_000_000;
   parameter BAUD_RATE = 1;//115_200;
   parameter CLOCKS_PER_BIT = CLOCK_RATE / BAUD_RATE;

   
   logic [7:0] message[5];

   initial begin
      message[0] = "H";
      message[1] = "e";
      message[2] = "l";
      message[3] = "l";
      message[4] = "o";
   end
   
   logic       send, busy;
   logic [7:0] data;

   logic [3:0] char_counter = 0;
   assign data = message[char_counter];

   assign send = sending && !busy;
   
   uart_tx #(.CLOCKS_PER_BIT(CLOCKS_PER_BIT)) uart_tx(
      .clk, .rst, .send, .data, .busy, .tx);

   always_ff @(posedge clk) begin
      if (rst) begin
	 sending <= 0;
	 char_counter <= 0;
      end
      else if (trigger && !sending) begin
	 char_counter <= 0;
	 sending <= 1;
      end
      else if (sending && !busy)
	if (char_counter == 5) begin
	   sending <= 0;
	   char_counter <= 0;
	end
	else
	  char_counter <= char_counter + 1;
   end
   
   
   
endmodule
