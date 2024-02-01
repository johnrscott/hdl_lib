/// Simple "Hello, World!" message, triggered by
/// a pushbutton and sent through a buffered UART
/// output
module hello_world(
    input	clk_i, rst_i,
    input [3:0]	buttons,
    output	uart_tx	
);

   localparam DEBOUNCE_PERIOD = 5_000_000;
   
   wishbone from_buttons(.clk_i, .rst_i);
   wishbone to_fifo(.clk_i, .rst_i);
   wishbone fifo_to_uart(.clk_i, .rst_i);

   // Input trigger from button
   buttons buttons(.buttons, .wb(from_buttons));

   // Custom logic (see below maps button trigger to FIFO

   // FIFO-to-UART wishbone-data-flow interconnected
   fifo fifo(.wb_i(to_fifo), .wb_o(fifo_to_uart));
   uart_tx uart_tx(.wb(fifo_to_uart), .uart_tx);

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

   logic button_request;
   assign button_request = from_buttons.cyc_o && from_buttons.stb_o;

   logic sending = 0;
   assign from_buttons.stall_i = button_request && sending;

   logic button_request_accepted;
   assign button_request_accepted = button_request && !sending;
   
   logic [3:0] char_counter = 0;
   assign to_fifo.dat_o = message[char_counter];

   logic fifo_request;
   assign button_request = to_fifo.cyc_o && to_fifo.stb_o;

   logic fifo_request_accepted;
   assign fifo_request_accepted = fifo_request && !to_fifo.stall_i;
   
   always_ff @(posedge from_buttons.clk_i) begin: button_trigger_sending
      if (from_buttons.rst_i)
	 sending <= 0;
      else if (button_request_accepted)
	 sending <= 1;
      else if (char_counter == 12)
	 sending <= 0;
   end

   always_ff @(posedge from_buttons.clk_i) begin: return_ack
      if (from_buttons.rst_i)
	from_buttons.ack_i <= 0;
      else if (button_request_accepted)
	 from_buttons.ack_i <= 1;
      else if (from_buttons.ack_i)
	from_buttons.ack_i <= 0;
   end

   /*
   always_ff @(posedge to_fifo.clk_i) begin: send_chars
      if (to_fifo.rst_i) begin
	 char_counter <= 0;
	 to_fifo.cyc_o <= 0;
	 to_fifo.stb_o <= 0;
      end
      else if (sending && !to_fifo.cyc_o) begin
	 to_fifo.cyc_o <= 1;
	 to_fifo.stb_o <= 1;
      end
      else if (fifo_request_accepted && (char_counter < 12))
	char_counter <= char_counter + 1;
      else if ((char_counter == 12) && to_fifo.ack_i) begin
	 char_counter <= 0;
	 to_fifo.cyc_o <= 0;
      end
   end
   */
   
endmodule
