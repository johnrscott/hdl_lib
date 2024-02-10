`ifndef DEBOUNCE_PERIOD
 `define DEBOUNCE_PERIOD 5_000_000
`endif

/// Simple "Hello, World!" message, triggered by
/// a pushbutton and sent through a buffered UART
/// output
module hello_world(
    input	clk_i, rst_i,
    input [3:0]	buttons,
    output	uart_tx	
);

   wishbone_classic wb_from_btn(.clk_i, .rst_i);
   wishbone_classic wb_to_fifo(.clk_i, .rst_i);
   wishbone_classic wb_to_uart(.clk_i, .rst_i);

   logic char_pushed, sending, button_pressed;
   logic [3:0] counter;

   // Buttons pushes trigger wishbone cycle
   buttons #(.DEBOUNCE_PERIOD(`DEBOUNCE_PERIOD)) btns(.buttons, .wb(wb_from_btn));
   
   wishbone_dev_classic dev(
      .request(button_pressed),
      .wb(wb_from_btn)
   );

   wishbone_ctrl_classic ctrl(
      .ack(char_pushed),
      .write_data(message[counter]),
      .start(sending),
      .wb(wb_to_fifo)
   );
   
   fifo fifo(.wb_i(wb_to_fifo), .wb_o(wb_to_uart));
   uart_tx uart_tx(.wb(wb_to_uart), .uart_tx);

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

   always_ff @(posedge clk_i) begin: trigger_send
      if (rst_i)
	sending <= 0;
      else if (button_pressed && !sending)
	sending <= 1;
      else if (counter == 12)
	sending <= 0;
   end

   always_ff @(posedge clk_i) begin: inc_counter
      if (rst_i)
	counter <= 0;
      else if (sending && char_pushed)
	if (counter == 12)
	  counter <= 0;
	else
	  counter <= counter + 1;
   end
   
endmodule
