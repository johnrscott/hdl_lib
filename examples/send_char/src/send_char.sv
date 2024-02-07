`ifndef DEBOUNCE_PERIOD
 `define DEBOUNCE_PERIOD 5_000_000
`endif

module send_char(
   input	clk_i, rst_i,
   input [3:0]	buttons, switches,
   output logic	uart_tx
);

   logic request, send_char;
   logic [7:0] btn_data, char_to_send;

   wishbone_classic wb_from_btn(.clk_i, .rst_i);
   wishbone_classic wb_to_uart(.clk_i, .rst_i);
   
   // Buttons pushes trigger wishbone cycle
   buttons #(.DEBOUNCE_PERIOD(`DEBOUNCE_PERIOD)) btns(.buttons, .switches, .wb(wb_from_btn));

   // Read the button wishbone output
   wishbone_dev_classic dev(
      .write_data(btn_data),
      .request,
      .ack(1'b1), // risks missing button pushes, but UART is much faster than repeated pushes
      .wb(wb_from_btn)
   );

   always_ff @(posedge clk_i) begin: map_buttons_to_chars
      if (rst_i)
	char_to_send <= "!";
      else if (request)
	case (btn_data)
	  0: char_to_send <= "0";
	  1: char_to_send <= "1";
	  2: char_to_send <= "2";
	  4: char_to_send <= "3";
	  default: char_to_send <= "u"; // unknown
	endcase		
   end

   always_ff @(posedge clk_i) begin: trigger_send_char
      if (rst_i)
	send_char <= 0;
      else if (request)
	send_char <= 1;
      else if (send_char)
	send_char <= 0;
   end
   
   // Push char data to UART via wishbone
   wishbone_ctrl_classic ctrl(
      .write_data(char_to_send),
      .write_en(1'b1),
      .start(send_char),
      .wb(wb_to_uart)
   );

   // Char data sent out over uart
   uart_tx u0(.uart_tx, .wb(wb_to_uart));
   
endmodule
