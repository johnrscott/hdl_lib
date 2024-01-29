import types::rgb_led_t;

module top(
   // External clock (e3) and active-low reset (c2)
   input	      clk_ext, rstn_ext,

   // Input/output
   input logic [3:0]  buttons, switches,
   output logic [3:0] green_leds,
   output	      rgb_led_t [3:0] rgb_leds,
		  
   // UART signals
   output uart_tx, uart_tx_debug
);

   // These internal signals are common to all the Wishbone
   // modules.
   logic rst_i, clk_i;

   // Generate the Wishbone reset from the external reset
   assign rst_i = !rstn_ext;
   
   // Generate the Wishbone clock from the external clock
   // via the clocking wizard
   clk_wiz_0 clk_wiz_0(
      .clk_in1(clk_ext),
      .clk_out1(clk_i)
   );

   // Route the UART signals to headers for debugging
   assign uart_tx_debug = uart_tx;
   
   // Pick the top level module here (defined by the TCL
   // script). It will pick the ports it needs from the
   // inputs (otherwise will be tied to ground).
   `MOD `MOD(.*);

endmodule
