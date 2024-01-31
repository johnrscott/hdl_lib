interface wishbone #(parameter DAT_WIDTH = 8)(input logic clk_i, rst_i);
   
   // From perspective of controller
   logic cyc_o, stb_o, we_o, ack_i, err_i, rty_i, stall_i;
   logic [DAT_WIDTH-1:0] dat_o;

   initial begin
      cyc_o = 0;
      stb_o = 0;
      we_o = 0;
      dat_o = 0;
   end
   
   modport controller(
      output cyc_o, stb_o, we_o, dat_o,
      input  clk_i, rst_i, ack_i, err_i, rty_i, stall_i
   );

   modport device(
      output .ack_o(ack_i), .err_o(err_i), .rty_o(rty_i), .stall_o(stall_i),
      input clk_i, rst_i, .cyc_i(cyc_o), .stb_i(stb_o), .we_i(we_o), .dat_i(dat_o)
   );
      
endinterface
