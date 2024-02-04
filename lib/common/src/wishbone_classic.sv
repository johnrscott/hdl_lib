interface wishbone_classic #(
   parameter DAT_WIDTH = 8
)(
   input logic clk_i, rst_i
);

   // From perspective of controller
   logic cyc_o, stb_o, we_o, ack_i, err_i, rty_i;
   logic [DAT_WIDTH-1:0] dat_o, dat_i;

   initial begin
      cyc_o = 0;
      stb_o = 0;
      we_o = 0;
      dat_o = 0;
   end
   
   modport controller(
      output cyc_o, stb_o, we_o, dat_o,
      input  clk_i, rst_i, ack_i, err_i, rty_i, dat_i
   );

   modport device(
      output .ack_o(ack_i), .err_o(err_i), .rty_o(rty_i), .dat_o(dat_i),
      input clk_i, rst_i, .cyc_i(cyc_o), .stb_i(stb_o), .we_i(we_o), .dat_i(dat_o)
   );

`ifdef FORMAL

   default clocking @(posedge clk_i);
   endclocking

   default disable iff (rst_i);

 `ifdef FAKE_WB_CONTROLLER
   // Use this if the top level module is a Wishbone device,
   // and needs Wishbone-controller assumptions to be satisfied
   // on an input port
   
 `endif

 `ifdef FAKE_WB_DEVICE
   // Use this if the top level module is a Wishbone controller,
   // and needs Wishbone-device assumptions to be satisfied
   // on an input port.

 `endif

   // Convenience definitions for Wishbone protocol
   logic request, responded;
   assign request = cyc_o && stb_o;
   assign response = ack_i || rty_i || err_i;
   
   sequence cycle(write_en, duration);
      !cyc_o[*10] ##1 (cyc_o && (we_o == write_en))[*duration] ##1 !cyc_o[*10]
   endsequence

   sequence not_cycle_start();
      cyc_o && !($rose(cyc_o) || $past(ack_i));
   endsequence
   
   sequence awaiting_response();
      cyc_o and not_cycle_start;
   endsequence // awaiting_response
   
   sequence request_stable();
      $stable(cyc_o) and $stable(stb_o) and $stable(we_o) and $stable(dat_o);
   endsequence // request_stable
   
   // 1. Wishbone B4 single read/write protocol
   
   // Device eventually responds to every request
   response_follows_request: assert property (request |-> ##[1:$] response);

   // Request signals are stable until response
   request_stable_until_response: assert property (awaiting_response |-> request_stable);
   
   // 2. Wishbone example traces

   two_cycle_single_write_cycle: cover property (cycle(1, 2));
   five_cycle_single_read_cycle: cover property (cycle(0, 5));
 
`endif
      
endinterface
