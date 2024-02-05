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

   // Convenience definitions for Wishbone protocol
   logic request, responded;
   assign request = cyc_o && stb_o;
   assign response = ack_i || rty_i || err_i;
   
   sequence not_cycle_start();
      cyc_o && !($rose(cyc_o) || $past(ack_i));
   endsequence

   sequence start_from_idle();
      !$past(request) && request;
   endsequence

   /// This case can happen in Wishbone classic if the controller
   /// continues to assert cyc_o and stb_o after the device has
   /// acknowledged the transaction for one clock (thereby ending
   /// the previous cycle)
   sequence start_from_previous_cycle();
      $past(request) && $past(ack_i) && request && !ack_i;
   endsequence
   
   sequence cycle_start();
      start_from_idle or start_from_previous_cycle;  
   endsequence
   
   sequence awaiting_response();
      cyc_o and not_cycle_start;
   endsequence // awaiting_response
   
   sequence request_data_stable();
      $stable(stb_o) and $stable(we_o) and $stable(dat_o);
   endsequence // request_stable

   sequence wishbone_idle(duration);
      !cyc_o[*duration]
   endsequence

   /// An async-ack cycle is one where the device asserts ack_i combinationally
   /// based on cyc_o and stb_o (so it happens in the same cycle), and the
   /// cycle therefore terminates in one cycle.
   sequence async_ack_cycle();
      cycle_start and ack_i;
   endsequence
   
   /// A sync-ack cycle is one where the device registers ack_i, so it comes
   /// one clock after cyc_o and stb_o at the earliest. The device may insert
   /// arbitrary wait states (meaning ack_i is delayed by arbitrary many cycles).
   sequence sync_ack_cycle();
      cycle_start ##[1:$] ack_i;
   endsequence

   sequence cycle();
      sync_ack_cycle or async_ack_cycle;
   endsequence

   sequence cycle_ended();
      cyc_o ##1 !cyc_o
   endsequence
   
   // 1. Wishbone B4 single read/write protocol
   
   response_follows_request: assert property (request |-> ##[1:$] response);
   request_stable_until_response: assert property (awaiting_response |-> request_data_stable);
   cyc_high_until_response: assert property ((cyc_o && !ack_i) |=> $stable(request));
   
   // 2. Wishbone example traces

   single_write_cycle: cover property (wishbone_idle(10) ##1 cycle ##1 wishbone_idle(10));

   // 3. Assumptions if only one or other side of the interface
   // is connected
   
 `ifdef FAKE_WB_CONTROLLER
   // Use this if the top level module is a Wishbone device,
   // and needs Wishbone-controller assumptions to be satisfied
   // on an input port

   assume_request_stable_until_response: assume property (awaiting_response |-> request_data_stable);   

   assume_cyc_high_until_response: assume property ((cyc_o && !ack_i) |=> $stable(request));
   
 `endif

 `ifdef FAKE_WB_DEVICE
   // Use this if the top level module is a Wishbone controller,
   // and needs Wishbone-device assumptions to be satisfied
   // on an input port.

 `endif

   
`endif
      
endinterface
