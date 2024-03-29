interface wishbone_classic #(
   parameter DAT_WIDTH = 8
)(
   input logic clk_i, rst_i
);

   logic cyc, stb, we = 0, ack = 0, err = 0, rty = 0;

   /// Would be better to name them dat_o and dat_i, but due to a
   /// Vivado bug (I think) this doesn't synthesize properly. Key point
   /// is not to have overlaps between modport expression names and internal
   /// signal names
   logic [DAT_WIDTH-1:0] dat_out, dat_in;

   modport controller(
      output .cyc_o(cyc), .stb_o(stb), .we_o(we), .dat_o(dat_out),
      input  clk_i, rst_i, .ack_i(ack), .err_i(err), .rty_i(rty), .dat_i(dat_in)
   );

   modport device(
      // For future reference: this is the bit which causes the synthesis to
      // fail -- apparently something to do with using dat_i and dat_o as expression
      // names. To run the synthesis, change to the xilinx/ folder, make a folder
      // called build/ and change into it, then vivado -mode tcl and run run.tcl
      // line by line. Use start_gui and show_schematic [get_nets] to look at
      // the issues.
      output .ack_o(ack), .err_o(err), .rty_o(rty), .dat_o(dat_in),
      input clk_i, rst_i, .cyc_i(cyc), .stb_i(stb), .we_i(we), .dat_i(dat_out)
   );

   function int bar();
      return (3);
   endfunction
   
   function int foo();
      return(bar());
   endfunction
   
`ifdef FORMAL

   default clocking @(posedge clk_i);
   endclocking

   default disable iff (rst_i);

   // Convenience definitions for Wishbone protocol
   logic request, responded;
   assign request = cyc && stb;
   assign response = ack || rty || err;
   
   sequence not_cycle_start();
      cyc && !($rose(cyc) || $fell(response));
   endsequence

   sequence start_from_idle();
      !$past(request) && request;
   endsequence

   /// This case can happen in Wishbone classic if the controller
   /// continues to assert cyc and stb after the device has
   /// acknowledged the transaction for one clock (thereby ending
   /// the previous cycle)
   sequence start_from_previous_cycle();
     request && $stable(request) && $fell(response);
   endsequence
   
   sequence cycle_start();
      start_from_idle or start_from_previous_cycle;  
   endsequence
   
   sequence awaiting_response();
      request and !response;
   endsequence // awaiting_response
   
   sequence request_data_stable();
      $stable(request) and $stable(we) and $stable(dat_out);
   endsequence // request_stable

   sequence wishbone_idle(duration);
      !cyc[*duration]
   endsequence

   /// An async-ack cycle is one where the device asserts ack combinationally
   /// based on cyc and stb (so it happens in the same cycle), and the
   /// cycle therefore terminates in one cycle.
   sequence async_ack_cycle();
      cycle_start and response;
   endsequence
   
   /// A sync-ack cycle is one where the device registers ack, so it comes
   /// one clock after cyc and stb at the earliest. The device may insert
   /// arbitrary wait states (meaning ack is delayed by arbitrary many cycles).
   sequence sync_ack_cycle();
      cycle_start ##[1:$] response;
   endsequence

   sequence cycle();
      sync_ack_cycle or async_ack_cycle;
   endsequence

   sequence cycle_ended();
      cyc ##1 !cyc
   endsequence
   
   // 1. Wishbone B4 single read/write protocol
   
   response_follows_request: assert property (request |-> ##[1:$] response);
   //request_stable_until_response: assert property (awaiting_response |=> request_data_stable);
   cyc_high_until_response: assert property ((request ##1 !request) |-> $past(response));
   
   // 2. Wishbone example traces

   single_write_cycle: cover property (wishbone_idle(10) ##1 cycle ##1 wishbone_idle(10));

   // 3. Assumptions if only one or other side of the interface
   // is connected
      
   
`endif
      
endinterface
