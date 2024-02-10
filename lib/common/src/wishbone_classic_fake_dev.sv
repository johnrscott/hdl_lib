/// Connect this stub module to wishbone controller
/// module-under-test to simulate the behaviour of a
/// device for formal verification purposes.
module wishbone_classic_fake_dev(
   wishbone_classic.device wb
);

`ifdef FORMAL
   
   default clocking @(posedge wb.clk_i);
   endclocking //

   default disable iff (wb.rst_i);

   // Convenience definitions for Wishbone protocol
   logic request, responded;
   assign request = wb.cyc_i && wb.stb_i;
   assign response = wb.ack_o || wb.rty_o || wb.err_o;

   // No response unless a request is in progress
   no_response_without_request: assume property (response |-> request);
   
`endif
   
endmodule
