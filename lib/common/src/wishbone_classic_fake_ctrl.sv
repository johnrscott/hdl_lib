/// Connect this stub module to wishbone device
/// module-under-test to simulate the behaviour of a
/// controller for formal verification purposes
module wishbone_classic_fake_ctrl(
   wishbone_classic.controller wb
);

`ifdef FORMAL
   
   default clocking @(posedge wb.clk_i);
   endclocking //

   default disable iff (wb.rst_i);
   
   //assume_request_stable_until_response: assume property (awaiting_response |=> request_data_stable);
   //thingy: cover property ((request ##1 !request));
   //thingy1: cover property ((request ##1 !request) ##0 $past(response));

   // The only way request can terminate is if ack is high 
   assume_cyc_high_until_response: assume property ((request ##1 !request) |-> $past(response));

`endif

   
endmodule
