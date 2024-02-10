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

`endif
   
endmodule
