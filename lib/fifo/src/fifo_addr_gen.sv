/// Wrapping address generation for FIFO
///
/// On (synchronous) reset, set the address
/// output to zero. Otherwise, increment
/// address on rising edge of clk if inc is
/// set, wrapping back to zero above MAX_DATA.
module fifo_addr_gen 
#(
   parameter ADDR_WIDTH=4
)(
   input	    inc, clk, rst,
   output reg [ADDR_WIDTH-1:0] addr
);
   localparam ADDR_BOUND = (1 << ADDR_WIDTH);
   
   initial addr = 0;

    // async reset
    // increment address when enabled
   always @(posedge clk or posedge rst)
     if (rst)
       addr <= 0;
     else if (inc) begin
        if (addr == ADDR_BOUND-1)
          addr <= 0;
        else
          addr <= addr + 1;
     end

`ifdef FORMAL

   default clocking @(posedge clk);
   endclocking

   default disable iff (rst);

   sequence max_addr;
      addr == ADDR_BOUND - 1;
   endsequence
   
   /// Address is always in range
   addr_in_range: assert property (addr < ADDR_BOUND);

   /// Address wraps at ADDR_BOUND
   addr_wraps: assert property ((inc and max_addr) |=> (addr == 0));

   /// Address does not change unless incremented
   addr_stable: assert property (!inc |=> $stable(addr));

   /// Address always increments by one unless wrapping
   addr_increments: assert property (inc |=> (addr == $past(addr) + 1) or (addr == 0));
   
`endif
   
endmodule
