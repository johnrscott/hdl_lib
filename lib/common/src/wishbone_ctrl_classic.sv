/// Simple Wishbone Classic Read/Write Cycle Controller
///
/// This module implements the Wishbone B4 specification
/// classic single read/write cycle.
///
/// A write transaction is prepared by setting write_data,
/// setting write_en, and asserting start. The cyc signal
/// is set while the cycle is underway, and ack is set to
/// indicate cycle completion.
///
/// A read transaction is prepared by clearing write_en, and
/// asserting start. The cyc signal is set while the transaction
/// is underway, and ack is set to indicate that read_data
/// contains valid data.
///
/// Multiple transactions can be performed back to back by
/// keeping start asserted. In this case, data for the next
/// transaction should be maintained until ack is asserted,
/// at which point new write_data/write_en can be loaded.
///  
module wishbone_ctrl_classic #(
   parameter DAT_WIDTH = 8
)(
   output [DAT_WIDTH-1:0]      read_data,
   output		       cyc, ack,
   input [DAT_WIDTH-1:0]       write_data,
   input		       write_en,
   input		       start,
   wishbone_classic.controller wb
);

   assign cyc = wb.cyc_o;
   assign ack = wb.ack_i;
   assign read_data = wb.dat_i;

   assign wb.cyc_o = wb.stb_o;

   // Set prior to the first clock cycle of the wishbone cycle.  Used
   // to latch data (write_data and write_en), and set cyc/stb. Set
   // either when start is asserted and no cycle is in progress, or
   // when a cycle is in progress, but start is set and ack is set
   // (the last clock cycle before a back-to-back wishbone cycle)
   logic cycle_start;
   assign cycle_start = start && (!cyc || ack);
   
   always_ff @(posedge wb.clk_i) begin: start_transaction
      if (wb.rst_i) begin
	 wb.stb_o <= 0;
	 wb.dat_o <= 0;
	 wb.we_o <= 0;
      end
      else if (cycle_start) begin
	 wb.stb_o <= 1;
	 wb.dat_o <= write_data;
	 wb.we_o <= write_en;
      end
      else if (ack) begin
	 wb.stb_o <= 0;
	 wb.dat_o <= 0;
	 wb.we_o <= 0;
      end 
   end
   
`ifdef FORMAL

   default clocking @(posedge wb.clk_i);
   endclocking

   default disable iff (wb.rst_i);

`endif
   
endmodule

/// Wrap the module with the Wishbone interface in order to
/// instantiate (and therefore run assertions in) the interface
module wishbone_ctrl_classic_formal(input clk_i, rst_i);

   logic cyc, ack, write_en, start;
   logic [7:0] write_data, read_data;
   
   wishbone_classic wb(.clk_i, .rst_i);
   wishbone_ctrl_classic ctrl(.*);
   
endmodule
