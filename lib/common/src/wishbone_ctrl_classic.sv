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
// A read transaction is prepared by clearing write_en, and
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
   assign wb.we_o = write_en && wb.cyc_o;
   assign wb.dat_o = write_data;
   
   always_ff @(posedge wb.clk_i) begin: start_transaction
      if (wb.rst_i)
	wb.stb_o <= 0;
      else if (start)
	wb.stb_o <= 1;
      else if (wb.ack_i)
	wb.stb_o <= 0;
   end

endmodule
