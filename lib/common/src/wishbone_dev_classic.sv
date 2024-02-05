/// Simple Wishbone Classic Read/Write Cycle Device
///
/// Use this module as a simple interface to listen for
/// single read/write Wishbone B4 cycles.
///
/// The transaction begin when request is asserted. 
/// write_en determines whether the controller is 
/// requesting a read/write cycle.
///
/// On the first rising clock edge where request is asserted,
/// the device is free to respond to the request by reading/
/// write_data or setting write_data, setting ack to indicate
/// it has completed the request. Alternatively, the device
/// can delay ack by any number of clock cycles. During this
/// delay, both request and any data/write_en will remain stable.
///
/// After ack has been set, request will fall, indicating the
/// end of the transaction. A new transaction may then begin
/// immediately if request goes high again on the next transaction.
///
/// If the device never needs to stall, then ack may be tied
/// to 1 all the time. In this case, each transaction takes
/// two clock cycles (an asynchronous mode):
///
/// * On the first rising clock edge, request is asserted.
///   Since ack is set too, the device is confirming it has
///   read/returned data asynchronously on this clock edge.
/// * On the second rising clock edge, request falls to
///   indicate the end of the transaction
///
/// This may be appropriate for simple devices where, e.g.
/// read data is asynchronously available and tied to read_data,
/// so the data is always valid.
///
/// Alternatively, if the slave wants to operate synchronously,
/// it should not tie ack to 1. In this case, three clock cycles
/// are required to complete the transaction:
///
/// * On the first rising clock edge, request is asserted.
/// * On the second rising clock edge, the device reads that
///   request is asserted, and performs a synchronous action
///   (latching input data or setting output data), and sets
///   ack to indicate processing is finished
/// * On the third rising clock edge, request falls in
///   response to ack to indicate the end of the transaction.
///
/// In both cases, the device may wait any number of clock cycles
/// before asserting ack.
///
module wishbone_dev_classic #(
   parameter DAT_WIDTH = 8
) (
   output [DAT_WIDTH-1:0]      write_data,
   output		       request, write_en,  
   input [DAT_WIDTH-1:0]       read_data,
   input		       ack,
   wishbone_classic.device wb
);

   assign request = wb.cyc_i && wb.stb_i && !wb.ack_o;
   assign write_data = wb.dat_i;
   
   // Ensures ack_o is only high for one cycle, even if device
   // asserts ack for more than one cycle
   always_ff @(posedge wb.clk_i) begin: ack_control
      if (wb.rst_i || wb.ack_o)
	wb.ack_o <= 0;
      else if (request && ack)
	wb.ack_o <= 1;
   end
   
endmodule
  
