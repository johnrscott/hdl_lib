interface wishbone #(parameter DAT_WIDTH = 8)(input logic clk_i, rst_i);
   
   // From perspective of controller
   logic cyc_o, stb_o, we_o, ack_i, err_i, rty_i, stall_i;
   logic [DAT_WIDTH-1:0] dat_o;

   // The stall_i logic from the device should be unregistered (i.e.
   // it should update along with a change in cyc_o and stb_o). This
   // is achieved here by driving it from an internal busy signal
   // (managed by the device) which is asynchronously combined with
   // cyc_o and swtb_o to make stall_i;
   logic		 busy;
   assign stall_o = busy && cyc_o && stb_o;
   
   // State of cycle
   enum {
      CTRL_IDLE, // cyc_o is low, transaction not in progress
      START_CYCLE, // cyc_o and stb_o set, stays here until stall_i is low
      AWAIT_DEV_RESPONSE // cyc_o set, stb_o cleared, wait for ack/err/rty  
   } ctrl_state;

   modport controller(
      output cyc_o, stb_o, we_o,
      input  clk_i, rst_i, ack_i, err_i, rty_i, stall_i,
      import task cycle_process(logic trigger, logic write, logic [DAT_WIDTH-1:0] data)
   );

   modport device(
      output .ack_o(ack_i), .err_o(err_i), .rty_o(rty_i), .stall_o(stall_i),
      input clk_i, rst_i, .cyc_i(cyc_o), .stb_i(stb_o), .we_i(we_o)
   );
   
   task ctrl_reset();
      cyc_o <= 0;
      stb_o <= 0;
      we_o <= 0;
   endtask // ctrl_reset

   task dev_reset();
      ack_i <= 0;
      rty_i <= 0;
      err_i <= 0;
   endtask // ctrl_reset
   

   /// High if device returns acknowledge, retry, or
   /// error responses
   function logic dev_response();
      return (ack_i || rty_i || err_i);
   endfunction
   
   /// Put this is an always_ff block to manage read/write cycles
   /// initiated by the controller. On a rising edge where trigger is
   /// high, a read/write cycle will be initiated (latching the data
   /// for a write). If trigger is high while a cycle is already in
   /// progress, the request is ignored.
   task cycle_process(input logic trigger, input logic write, input logic [DAT_WIDTH-1:0] data);
      if (rst_i)
	ctrl_reset();
      else
	case (ctrl_state)
	  CTRL_IDLE: if (trigger) begin
	     dat_o <= data;
	     cyc_o <= 1;
	     stb_o <= 1;
	     we_o <= write;
	     ctrl_state <= START_CYCLE;
	  end
	  START_CYCLE: if (!stall_i) begin
	     stb_o <= 0;
	     ctrl_state <= AWAIT_DEV_RESPONSE;
	  end
	  AWAIT_DEV_RESPONSE: if (dev_response()) begin
	     cyc_o <= 0;
	     we_o <= 0;
	     ctrl_state <= CTRL_IDLE;
	  end
	endcase
   endtask;

   /// Put this is an always_ff block in the device to await a cycle
   /// from the wishbone controller. The device can set the busy signal
   /// when it cannot accept a transaction, which will drive the stall
   //    
   task await_cycle();
      if (rst_i)
	dev_reset();
      else if ()

	
     endtask
   
endinterface
