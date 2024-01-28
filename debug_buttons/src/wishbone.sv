interface wishbone #(parameter DAT_WIDTH = 8)(input logic clk_i, rst_i);
   
   // From perspective of controller
   logic cyc_o, stb_o, we_o, ack_i, err_i, rty_i, stall_i;
   logic [DAT_WIDTH-1:0] dat_o;
   
   // State of cycle
   enum {
      IDLE, // cyc_o is low, transaction not in progress
      START_CYCLE, // cyc_o and stb_o set, stays here until stall_i is low
      AWAIT_DEV_RESPONSE // cyc_o set, stb_o cleared, wait for ack/err/rty  
   } state;
   
   modport controller(
      output cyc_o, stb_o, we_o,
      input  clk_i, rst_i, ack_i, err_i, rty_i, stall_i,
      import task cycle_process(logic, logic, logic [DAT_WIDTH-1:0])
   );

   modport device(
      output .ack_o(ack_i), .err_o(err_i), .rty_o(rty_i), .stall_o(stall_i),
      input clk_i, rst_i, .cyc_i(cyc_o), .stb_i(stb_o), .we_i(we_o)
   );
   
   task reset();
      cyc_o <= 0;
      stb_o <= 0;
      we_o <= 0;
   endtask // controller_reset

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
   task cycle_process(logic trigger, logic write, logic [DAT_WIDTH-1:0] data);
      if (rst_i)
	reset();
      else
	case (state)
	  IDLE: if (trigger) begin
	     dat_o <= data;
	     cyc_o <= 1;
	     stb_o <= 1;
	     we_o <= write;
	     state <= START_CYCLE;
	  end
	  START_CYCLE: if (!stall_i) begin
	     stb_o <= 0;
	     state <= AWAIT_DEV_RESPONSE;
	  end
	  AWAIT_DEV_RESPONSE: if (dev_response()) begin
	     cyc_o <= 0;
	     we_o <= 0;
	     state <= IDLE;
	  end
	endcase
   endtask;
      
   
endinterface
