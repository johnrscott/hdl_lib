module fifo #(
   ADDR_WIDTH = 4
)(
   wishbone.device wb_i,
   wishbone.controller wb_o
);

   localparam DEPTH = (1 << ADDR_WIDTH);
   
   logic [7:0] buffer[DEPTH] = '{ default: '0 };

   logic [ADDR_WIDTH-1:0] read_addr, write_addr;

   // Give count an extra bit to express DEPTH
   logic [ADDR_WIDTH:0]	  count;
   
   logic		  push, pop, full, empty, wishbone_request;


   // Upstream wishbone controller makes request
   assign wishbone_request = wb_i.cyc_i && wb_i.stb_i;

   // Wishbone device stalls if the buffer is full
   assign wb_i.stall_o = wishbone_request && full;
   
   // Wishbone transaction accepted if not full
   assign push = wishbone_request && !full;
   
   fifo_addr_gen #(.ADDR_WIDTH(ADDR_WIDTH)) write_addr_gen(
      .clk(wb_i.clk_i),
      .rst(wb_i.rst_i),
      .inc(push),
      .addr(write_addr)
   );

   fifo_addr_gen #(.ADDR_WIDTH(ADDR_WIDTH)) read_addr_gen(
      .clk(wb_i.clk_i),
      .rst(wb_i.rst_i),
      .inc(pop),
      .addr(read_addr)
   );

   always_ff @(posedge wb_i.clk_i) begin: update_count
      if (wb_i.rst_i)
	count <= 0;
      else if (push && !pop)
	count <= count + 1;
      else if (pop && !push)
	count <= count - 1;
   end
   
   // Is the buffer full or empty?
   assign full = (count == DEPTH);
   assign empty = (count == 0);

   // Lags push by one clock
   always_ff @(posedge wb_i.clk_i) begin: wishbone_ack
      if (wb_i.rst_i)
	 wb_i.ack_o <= 0;
      else if (push)
	 wb_i.ack_o <= 1;
      else
	 wb_i.ack_o <= 0;
   end

   always_ff @(posedge wb_i.clk_i) begin: push_to_buffer
      if (wb_i.rst_i)
	buffer <= '{ default: '0 };
      else if (push)
	buffer[write_addr] <= wb_i.dat_i;
   end

`ifdef FORMAL

   // The fact this design has two clocks is really a defect.
   // In any real instantiation, both clocks should be derived
   // from the same thing (a common Wishbone SYSCON)
   default clocking@(posedge wb_i.clk_i);
   endclocking // wb_i

   // Same comment as above
   default disable iff (wb_i.rst_i);

   // Data in buffer always less than DEPTH
   no_overflow: assert property (count <= DEPTH);

   // Check that buffer can fill up
   buffer_full: cover property (full);
   
`endif
   
endmodule
