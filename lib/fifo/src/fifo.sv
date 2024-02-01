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
   logic [ADDR_WIDTH:0]	  count = 0;
   
   logic		  push, pop, full, empty, wishbone_dev_request,
			  wishbone_ctrl_request, await_ack = 0;

   // Upstream wishbone controller makes request
   assign wishbone_dev_request = wb_i.cyc_i && wb_i.stb_i;

   // Wishbone controller request
   assign wishbone_ctrl_request = wb_o.cyc_o && wb_o.stb_o;
   
   // Wishbone device stalls if the buffer is full
   assign wb_i.stall_o = wishbone_dev_request && full;
   
   // Wishbone transaction accepted if not full
   assign push = wishbone_dev_request && !full;

   // Using the await_ack in the condition guarantees that the pop
   // only happens once per transaction (guards against a device
   // where ack is tied high).
   assign pop = await_ack && wb_o.ack_i;

   // Route read-data to the downstream data interface
   assign wb_o.dat_o = buffer[read_addr];
   
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

   // Acknowledge lags push by one clock
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

   always_ff @(posedge wb_o.clk_i) begin: wishbone_send_data
      if (wb_o.rst_i) begin
	 await_ack <= 0;
	 wb_o.cyc_o <= 0;
	 wb_o.stb_o <= 0;
      end
      else if (!empty && !wb_o.cyc_o) begin
	 wb_o.cyc_o <= 1;
	 wb_o.stb_o <= 1;	 
      end
      else if (wishbone_ctrl_request && !wb_o.stall_i) begin
	 wb_o.stb_o <= 0;
	 // Check if device returns ack immediately. Otherwise,
	 // set state to wait for ack.
	 if (wb_o.ack_i)
	   wb_o.cyc_o <= 0;
	 else	   
	   await_ack <= 1;	      
      end
      else if (wb_o.ack_i && await_ack) begin
	 wb_o.cyc_o <= 0;
	 await_ack <= 0;	 
      end
   end   

`ifdef FORMAL

   // The fact this design has two clocks is really a defect.
   // In any real instantiation, both clocks should be derived
   // from the same thing (a common Wishbone SYSCON)
   default clocking@(posedge wb_i.clk_i);
   endclocking // wb_i

   // Same comment as above
   default disable iff (wb_i.rst_i);

   // Assume that the clocks and resets are always equal
   clocks_equal: assume property (disable iff (0) wb_i.clk_i == wb_o.clk_i);
   resets_equal: assume property (disable iff (0) wb_i.rst_i == wb_o.rst_i);
   
   // Data is only ever added or removed one item at a time
   count_inc_or_dec: assert property (
      (count == 0) ||
      $stable(count) ||
      (count == $past(count) + 1) ||
      (count == $past(count) - 1));
   
   // Data in buffer always less than DEPTH
   no_overflow: assert property (count <= DEPTH);

   // Check that buffer can fill up
   buffer_full: cover property (full);

   sequence non_stalled_push;
      wishbone_dev_request ##1 wb_i.ack_o;
   endsequence

   sequence stalled_push;
      wb_i.stall_o[*1:$] ##1 wishbone_dev_request ##1 wb_i.ack_o;
   endsequence
   
   // Assume upstream wishbone controller holds cyc high for
   // duration of wishbone cycle (until ack is returned)
   cycle_duration: assume property (
      wishbone_dev_request |-> wb_i.cyc_i s_until_with wb_i.ack_o);

   // Assume upstream wishbone controll keeps stb low
   // unless cyc is high (not required0
   //stb_implies_cyc: assume property (wb_i.stb_i |-> wb_i.cyc_i);

   // Assume that the downstream Wishbone device only raises
   // stall if cyc and stb are set
   downstream_stall_valid: assume property (
      wb_o.stall_i |-> wb_o.cyc_o && wb_o.stb_o);

   // Assume that the downstream returns ack the cycle after it
   // has accepted the transaction
   downstream_ack_follows_pop: assume property (
      wb_o.cyc_o && wb_o.stb_o && !wb_o.stall_i |=> wb_o.ack_i);

   // Assume that the downstream returns ack only if cyc is high,
   // 
   downstream_ack_valid: assume property (wb_o.ack_i |-> wb_o.cyc_o);

   wishbone_simple_push: cover property (
      !wb_i.cyc_i[*10]
      ##1 non_stalled_push
      ##1 !wb_i.cyc_i[*10]
   );

   wishbone_stalled_push: cover property (
      !wb_i.cyc_i[*10]
      ##1 stalled_push
      ##1 !wb_i.cyc_i[*10]
   );

   // Check that await_ack is only ever set when cyc_o is set
   await_ack_valid: assert property (await_ack |-> wb_o.cyc_o);

   // Check a transaction can never be occurring if the buffer is empty
   // (since the pop occurs at the end of the cycle)
   no_send_while_empty: assert property (empty |-> !wb_o.cyc_o);
   
`endif
   
endmodule
