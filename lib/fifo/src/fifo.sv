module fifo #(
   ADDR_WIDTH = 4
)(
   wishbone_classic.device wb_i,
   wishbone_classic.controller wb_o
);

   localparam DEPTH = (1 << ADDR_WIDTH);
   
   logic [7:0] buffer[DEPTH] = '{ default: '0 };

   logic [ADDR_WIDTH-1:0] read_addr, write_addr;

   logic [7:0]		  push_data;

   // Extra bit to express DEPTH (for full check)
   logic [ADDR_WIDTH:0] count = 0;
   
   logic		  push_request, start_pop, pop_request, pop, push, full, empty;

   assign full = (count == DEPTH);
   assign empty = (count == 0);
   
   assign push = push_request && !full;
   assign pop = pop_request && !empty;

   assign start_pop = !empty && !wb_o.cyc_o;;
   
   wishbone_dev_classic dev(
      .write_data(push_data),
      .request(push_request),
      .ack(push),
      .wb(wb_i)
   );

   wishbone_ctrl_classic ctrl(
      .ack(pop_request),
      .write_data(buffer[read_addr]),
      .write_en(1'b1),
      .start(start_pop),
      .wb(wb_o)
   );
   
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
   count_in_range: assert property (count <= DEPTH);

   sequence overflow;
      (count == DEPTH) && push && !pop;
   endsequence
   
   no_overflow: assert property (not overflow);

   sequence underflow;
      (count == 0) && pop && !push;
   endsequence
   
   no_underflow: assert property (not underflow);

   no_pop_if_empty: assert property ((empty && !wb_o.cyc_o) |=> !wb_o.cyc_o);
   
   // Check that buffer can fill up
   buffer_full: cover property (full);

   // Check that the buffer can fill up and then empty
   buffer_full_then_empty: cover property (full ##[1:$] empty);

   // Check that a push/pop can occur simultaneously (check two in a row)
   simultaneous_push_pop: cover property (push && pop ##[1:5] push && pop);

   sequence push_value(value);
      ((wb_i.dat_i == value) && $rose(wb_i.cyc_i)) ##[1:$] push;
   endsequence

   sequence pop_value(value);
      ((wb_o.dat_o == value) && $rose(wb_i.cyc_i)) ##[1:$] pop;
   endsequence
   
   // Check a push/pop of real data
   check_pop_after_push: cover property (push_value(4) ##[0:$] pop_value(4));
   
   // Check that nothing is sent while the buffer is empty (transaction
   // ends with pop on ack -- buffer becomes empty on the same cycle that
   // stb and cyc fall)
   //no_send_while_empty: assert property (empty |-> (!wb_o.cyc_o && !wb_o.stb_o));

   // Check the buffer can be full
   //buffer_full: cover property (empty ##[1:$] full ##[1:$] empty);

   //invalid_pop: cover property ((empty && !wb_o.cyc_o) ##1 (empty && wb_o.cyc_o));

   //invalid_pop_2: cover property (empty && $stable(empty) && $fell(wb_o.cyc_o));
   
   /*
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
   */
`endif
   
endmodule

module fifo_formal(input logic clk_i, rst_i);

   wishbone_classic wb_i(.clk_i, .rst_i);
   wishbone_classic wb_o(.clk_i, .rst_i);

   wishbone_classic_fake_ctrl ctrl(.wb(wb_i));
   wishbone_classic_fake_dev dev(.wb(wb_o));

   fifo dut(.wb_i, .wb_o);
   
endmodule
