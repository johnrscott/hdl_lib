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
      ((wb_i.dat_i == value) && $rose(wb_i.cyc_i && wb_i.stb_i)) ##[1:$] push;
   endsequence

   sequence pop_value(value);
      ((wb_o.dat_o == value) && $rose(wb_i.cyc_i)) ##[1:$] pop;
   endsequence
   
   // Check a push/pop of real data
   check_pop_after_push: cover property (push_value(4) ##[0:$] pop_value(4));

   // Check two pushes then two pops
   check_pop2_after_push2: cover property (
      push_value(2) ##[0:$] push_value(4) ##[0:$] pop_value(2) ##[0:$] pop_value(4)
   );

   // Makes no difference
   initial begin
      wb_o.cyc_o = 0;
      wb_o.stb_o = 0;
   end
   
   logic pop_wb_request;
   assign pop_wishbone_request = wb_o.cyc_o && wb_o.stb_o;
   
   // Prove that no pop can be initiated if the buffer is empty
   no_pop_request_while_empty: assert property (!pop_wishbone_request ##1 pop_wishbone_request |-> !$past(empty));

   fails: assert property (!empty throughout pop_wishbone_request); 
   
   // Check that nothing is sent while the buffer is empty (transaction
   // ends with pop on ack -- buffer becomes empty on the same cycle that
   // stb and cyc fall)
   //no_send_while_empty: assert property (empty |-> (!wb_o.cyc_o && !wb_o.stb_o));

   sequence badness;
      empty && wb_o.cyc_o && wb_o.stb_o;
   endsequence
   
   this_passes: cover property (badness);
   but_this_fails: cover property (!wb_o.cyc_o ##[1:$] badness);
   // test3: cover property (1 ##1 (empty && $rose(wb_o.cyc_o && wb_o.stb_o)));
   
`endif
   
endmodule

module fifo_formal(input logic clk_i, rst_i);

   wishbone_classic wb_i(.clk_i, .rst_i);
   wishbone_classic wb_o(.clk_i, .rst_i);

   wishbone_classic_fake_ctrl ctrl(.wb(wb_i));
   wishbone_classic_fake_dev dev(.wb(wb_o));

   fifo dut(.wb_i, .wb_o);
   
endmodule
