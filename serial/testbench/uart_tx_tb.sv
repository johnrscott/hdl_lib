module uart_tx_tb;

   timeunit 1ns;
   timeprecision 10ps;

   logic	     clk, rst, send, busy, tx;
   logic [7:0]	     data;

   parameter	     CLOCK_RATE = 10;
   parameter	     BAUD_RATE = 1;
   parameter	     CLOCKS_PER_BIT = CLOCK_RATE/BAUD_RATE;
   
   uart_tx #(.CLOCKS_PER_BIT(CLOCKS_PER_BIT)) dut(.*);
   
   always begin
      #1 clk = 1;
      #1 clk = 0;
   end

   initial begin
      wait (busy == 1);
      wait (busy == 0);

      #10;

      $finish;
   end
   
   /*
   default clocking cb @(posedge clk);
      default input #2 output #1;
      input busy, tx;
      output clk, rst, send;
   endclocking
    */
   initial begin

      $dumpfile("build/wave.vcd");
      $dumpvars;

      send = 0;
      rst = 1;

      #2;

      rst = 0;

      #2;

      data = "U";

      #4;
      send = 1;
      #2;
      send = 0;

   end // initial begin

   
endmodule
