module uart_tx_tb;

   timeunit 1ns;
   timeprecision 10ps;

   logic	     clk, rst, send, busy, tx;
   logic [7:0]	     data;
   
   uart_tx dut(.*);
   
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
