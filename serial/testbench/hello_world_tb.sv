module hello_world_tb;

   timeunit 1ns;
   timeprecision 10ps;

   logic	     clk, rst, trigger, busy, tx;
   logic [7:0]	     data;
   
   parameter	     CLOCK_RATE = 10;
   parameter	     BAUD_RATE = 1;
   parameter	     CLOCKS_PER_BIT = CLOCK_RATE/BAUD_RATE;
   
   hello_world dut(.*);
   
   always begin
      #1 clk = 1;
      #1 clk = 0;
   end
   
   initial begin
      wait (busy == 1);
      wait (busy == 0);
      
      #100;
      
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

      $dumpfile("build/hello_world_tb_wave.vcd");
      $dumpvars;

      trigger = 0;
      rst = 1;

      #4;

      rst = 0;

      #4;
      trigger = 1;
      #2;
      trigger = 0;

   end // initial begin

   
endmodule
