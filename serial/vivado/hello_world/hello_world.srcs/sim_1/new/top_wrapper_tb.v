module top_wrapper_tb;

   timeunit 1ns;
   timeprecision 100ps;

   logic	     busy,clk,rst,trigger,tx,tx_debug;
   
   parameter	     CLOCK_RATE = 100_000_000;
   parameter	     BAUD_RATE = 115_200;
   parameter	     CLOCKS_PER_BIT = CLOCK_RATE/BAUD_RATE;
   
   top_wrapper dut(.*);
   
   always begin
      #5 clk = 1;
      #5 clk = 0;
   end
   /*
   initial begin
      wait (busy == 1);
      wait (busy == 0);
      
      #100;
      
      $finish;
   end
    */
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

      #800;

      trigger = 0;
      rst = 1;

      #40;

      rst = 0;

      #40;
      trigger = 1;
      #20;
      trigger = 0;

      #50;
      wait (busy == 0);

      #40;
      trigger = 1;
      #20;
      trigger = 0; 

   end // initial begin

   
endmodule
