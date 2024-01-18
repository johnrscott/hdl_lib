/// Maintain a 10-bit shift register, which stores the data to be
/// transmitted (one start bit, 8 data bits, 1 stop bit).
///
/// The output tx is tied to the least significant bit of the
/// shift register. When shift is high, the register is arithmetic
/// right-shifted by one. Eventually, the all-one state is reached
/// and the output tx is constant one.
///
/// On reset (sync. active high), the internal shift register
/// is reset to all-ones.
///
/// On data, the shift register is set to { 1'b1, data, 1'b0 }.
/// Note this has the effect of asserting the start bit (tx drops
/// to zero).
///
/// If both load and shift are asseerted, shift is ignored and data
/// is loaded.
module tx_shift_reg(
   input logic clk, rst, load, shift,
   input logic [7:0] data,
   output tx
);

   logic [9:0] shift_reg = '1;

   assign tx = shift_reg[0];
   
   always_ff @(posedge clk) begin: reset_load_or_shift
      if (rst)
	shift_reg <= '1;
      else if (load)
	shift_reg <= { 1'b1, data, 1'b0 }; // Asserts start bit 
      else if (shift)
	shift_reg <= { 1'b1, shift_reg[9:1] };
   end
   
endmodule
