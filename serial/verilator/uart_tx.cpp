#include <iostream>
#include "Vuart_tx.h"
#include <verilated.h>
#include <verilated_vcd_c.h>

namespace util {

    class clock {
    public:

	/// Make a new clock object associated
	/// to a top model and optionally a trace
	/// object.
	clock(Vuart_tx *tb,
	      VerilatedVcdC *tfp)
	    : tb_{tb}, tfp_{tfp} {}

    
	/// Advance the clock by a single tick
	///
	/// Calling this function does three things:
	///
	/// 1. Evaluates the model based on inputs that
	/// have been set since last calling tick(). These
	/// are assumed to be driven from the same clocking
	/// domain as this clock, so they should change just
	/// after the last rising edge of the clock. The
	/// delay is the hold time. Write to the trace file.
	///
	/// 2. After half a clock period, set the falling
	/// edge of the clock and write to the trace file.
	///
	/// 3. After another half clock period, set the rising
	/// edge of the clock, and evaluate. Write the results
	/// to the trace file. Since both the rising clock edge
	/// and all dependent logic are evaluated at the same
	/// time (and written to the trace file under the same
	/// timestamp), this models the logic as having zero
	/// propagation delay.
	///
	void tick() {

	    // Assume the user set inputs outside. Evaluate
	    // the model based on these inputs, and write the
	    // results to the trace file a hold time after the
	    // previous rising clock edge (at the end of this
	    // tick function).
	    tb_->eval();
	    if (tfp_) {
		tfp_->dump(10*tick_ + hold_);
	    }	    

	    // Now set clock falling edge + eval + write
	    // falling edge to trace
	    tb_->clk = 0;
	    tb_->eval();
	    if (tfp_) {
		tfp_->dump(10*tick_ + 5);
	    }	    

	    // Rising edge + eval. All signals depending on
	    // posedge update. Write all signals to trace at
	    // same time (acts like logic has zero propagation
	    // delay).
	    tb_->clk = 1;
	    tb_->eval();
	    if (tfp_) {
		tfp_->dump(10*tick_ + 10);
		tfp_->flush();
	    }

	    tick_++;
	}
    private:
	Vuart_tx *tb_;
	VerilatedVcdC *tfp_;
	unsigned tick_{0};
	unsigned hold_{1};
    };
}

int main(int argc , char **argv) {


    Verilated::commandArgs(argc, argv);
    Vuart_tx *tb{new Vuart_tx{}};

    // Trace output
    Verilated::traceEverOn(true);
    VerilatedVcdC *tfp{new VerilatedVcdC{}};
    tb->trace(tfp, 99);
    tfp->open("build/vl_uart_tx.vcd");

    util::clock clk{tb, tfp};

    // Perform two writes
    for (int cycle = 0; cycle < 2; cycle++) {

	// Delay 5 cycles
	for (int k = 0; k < 10; k++) {
	    clk.tick();
	}

	// Something
    }    

    // Delay 100 cycles
    for (int k = 0; k < 100; k++) {
	clk.tick();
    }
    
    
    
}
