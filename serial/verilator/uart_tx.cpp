#include <iostream>
#include "Vuart_tx.h"
#include <verilated.h>
#include <verilated_vcd_c.h>

/// Based on top module Top, which needs a
/// ->clk() method to abstract whatever signal
/// is being used as the clock.
class uart_tx {
public:

    /// Wrap the module port to use as the clock
    void set_clock(int value) {
	tb_->clk = value;
    }

    /// Provide access to all module ports
    Vuart_tx* operator->() {
	return tb_;
    }
       	
    /// Make a new clock object associated
    /// to a top model
    uart_tx() : tb_{new Vuart_tx{}} {
	Verilated::traceEverOn(true);
	tfp_ = new VerilatedVcdC{};

	// Trace output
	tb_->trace(tfp_, 99);
	tfp_->open("build/vl_uart_tx.vcd");
    }

    ~uart_tx() {
	if (tfp_) {
	    delete tfp_;
	}

	if (tb_) {
	    delete tb_;
	}
    }
	
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
	set_clock(0);
	tb_->eval();
	if (tfp_) {
	    tfp_->dump(10*tick_ + 5);
	}	    

	// Rising edge + eval. All signals depending on
	// posedge update. Write all signals to trace at
	// same time (acts like logic has zero propagation
	// delay).
	set_clock(1);
	tb_->eval();
	if (tfp_) {
	    tfp_->dump(10*tick_ + 10);
	    tfp_->flush();
	}

	tick_++;
    }
private:
    Vuart_tx *tb_{nullptr};
    VerilatedVcdC *tfp_{nullptr};
    unsigned tick_{0};
    unsigned hold_{1};
};

int main(int argc , char **argv) {

    Verilated::commandArgs(argc, argv);

    uart_tx dut{};
    
    // Perform two writes
    for (int cycle = 0; cycle < 2; cycle++) {

	// Delay 5 cycles
	for (int k = 0; k < 10; k++) {
	    dut.tick();
	}

	// Something
    }    

    // Delay 100 cycles
    for (int k = 0; k < 100; k++) {
	dut.tick();
    }
    
    
    
}
