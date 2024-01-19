#ifndef TOP_HPP
#define TOP

#include <verilated.h>
#include <verilated_vcd_c.h>

template<typename Top>
class Clock {
public:
    
    /// Make a new clock object associated
    /// to a top model
    Clock(Top &top, const std::string &vcd_path) : top_{top} {
	Verilated::traceEverOn(true);
	tfp_ = new VerilatedVcdC{};

	// Trace output
	top_.mod->trace(tfp_, 99);
	tfp_->open(vcd_path.c_str());
    }

    ~Clock() {
	if (tfp_) {
	    delete tfp_;
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
	top_.mod->eval();
	if (tfp_) {
	    tfp_->dump(10*tick_ + hold_);
	}	    

	// Now set clock falling edge + eval + write
	// falling edge to trace
	top_.set_clock(0);
	top_.mod->eval();
	if (tfp_) {
	    tfp_->dump(10*tick_ + 5);
	}	    

	// Rising edge + eval. All signals depending on
	// posedge update. Write all signals to trace at
	// same time (acts like logic has zero propagation
	// delay).
	top_.set_clock(1);
	top_.mod->eval();
	if (tfp_) {
	    tfp_->dump(10*tick_ + 10);
	    tfp_->flush();
	}

	tick_++;

	tick_count_++;
    }

    /// Total number of clock cycles elapsed
    unsigned tick_count() const {
	return tick_count_;
    }
    
private:
    Top &top_;
    VerilatedVcdC *tfp_{nullptr};
    unsigned tick_{0};
    unsigned hold_{1};
    unsigned tick_count_{0};
};


#endif
