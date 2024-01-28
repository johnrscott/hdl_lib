#include <iostream>
#include <string>

#include "Vuart_tx.h"
#include "top.hpp"

template<typename Mod>
class Top {
public:
    /// Access module ports through this member
    Mod *mod{nullptr};

    Top() : mod{new Mod{}} {}
    ~Top() {
	if (mod) {
	    delete mod;
	}
    }
    
};

class UartTx: public Top<Vuart_tx> {
public:

    /// Implement this virtual function to
    /// pick which port is the clock for tick()
    void set_clock(int value) {
	mod->clk = value;
    }

    UartTx() {}
};

/// Read the ports and check the state
class UartRxSim {
public:

    enum class State {
	IDLE,
	START,
	RECEIVING,
	STOP
    };
    
    UartRxSim(UartTx &uart_tx)
	: dut_{uart_tx}, clock_{uart_tx, "build/vl_uart_tx.vcd"} {}

    std::string rx_string() const {
	return rx_string_;
    }
    
    /// Update the clock and refresh the simulation
    void tick() {
	clock_.tick();

	std::cout << "Starting tick" << clock_.tick_count() << std::endl;
	
	// Now read the outputs
	switch (state_) {
	case State::IDLE:
	    if (dut_.mod->tx == 0) {
		reference_tick_ = clock_.tick_count();
		state_ = State::START;
		std::cout << "Detected possible start bit" << std::endl;
	    }
	    break;
	case State::START:
	    if (dut_.mod->tx == 1) {
		std::cout << "Aborted start bit" << std::endl;
		state_ = State::IDLE;
	    }
	    if (clock_.tick_count() == reference_tick_ + CLOCKS_PER_BIT/2) {
		std::cout << "Confirmed start bit" << std::endl;
		rx_data_ = 0;
		reference_tick_ = clock_.tick_count();
		bit_count_ = 0;
		state_ = State::RECEIVING;
	    }
	    break;
	case State::RECEIVING:
	    if (clock_.tick_count() == reference_tick_ + CLOCKS_PER_BIT) {
		reference_tick_ = clock_.tick_count();
		unsigned bit{dut_.mod->tx};
                rx_data_ |= (bit << bit_count_);
		std::cout << "Sampling tx data, got " << bit << std::endl;
		if (++bit_count_ == 8) {
		    std::cout << "Finished final bit. Going to stop bit."
			      << std::endl;
		    state_ = State::STOP;
		}
	    }
	    break;
	case State::STOP:
	    if (clock_.tick_count() == reference_tick_ + CLOCKS_PER_BIT) {
		unsigned bit{dut_.mod->tx};
		if (bit != 1) {
		    std::cout << "Error, stop bit has wrong value" << std::endl;
		} else {
		    std::cout << "Got correct stop bit" << std::endl;
		    std::cout << "Received character was: " << (char)rx_data_
			      << std::endl;
		    rx_string_.push_back((char)rx_data_);
		}
		state_ = State::IDLE;
	    }
	    break;
	}
    }
	  
private:
    UartTx &dut_;
    Clock<UartTx> clock_;
    unsigned reference_tick_;
    unsigned bit_count_;
    uint8_t rx_data_;
    std::string rx_string_;
    State state_;
};

int main(int argc , char **argv) {

    Verilated::commandArgs(argc, argv);

    UartTx dut{};
    UartRxSim sim{dut};

    std::string message = "Hello, World!";

    // Start up simulation
    for (int n = 0; n < 10; n++) {
	sim.tick();
    }
    
    // Write each character in turn
    for (char ch : message) {

	// Trigger a transmission
	dut.mod->data = ch;
        dut.mod->send = 1;
       
	// Wait for transmission to start
	while (dut.mod->busy == 0) {
	    sim.tick();
	}	

	// Deassert send signal
	dut.mod->send = 0;
	
	// Wait for transmission to end
	while (dut.mod->busy == 1) {
	    sim.tick();
	}
	
    }
    
    // Delay 100 cycles
    for (int k = 0; k < 100; k++) {
	sim.tick();
    }

    // Print final string
    std::cout << "Received string: " << sim.rx_string() << std::endl;

    if (sim.rx_string() == message) {
	std::cout << "TEST PASSED" << std::endl;
    } else {
	std::cout << "TEST FAILED" << std::endl;
    }
}
