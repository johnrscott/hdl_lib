# Contains three targets:
#
# iv_wave:
# Runs a testbench file through iverilog and
# opens the resulting waves in gtkwave. Assumes
# the testbench and all the required modules are
# in *.sv files in this folder. Results placed in
# build/
#
# vl_wave:
# Compiles and runs a verilator simulation and
# opens the resulting waves in gtkwave.

VERILATOR_INC=/usr/share/verilator/include/
IFLAGS=-Iobj_dir/ -I$(VERILATOR_INC)
TOP=uart_tx
TOP_TB=hello_world_tb

CLOCKS_PER_BIT=5

# Display iverilog waves
.PHONY: iv_wave
iv_wave: run
	gtkwave build/$(TOP_TB)_wave.vcd

# Display verilator waves
.PHONY: vl_wave
vl_wave: build/$(TOP).bin
	./$^
	gtkwave build/vl_$(TOP).vcd

build/$(TOP).bin: verilator/*.cpp obj_dir/V$(TOP)__ALL.a
	g++ -O2 $^ $(VERILATOR_INC)/verilated.cpp \
		-DCLOCKS_PER_BIT=$(CLOCKS_PER_BIT) \
		$(VERILATOR_INC)/verilated_vcd_c.cpp $(IFLAGS) -o $@

obj_dir/V$(TOP)__ALL.a: src/*.sv
	verilator -Wall -cc --trace --top-module $(TOP) \
		-GCLOCKS_PER_BIT=$(CLOCKS_PER_BIT) $^
	make -C obj_dir -f V$(TOP).mk

.PHONY: run
run: build/tb
	./build/tb

build/tb: src/*.sv testbench/*.sv
	mkdir -p build
	iverilog -g2005-sv -s$(TOP_TB) $^ -o $@

.PHONY: clean
clean:
	rm -rf build/ obj_dir/
