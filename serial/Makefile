# Runs a testbench file through iverilog and
# opens the resulting waves in gtkwave. Assumes
# the testbench and all the required modules are
# in *.sv files in this folder. Results placed in
# build/

.PHONY: display
display: run
	gtkwave build/wave.vcd

.PHONY: run
run: build/tb
	./build/tb

build/tb: *.sv
	mkdir -p build
	iverilog -g2005-sv $^ -o $@

.PHONY: clean
clean:
	rm -rf build
