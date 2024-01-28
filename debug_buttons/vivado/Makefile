# Add -mode batch if you want Vivado to exit after running the
# command
run:
	mkdir -p build
	cd build/; vivado -mode tcl -script ../run.tcl

.PHONY: clean
clean:
	rm -rf build/
