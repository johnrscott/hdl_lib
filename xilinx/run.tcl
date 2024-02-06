create_project -in_memory -part xc7a35ticsg324-1L

# Set the name of the example to build (this is the folder name in
# examples/)
set example buttons_to_leds

# Set the name of the board. This will pick out a *.xdc file with the
# same name (currently only Arty A7 has been added, but similar boards
# would work too if the port mapping constraints were modified).
set board_name arty_a7

# Read the example to synthesize/program
read_verilog -sv [ glob ../../examples/$example/src/*.sv ]

# Read the library (reads all the modules from all the components,
# even if some are unused)
read_verilog -sv [ glob ../../lib/*/src/*.sv ]

# Read the generic top wrapper and Arty A7 constraints
read_verilog -sv ../top.sv
read_xdc ../arty_a7.xdc

# Copied from Vivado
# set_property board_part digilentinc.com:arty-a7-35:part0:1.1

# THIS: clock 100MHz without reset
create_ip -name clk_wiz -vendor xilinx.com -library ip -version 6.0 -module_name clk_wiz_0
set_property CONFIG.USE_RESET {false} [get_ips clk_wiz_0]

# OR...
read_ip ./.srcs/sources_1/ip/clk_wiz_0/clk_wiz_0.xci

# Seems like this also generates instantiation template
generate_target all [get_ips]

# Will generate output products if needed. This is crucial --
# If you skip this step, Vivado will give module-not-found errors
# when attempting to synthesize the user RTL design and IP instantiation
# templates are used in the RTL.
synth_ip [get_ips]

# Copied from Vivado (does not seem to fix issue)
export_ip_user_files -of_objects [get_ips] -no_script -sync -force -quiet

# To elaborate design
synth_design -rtl -top top -verilog_define MOD=$example
start_gui
show_schematic [get_nets]

synth_design -top top -verilog_define MOD=$example

opt_design
place_design
phys_opt_design
route_design

write_bitstream -force bitstream.bit

# Connect to the Digilent Cable on localhost:3121
open_hw_manager
connect_hw_server -url localhost:3121
current_hw_target [get_hw_targets */xilinx_tcf/Digilent/210319B0C665A]
open_hw_target

# Program and Refresh the XC7K325T Device
set device [lindex [get_hw_devices] 0]
current_hw_device $device
refresh_hw_device -update_hw_probes false $device
set_property PROGRAM.FILE bitstream.bit $device

program_hw_devices $device
refresh_hw_device $device
