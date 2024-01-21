set output_dir ./output
file mkdir $output_dir

create_project -in_memory -part xc7a35ticsg324-1L

read_verilog -sv [ glob ../src/*.sv ]
read_verilog hello_world_wrapper.v
read_xdc constraints.xdc

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

synth_design -top hello_world_wrapper

opt_design
place_design
phys_opt_design
route_design

write_bitstream -force $output_dir/bitstream.bit

# Connect to the Digilent Cable on localhost:3121
open_hw_manager
connect_hw_server -url localhost:3121
current_hw_target [get_hw_targets */xilinx_tcf/Digilent/210319B0C665A]
open_hw_target

# Program and Refresh the XC7K325T Device
set device [lindex [get_hw_devices] 0]
current_hw_device $device
refresh_hw_device -update_hw_probes false $device
set_property PROGRAM.FILE $output_dir/bitstream.bit $device

program_hw_devices $device
refresh_hw_device $device
