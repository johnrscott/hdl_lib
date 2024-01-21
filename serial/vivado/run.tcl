create_project -in_memory -part xc7a35ticsg324-1L

read_verilog -sv [ glob ../src/*.sv ]
read_verilog hello_world_wrapper.v
read_xdc constraints.xdc
read_ip ./.srcs/sources_1/ip/clk_wiz_0/clk_wiz_0.xci

generate_target all [get_ips]

