## Script used to generate the clock IP
##
## This only needs to be run once -- the output .xci has been stored in
## .srcs/sources_1/ip/clk_wiz_0/clk_wiz_0.xci
create_ip -name clk_wiz -vendor xilinx.com -library ip -version 6.0 -module_name clk_wiz_0
set_property -dict [list \
			CONFIG.CLKOUT1_JITTER {193.154} \
			CONFIG.CLKOUT1_PHASE_ERROR {109.126} \
			CONFIG.CLKOUT1_REQUESTED_OUT_FREQ {20.000} \
			CONFIG.MMCM_CLKFBOUT_MULT_F {8.500} \
			CONFIG.MMCM_CLKOUT0_DIVIDE_F {42.500} \
		       ] [get_ips clk_wiz_0]
