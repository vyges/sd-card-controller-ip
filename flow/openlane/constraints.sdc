# SD Card Controller Timing Constraints
# Generated for OpenLane ASIC flow
# Author: Vyges AI
# Date: 2025

# Clock definitions
create_clock -name clk_i -period 10.0 -waveform {0 5} [get_ports clk_i]

# Clock uncertainty
set_clock_uncertainty 0.25 clk_i

# Clock transition
set_clock_transition 0.15 clk_i

# Input delays
set_input_delay -clock clk_i -max 2.0 [get_ports reset_n_i]
set_input_delay -clock clk_i -max 2.0 [get_ports psel_i]
set_input_delay -clock clk_i -max 2.0 [get_ports penable_i]
set_input_delay -clock clk_i -max 2.0 [get_ports pwrite_i]
set_input_delay -clock clk_i -max 2.0 [get_ports paddr_i[*]]
set_input_delay -clock clk_i -max 2.0 [get_ports pwdata_i[*]]
set_input_delay -clock clk_i -max 2.0 [get_ports sd_cd_i]
set_input_delay -clock clk_i -max 2.0 [get_ports sd_wp_i]
set_input_delay -clock clk_i -max 2.0 [get_ports test_mode_i]
set_input_delay -clock clk_i -max 2.0 [get_ports test_clk_i]
set_input_delay -clock clk_i -max 2.0 [get_ports test_data_i[*]]
set_input_delay -clock clk_i -max 2.0 [get_ports test_valid_i]

# Output delays
set_output_delay -clock clk_i -max 8.0 [get_ports prdata_o[*]]
set_output_delay -clock clk_i -max 8.0 [get_ports pready_o]
set_output_delay -clock clk_i -max 8.0 [get_ports pslverr_o]
set_output_delay -clock clk_i -max 8.0 [get_ports irq_o]
set_output_delay -clock clk_i -max 8.0 [get_ports debug_clk_o]
set_output_delay -clock clk_i -max 8.0 [get_ports debug_data_o[*]]
set_output_delay -clock clk_i -max 8.0 [get_ports debug_valid_o]

# Bidirectional ports (SD card interface)
set_input_delay -clock clk_i -max 2.0 [get_ports sd_cmd_io]
set_input_delay -clock clk_i -max 2.0 [get_ports sd_data_io[*]]
set_output_delay -clock clk_i -max 8.0 [get_ports sd_cmd_io]
set_output_delay -clock clk_i -max 8.0 [get_ports sd_data_io[*]]
set_output_delay -clock clk_i -max 8.0 [get_ports sd_clk_o]

# False paths
set_false_path -from [get_ports reset_n_i]
set_false_path -from [get_ports test_mode_i]
set_false_path -from [get_ports test_clk_i]
set_false_path -from [get_ports test_data_i[*]]
set_false_path -from [get_ports test_valid_i]

# Multicycle paths
set_multicycle_path -setup 2 -from clk_i -to clk_i
set_multicycle_path -hold 1 -from clk_i -to clk_i

# Load constraints
set_load 17.65 [all_outputs]

# Driving cell constraints
set_driving_cell -lib_cell sky130_fd_sc_hd__inv_8 [all_inputs]

# Area constraints
set_max_area 0

# Power constraints
set_max_dynamic_power 50mW
set_max_leakage_power 5mW

# Operating conditions
set_operating_conditions -library sky130_fd_sc_hd__tt_025C_1v80

# Wire load model
set_wire_load_model -name "sky130_1p8v_typical"

# Timing derating
set_timing_derate -early 0.95
set_timing_derate -late 1.05 