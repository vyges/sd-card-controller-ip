# tb/Makefile - SD Card Controller testbench simulation with multiple simulator support

# Simulator choice (iverilog, vlog, vcs, verilator, cocotb)
# How to run:
# make SIM=iverilog run
# make SIM=vcs run
# make SIM=vlog run (for Questa/ModelSim)
# make SIM=verilator run
# make SIM=cocotb run

SIM ?= iverilog
SIM_OPTS ?= -g2012

# Top-level testbench module (for HDL simulators)
TOPLEVEL ?= sd_card_controller_tb

# Verilator top-level C++ sim file name
VERILATOR_TOP_CPP ?= Vsd_card_controller_tb.cpp

# SD Card Controller RTL source files
RTL_SRCS = \
  ../rtl/sd_card_controller.sv \
  ../rtl/sd_apb_interface.sv \
  ../rtl/sd_register_file.sv \
  ../rtl/sd_command_engine.sv \
  ../rtl/sd_data_engine.sv \
  ../rtl/sd_clock_generator.sv \
  ../rtl/sd_dma_controller.sv \
  ../rtl/sd_power_controller.sv \
  ../rtl/sd_security_controller.sv \
  ../rtl/sd_debug_controller.sv \
  ../rtl/sd_test_controller.sv \
  ../rtl/sd_error_controller.sv \
  ../rtl/sd_performance_controller.sv \
  ../rtl/sd_calibration_controller.sv \
  ../rtl/sd_interrupt_controller.sv \
  ../rtl/sd_interface.sv

# SystemVerilog testbench source files
SV_TB_SRCS = \
  ./sv_tb/sd_card_controller_tb.sv \
  ./sv_tb/tb_sd_apb_interface.sv \
  ./sv_tb/tb_sd_register_file.sv \
  ./sv_tb/tb_sd_command_engine.sv \
  ./sv_tb/tb_sd_data_engine.sv \
  ./sv_tb/tb_sd_clock_generator.sv \
  ./sv_tb/tb_sd_dma_controller.sv \
  ./sv_tb/tb_sd_power_controller.sv \
  ./sv_tb/tb_sd_security_controller.sv \
  ./sv_tb/tb_sd_debug_controller.sv \
  ./sv_tb/tb_sd_test_controller.sv \
  ./sv_tb/tb_sd_error_controller.sv \
  ./sv_tb/tb_sd_performance_controller.sv \
  ./sv_tb/tb_sd_calibration_controller.sv \
  ./sv_tb/tb_sd_interrupt_controller.sv \
  ./sv_tb/tb_sd_interface.sv

# Cocotb test files
COCOTB_TESTS = \
  ./cocotb/test_sd_card_controller.py \
  ./cocotb/test_sd_apb_interface.py \
  ./cocotb/test_sd_register_file.py \
  ./cocotb/test_sd_command_engine.py \
  ./cocotb/test_sd_data_engine.py \
  ./cocotb/test_sd_clock_generator.py \
  ./cocotb/test_sd_dma_controller.py \
  ./cocotb/test_sd_power_controller.py \
  ./cocotb/test_sd_security_controller.py \
  ./cocotb/test_sd_debug_controller.py \
  ./cocotb/test_sd_test_controller.py \
  ./cocotb/test_sd_error_controller.py \
  ./cocotb/test_sd_performance_controller.py \
  ./cocotb/test_sd_calibration_controller.py \
  ./cocotb/test_sd_interrupt_controller.py \
  ./cocotb/test_sd_interface.py

# All source files for HDL simulators
SRCS = $(RTL_SRCS) $(SV_TB_SRCS)

# Verilator options
VERILATOR_OPTS = --cc --exe --build --trace --top-module $(TOPLEVEL)

# Output files
SIM_EXEC = simv.out
VERILATOR_EXEC = obj_dir/V$(TOPLEVEL)

# Cocotb configuration
export COCOTB_REDUCED_LOG_FMT=1
export PYTHONPATH := $(PWD)/cocotb:$(PYTHONPATH)
export TOPLEVEL_LANG = verilog
export TOPLEVEL = sd_card_controller

# Compilation commands by simulator
ifeq ($(SIM), iverilog)
  COMPILE = iverilog $(SIM_OPTS) -o $(SIM_EXEC) $(SRCS)
  RUN = vvp $(SIM_EXEC)
endif

ifeq ($(SIM), vlog)  # Questa/ModelSim
  COMPILE = vlog -sv $(SRCS)
  RUN = vsim -c -do "run -all; exit" $(TOPLEVEL)
endif

ifeq ($(SIM), vcs)
  COMPILE = vcs -full64 -sverilog $(SRCS) -o $(SIM_EXEC)
  RUN = ./$(SIM_EXEC)
endif

ifeq ($(SIM), verilator)
  COMPILE = verilator $(VERILATOR_OPTS) $(SRCS)
  RUN = ./$(VERILATOR_EXEC)
endif

ifeq ($(SIM), cocotb)
  COMPILE = echo "Cocotb compilation handled by Python"
  RUN = python3 -m pytest $(COCOTB_TESTS) -v
endif

.PHONY: all clean run test lint coverage

all: $(SIM_EXEC)

$(SIM_EXEC):
ifeq ($(SIM), verilator)
	@echo "Running Verilator to build C++ sim..."
	$(COMPILE)
else ifeq ($(SIM), cocotb)
	@echo "Cocotb simulation - no compilation needed"
else
	@echo "Compiling with $(SIM)..."
	$(COMPILE)
endif

run: all
	@echo "Running simulation with $(SIM)..."
	$(RUN)

test: run
	@echo "Running all tests..."

lint:
	@echo "Running linting checks..."
	@echo "TODO: Add linting tools (Verilator, SpyGlass, etc.)"

coverage:
	@echo "Running coverage analysis..."
	@echo "TODO: Add coverage tools (Verilator coverage, Questa coverage, etc.)"

clean:
	@echo "Cleaning simulation artifacts..."
	rm -rf $(SIM_EXEC) obj_dir coverage csrc *.log *.vpd *.wlf *.key ucli.key
	rm -rf __pycache__ *.pyc .pytest_cache
	rm -rf results.xml

