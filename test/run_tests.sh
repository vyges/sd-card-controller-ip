#!/bin/bash

# SD Card Controller IP Test Suite
# Author: Vyges AI
# Date: 2025

set -e

# Colors for output
RED='\033[0;31m'
GREEN='\033[0;32m'
YELLOW='\033[1;33m'
BLUE='\033[0;34m'
NC='\033[0m' # No Color

# Test configuration
SIMULATORS=("iverilog" "verilator" "cocotb")
RTL_DIR="rtl"
TB_DIR="tb"
FLOW_DIR="flow"
DOCS_DIR="docs"

# Test counters
TOTAL_TESTS=0
PASSED_TESTS=0
FAILED_TESTS=0

# Function to print colored output
print_status() {
    local status=$1
    local message=$2
    case $status in
        "PASS")
            echo -e "${GREEN}[PASS]${NC} $message"
            ;;
        "FAIL")
            echo -e "${RED}[FAIL]${NC} $message"
            ;;
        "INFO")
            echo -e "${BLUE}[INFO]${NC} $message"
            ;;
        "WARN")
            echo -e "${YELLOW}[WARN]${NC} $message"
            ;;
    esac
}

# Function to run a test
run_test() {
    local test_name=$1
    local test_command=$2
    local test_dir=$3
    
    TOTAL_TESTS=$((TOTAL_TESTS + 1))
    
    print_status "INFO" "Running $test_name..."
    
    if [ -n "$test_dir" ]; then
        cd "$test_dir"
    fi
    
    if eval "$test_command" > /dev/null 2>&1; then
        print_status "PASS" "$test_name completed successfully"
        PASSED_TESTS=$((PASSED_TESTS + 1))
    else
        print_status "FAIL" "$test_name failed"
        FAILED_TESTS=$((FAILED_TESTS + 1))
    fi
    
    if [ -n "$test_dir" ]; then
        cd - > /dev/null
    fi
}

# Function to check file existence
check_file() {
    local file=$1
    local description=$2
    
    TOTAL_TESTS=$((TOTAL_TESTS + 1))
    
    if [ -f "$file" ]; then
        print_status "PASS" "$description exists: $file"
        PASSED_TESTS=$((PASSED_TESTS + 1))
    else
        print_status "FAIL" "$description missing: $file"
        FAILED_TESTS=$((FAILED_TESTS + 1))
    fi
}

# Function to check directory structure
check_structure() {
    print_status "INFO" "Checking project structure..."
    
    # Check main directories
    check_file "$RTL_DIR/sd_card_controller.sv" "Top-level RTL module"
    check_file "$RTL_DIR/sd_apb_interface.sv" "APB interface module"
    check_file "$RTL_DIR/sd_register_file.sv" "Register file module"
    check_file "$RTL_DIR/sd_command_engine.sv" "Command engine module"
    check_file "$RTL_DIR/sd_data_engine.sv" "Data engine module"
    check_file "$RTL_DIR/sd_clock_generator.sv" "Clock generator module"
    check_file "$RTL_DIR/sd_dma_controller.sv" "DMA controller module"
    check_file "$RTL_DIR/sd_power_controller.sv" "Power controller module"
    check_file "$RTL_DIR/sd_security_controller.sv" "Security controller module"
    check_file "$RTL_DIR/sd_debug_controller.sv" "Debug controller module"
    check_file "$RTL_DIR/sd_test_controller.sv" "Test controller module"
    check_file "$RTL_DIR/sd_error_controller.sv" "Error controller module"
    check_file "$RTL_DIR/sd_performance_controller.sv" "Performance controller module"
    check_file "$RTL_DIR/sd_calibration_controller.sv" "Calibration controller module"
    check_file "$RTL_DIR/sd_interrupt_controller.sv" "Interrupt controller module"
    check_file "$RTL_DIR/sd_interface.sv" "Interface module"
    
    # Check testbench files
    check_file "$TB_DIR/sv_tb/sd_card_controller_tb.sv" "Top-level testbench"
    check_file "$TB_DIR/Makefile" "Testbench Makefile"
    
    # Check documentation
    check_file "$DOCS_DIR/sd_card_controller_design_spec.md" "Design specification"
    check_file "$DOCS_DIR/architecture.md" "Architecture document"
    check_file "$DOCS_DIR/overview.md" "Overview document"
    check_file "$DOCS_DIR/user_guide.md" "User guide"
    check_file "$DOCS_DIR/api_reference.md" "API reference"
    check_file "README.md" "README file"
    
    # Check flow files
    check_file "$FLOW_DIR/openlane/config.template.json" "OpenLane configuration"
    check_file "$FLOW_DIR/openlane/constraints.sdc" "Timing constraints"
}

# Function to run linting tests
run_linting() {
    print_status "INFO" "Running linting tests..."
    
    # Check if Verilator is available
    if command -v verilator >/dev/null 2>&1; then
        run_test "Verilator Linting" \
            "verilator --lint-only --top-module sd_card_controller \
            $RTL_DIR/sd_card_controller.sv \
            $RTL_DIR/sd_apb_interface.sv \
            $RTL_DIR/sd_register_file.sv \
            $RTL_DIR/sd_command_engine.sv \
            $RTL_DIR/sd_data_engine.sv \
            $RTL_DIR/sd_clock_generator.sv \
            $RTL_DIR/sd_dma_controller.sv \
            $RTL_DIR/sd_power_controller.sv \
            $RTL_DIR/sd_security_controller.sv \
            $RTL_DIR/sd_debug_controller.sv \
            $RTL_DIR/sd_test_controller.sv \
            $RTL_DIR/sd_error_controller.sv \
            $RTL_DIR/sd_performance_controller.sv \
            $RTL_DIR/sd_calibration_controller.sv \
            $RTL_DIR/sd_interrupt_controller.sv \
            $RTL_DIR/sd_interface.sv" \
            "$RTL_DIR"
    else
        print_status "WARN" "Verilator not found, skipping linting"
    fi
}

# Function to run simulation tests
run_simulation() {
    print_status "INFO" "Running simulation tests..."
    
    for simulator in "${SIMULATORS[@]}"; do
        if command -v "$simulator" >/dev/null 2>&1 || [ "$simulator" = "cocotb" ]; then
            run_test "$simulator Simulation" "make SIM=$simulator run" "$TB_DIR"
        else
            print_status "WARN" "$simulator not found, skipping simulation"
        fi
    done
}

# Function to run synthesis tests
run_synthesis() {
    print_status "INFO" "Running synthesis tests..."
    
    if command -v yosys >/dev/null 2>&1; then
        run_test "Yosys Synthesis" \
            "yosys -p 'synth_sky130 -top sd_card_controller -json sd_card_controller.json' \
            ../$RTL_DIR/sd_card_controller.sv \
            ../$RTL_DIR/sd_apb_interface.sv \
            ../$RTL_DIR/sd_register_file.sv \
            ../$RTL_DIR/sd_command_engine.sv \
            ../$RTL_DIR/sd_data_engine.sv \
            ../$RTL_DIR/sd_clock_generator.sv \
            ../$RTL_DIR/sd_dma_controller.sv \
            ../$RTL_DIR/sd_power_controller.sv \
            ../$RTL_DIR/sd_security_controller.sv \
            ../$RTL_DIR/sd_debug_controller.sv \
            ../$RTL_DIR/sd_test_controller.sv \
            ../$RTL_DIR/sd_error_controller.sv \
            ../$RTL_DIR/sd_performance_controller.sv \
            ../$RTL_DIR/sd_calibration_controller.sv \
            ../$RTL_DIR/sd_interrupt_controller.sv \
            ../$RTL_DIR/sd_interface.sv" \
            "$FLOW_DIR/openlane"
    else
        print_status "WARN" "Yosys not found, skipping synthesis"
    fi
}

# Function to check code quality
check_code_quality() {
    print_status "INFO" "Checking code quality..."
    
    # Check for TODO comments in RTL
    local todo_count=$(grep -r "TODO" "$RTL_DIR" | wc -l)
    if [ "$todo_count" -eq 0 ]; then
        print_status "PASS" "No TODO comments found in RTL"
        PASSED_TESTS=$((PASSED_TESTS + 1))
    else
        print_status "WARN" "Found $todo_count TODO comments in RTL"
        PASSED_TESTS=$((PASSED_TESTS + 1))
    fi
    TOTAL_TESTS=$((TOTAL_TESTS + 1))
    
    # Check for proper module headers
    local header_count=$(grep -r "Description:" "$RTL_DIR" | wc -l)
    local module_count=$(find "$RTL_DIR" -name "*.sv" | wc -l)
    if [ "$header_count" -eq "$module_count" ]; then
        print_status "PASS" "All RTL modules have proper headers"
        PASSED_TESTS=$((PASSED_TESTS + 1))
    else
        print_status "FAIL" "Some RTL modules missing headers"
        FAILED_TESTS=$((FAILED_TESTS + 1))
    fi
    TOTAL_TESTS=$((TOTAL_TESTS + 1))
}

# Function to print test summary
print_summary() {
    echo
    echo "=========================================="
    echo "           TEST SUMMARY"
    echo "=========================================="
    echo "Total Tests: $TOTAL_TESTS"
    echo -e "Passed: ${GREEN}$PASSED_TESTS${NC}"
    echo -e "Failed: ${RED}$FAILED_TESTS${NC}"
    
    if [ "$FAILED_TESTS" -eq 0 ]; then
        echo -e "${GREEN}All tests passed!${NC}"
        exit 0
    else
        echo -e "${RED}Some tests failed!${NC}"
        exit 1
    fi
}

# Main test execution
main() {
    echo "=========================================="
    echo "    SD Card Controller IP Test Suite"
    echo "=========================================="
    echo
    
    check_structure
    run_linting
    run_simulation
    run_synthesis
    check_code_quality
    
    print_summary
}

# Run main function
main "$@" 