//=============================================================================
// Module Name: sdcard_controller
//=============================================================================
// Description: High-performance SD Card controller with APB interface
//              supporting SD/SDHC/SDXC cards with comprehensive power management,
//              security features, debug capabilities, and DMA support
//
// Features:
// - SD/SDHC/SDXC card support (SPI and SD modes)
// - APB3 slave interface
// - DMA support for high-speed transfers
// - Power management with multiple power states
// - Security features (access control, tamper detection, secure boot)
// - Debug interface (JTAG, trace)
// - Comprehensive error handling and recovery
// - Performance monitoring and optimization
// - Built-in self-test and scan chain support
//
// Author: Vyges Development Team
// License: Apache-2.0
//=============================================================================

`define SDCARD_CONTROLLER_SV

module sdcard_controller #(
    parameter int SDCARD_APB_ADDR_WIDTH = 16,
    parameter int SDCARD_DATA_WIDTH = 4,
    parameter int SDCARD_FIFO_DEPTH = 512,
    parameter bit SDCARD_DMA_ENABLE = 1'b1,
    parameter bit SDCARD_SPI_MODE_ENABLE = 1'b1
) (
    // Clock and Reset
    input  logic                    PCLK_i,           // APB clock
    input  logic                    PRESETn_i,        // APB reset, active low
    
    // APB Slave Interface
    input  logic                    PSEL_i,           // APB select
    input  logic                    PENABLE_i,        // APB enable
    input  logic                    PWRITE_i,         // APB write enable
    input  logic [SDCARD_APB_ADDR_WIDTH-1:0] PADDR_i,        // APB address bus
    input  logic [31:0]            PWDATA_i,          // APB write data
    output logic [31:0]            PRDATA_o,          // APB read data
    output logic                   PREADY_o,          // APB ready
    output logic                   PSLVERR_o,         // APB slave error
    
    // SD Card Interface
    output logic                   sd_clk_o,          // SD card clock
    inout  logic                   sd_cmd_io,         // SD command line
    inout  logic [SDCARD_DATA_WIDTH-1:0] sd_dat_io,       // SD data lines
    input  logic                   sd_cd_i,           // Card detect
    input  logic                   sd_wp_i,           // Write protect
    output logic                   sd_pwr_en_o,       // SD card power enable
    output logic                   sd_vdd_sel_o,      // SD card voltage select
    
    // Interrupt Interface
    output logic                   sd_irq_o,          // SD card interrupt
    output logic                   dma_irq_o,         // DMA transfer complete interrupt
    output logic                   error_irq_o,       // Error condition interrupt
    output logic                   debug_irq_o,       // Debug event interrupt
    
    // DMA Interface (Optional)
    output logic                   dma_req_o,         // DMA request
    input  logic                   dma_ack_i,         // DMA acknowledge
    output logic [31:0]            dma_addr_o,        // DMA address
    output logic [15:0]            dma_len_o,         // DMA length
    output logic                   dma_we_o,          // DMA write enable
    output logic                   dma_burst_o,       // DMA burst mode
    output logic [3:0]             dma_cache_o,       // DMA cache attributes
    
    // Debug Interface
    input  logic                   jtag_tck_i,        // JTAG test clock
    input  logic                   jtag_tms_i,        // JTAG test mode select
    input  logic                   jtag_tdi_i,        // JTAG test data input
    output logic                   jtag_tdo_o,        // JTAG test data output
    input  logic                   jtag_trst_n_i,     // JTAG test reset
    output logic [7:0]             trace_data_o,      // Trace data output
    output logic                   trace_valid_o      // Trace data valid
);

    // Internal signals
    logic [31:0]                   reg_data_out;
    logic [31:0]                   reg_data_in;
    logic [15:0]                   reg_addr;
    logic                          reg_read;
    logic                          reg_write;
    logic                          reg_ready;
    logic                          reg_error;
    
    // Command engine signals
    logic [5:0]                    cmd_index;
    logic [31:0]                   cmd_argument;
    logic                          cmd_start;
    logic                          cmd_busy;
    logic                          cmd_done;
    logic [39:0]                   cmd_response;
    logic                          cmd_timeout;
    logic                          cmd_crc_error;
    
    // Data engine signals
    logic [31:0]                   data_in;
    logic [31:0]                   data_out;
    logic                          data_valid;
    logic                          data_ready;
    logic                          data_start;
    logic                          data_busy;
    logic                          data_done;
    logic [15:0]                   data_crc;
    logic                          data_crc_error;
    
    // Clock generator signals
    logic                          clk_enable;
    logic [15:0]                   clk_divider;
    logic                          clk_calibrated;
    
    // FIFO signals
    logic [31:0]                   fifo_data_in;
    logic [31:0]                   fifo_data_out;
    logic                          fifo_write;
    logic                          fifo_read;
    logic                          fifo_full;
    logic                          fifo_empty;
    logic [9:0]                    fifo_count;
    
    // DMA signals
    logic                          dma_enable;
    logic [31:0]                   dma_base_addr;
    logic [15:0]                   dma_length;
    logic                          dma_busy;
    logic                          dma_done;
    logic                          dma_error;
    
    // Power management signals
    logic [1:0]                    power_state;
    logic                          power_good;
    logic                          power_fault;
    logic [3:0]                    voltage_sel;
    
    // Security signals
    logic                          security_lock;
    logic                          access_granted;
    logic                          tamper_detected;
    logic                          secure_boot_done;
    
    // Debug signals
    logic                          debug_enable;
    logic [7:0]                    trace_data;
    logic                          trace_valid;
    logic                          jtag_enable;
    logic [31:0]                   debug_trace_data;
    
    // Error signals
    logic [15:0]                   error_status;
    logic                          error_clear;
    logic                          error_interrupt;
    
    // Performance signals
    logic [31:0]                   performance_counters;
    logic                          performance_overflow;
    
    // Calibration signals
    logic                          cal_start;
    logic                          cal_busy;
    logic                          cal_done;
    logic [15:0]                   cal_result;
    
    // Interrupt signals
    logic [3:0]                    interrupt_status;
    logic [3:0]                    interrupt_enable;
    logic [3:0]                    interrupt_pending;

    // APB Interface Module
    sdcard_apb_interface #(
        .SDCARD_APB_ADDR_WIDTH(SDCARD_APB_ADDR_WIDTH)
    ) apb_interface (
        .PCLK_i(PCLK_i),
        .PRESETn_i(PRESETn_i),
        .PSEL_i(PSEL_i),
        .PENABLE_i(PENABLE_i),
        .PWRITE_i(PWRITE_i),
        .PADDR_i(PADDR_i),
        .PWDATA_i(PWDATA_i),
        .PRDATA_o(PRDATA_o),
        .PREADY_o(PREADY_o),
        .PSLVERR_o(PSLVERR_o),
        .reg_data_out(reg_data_out),
        .reg_data_in(reg_data_in),
        .reg_addr(reg_addr),
        .reg_read(reg_read),
        .reg_write(reg_write),
        .reg_ready(reg_ready),
        .reg_error(reg_error)
    );

    // Register File Module
    sdcard_register_file register_file (
        .PCLK_i(PCLK_i),
        .PRESETn_i(PRESETn_i),
        .reg_data_out(reg_data_out),
        .reg_data_in(reg_data_in),
        .reg_addr(reg_addr),
        .reg_read(reg_read),
        .reg_write(reg_write),
        .reg_ready(reg_ready),
        .reg_error(reg_error),
        .cmd_index(cmd_index),
        .cmd_argument(cmd_argument),
        .cmd_start(cmd_start),
        .cmd_busy(cmd_busy),
        .cmd_done(cmd_done),
        .cmd_response(cmd_response),
        .cmd_timeout(cmd_timeout),
        .cmd_crc_error(cmd_crc_error),
        .data_in(data_in),
        .data_out(data_out),
        .data_valid(data_valid),
        .data_ready(data_ready),
        .data_start(data_start),
        .data_busy(data_busy),
        .data_done(data_done),
        .data_crc(data_crc),
        .data_crc_error(data_crc_error),
        .clk_enable(clk_enable),
        .clk_divider(clk_divider),
        .clk_calibrated(clk_calibrated),
        .fifo_data_in(fifo_data_in),
        .fifo_data_out(fifo_data_out),
        .fifo_write(fifo_write),
        .fifo_read(fifo_read),
        .fifo_full(fifo_full),
        .fifo_empty(fifo_empty),
        .fifo_count(fifo_count),
        .dma_enable(dma_enable),
        .dma_base_addr(dma_base_addr),
        .dma_length(dma_length),
        .dma_busy(dma_busy),
        .dma_done(dma_done),
        .dma_error(dma_error),
        .power_state(power_state),
        .power_good(power_good),
        .power_fault(power_fault),
        .voltage_sel(voltage_sel),
        .security_lock(security_lock),
        .access_granted(access_granted),
        .tamper_detected(tamper_detected),
        .secure_boot_done(secure_boot_done),
        .debug_enable(debug_enable),
        .trace_data(trace_data),
        .trace_valid(trace_valid),
        .jtag_enable(jtag_enable),
        .error_status(error_status),
        .error_clear(error_clear),
        .error_interrupt(error_interrupt),
        .performance_counters(performance_counters),
        .performance_overflow(performance_overflow),
        .cal_start(cal_start),
        .cal_busy(cal_busy),
        .cal_done(cal_done),
        .cal_result(cal_result),
        .interrupt_status(interrupt_status),
        .interrupt_enable(interrupt_enable),
        .interrupt_pending(interrupt_pending)
    );

    // Command Engine Module
    sdcard_command_engine command_engine (
        .PCLK_i(PCLK_i),
        .PRESETn_i(PRESETn_i),
        .sd_clk_o(sd_clk_o),
        .sd_cmd_io(sd_cmd_io),
        .cmd_index(cmd_index),
        .cmd_argument(cmd_argument),
        .cmd_start(cmd_start),
        .cmd_busy(cmd_busy),
        .cmd_done(cmd_done),
        .cmd_response(cmd_response),
        .cmd_timeout(cmd_timeout),
        .cmd_crc_error(cmd_crc_error),
        .clk_enable(clk_enable),
        .clk_divider(clk_divider),
        .clk_calibrated(clk_calibrated),
        .power_state(power_state),
        .security_lock(security_lock),
        .access_granted(access_granted),
        .error_status(error_status),
        .error_clear(error_clear)
    );

    // Data Engine Module
    sdcard_data_engine #(
        .SDCARD_DATA_WIDTH(SDCARD_DATA_WIDTH),
        .FIFO_DEPTH(SDCARD_FIFO_DEPTH)
    ) data_engine (
        .PCLK_i(PCLK_i),
        .PRESETn_i(PRESETn_i),
        .sd_clk_o(sd_clk_o),
        .sd_dat_io(sd_dat_io),
        .data_in(data_in),
        .data_out(data_out),
        .data_valid(data_valid),
        .data_ready(data_ready),
        .data_start(data_start),
        .data_busy(data_busy),
        .data_done(data_done),
        .data_crc(data_crc),
        .data_crc_error(data_crc_error),
        .fifo_data_in(fifo_data_in),
        .fifo_data_out(fifo_data_out),
        .fifo_write(fifo_write),
        .fifo_read(fifo_read),
        .fifo_full(fifo_full),
        .fifo_empty(fifo_empty),
        .fifo_count(fifo_count),
        .clk_enable(clk_enable),
        .clk_divider(clk_divider),
        .power_state(power_state),
        .security_lock(security_lock),
        .access_granted(access_granted),
        .error_status(error_status),
        .error_clear(error_clear)
    );

    // Clock Generator Module
    sdcard_clock_generator clock_generator (
        .PCLK_i(PCLK_i),
        .PRESETn_i(PRESETn_i),
        .sd_clk_o(sd_clk_o),
        .clk_enable(clk_enable),
        .clk_divider(clk_divider),
        .clk_calibrated(clk_calibrated),
        .cal_start(cal_start),
        .cal_busy(cal_busy),
        .cal_done(cal_done),
        .cal_result(cal_result),
        .power_state(power_state),
        .error_status(error_status),
        .error_clear(error_clear)
    );

    // DMA Controller Module (Conditional)
    generate
        if (SDCARD_DMA_ENABLE) begin : dma_controller_gen
            sdcard_dma_controller dma_controller (
                .PCLK_i(PCLK_i),
                .PRESETn_i(PRESETn_i),
                .dma_req_o(dma_req_o),
                .dma_ack_i(dma_ack_i),
                .dma_addr_o(dma_addr_o),
                .dma_len_o(dma_len_o),
                .dma_we_o(dma_we_o),
                .dma_burst_o(dma_burst_o),
                .dma_cache_o(dma_cache_o),
                .dma_enable(dma_enable),
                .dma_base_addr(dma_base_addr),
                .dma_length(dma_length),
                .dma_busy(dma_busy),
                .dma_done(dma_done),
                .dma_error(dma_error),
                .fifo_data_out(fifo_data_out),
                .fifo_read(fifo_read),
                .fifo_empty(fifo_empty),
                .power_state(power_state),
                .security_lock(security_lock),
                .access_granted(access_granted),
                .error_status(error_status),
                .error_clear(error_clear)
            );
        end else begin : no_dma_gen
            assign dma_req_o = 1'b0;
            assign dma_addr_o = 32'h0;
            assign dma_len_o = 16'h0;
            assign dma_we_o = 1'b0;
            assign dma_burst_o = 1'b0;
            assign dma_cache_o = 4'h0;
            assign dma_busy = 1'b0;
            assign dma_done = 1'b0;
            assign dma_error = 1'b0;
        end
    endgenerate

    // Power Controller Module
    sdcard_power_controller power_controller (
        .PCLK_i(PCLK_i),
        .PRESETn_i(PRESETn_i),
        .sd_pwr_en_o(sd_pwr_en_o),
        .sd_vdd_sel_o(sd_vdd_sel_o),
        .power_state(power_state),
        .power_good(power_good),
        .power_fault(power_fault),
        .voltage_sel(voltage_sel),
        .clk_enable(clk_enable),
        .error_status(error_status),
        .error_clear(error_clear)
    );

    // Security Controller Module
    sdcard_security_controller #(
        .SDCARD_KEY_WIDTH(256),
        .SDCARD_AUTH_TIMEOUT(1000),
        .SDCARD_MAX_ATTEMPTS(3)
    ) security_controller (
        .PCLK_i(PCLK_i),
        .PRESETn_i(PRESETn_i),
        .auth_key_i(256'h0),          // TODO: Connect to secure key storage
        .enc_key_i(256'h0),           // TODO: Connect to encryption key
        .user_id_i(8'h0),             // TODO: Connect to user ID
        .access_level_i(4'h0),        // TODO: Connect to access level
        .auth_request_i(1'b0),        // TODO: Connect to auth request
        .enc_request_i(1'b0),         // TODO: Connect to encryption request
        .dec_request_i(1'b0),         // TODO: Connect to decryption request
        .auth_valid_o(),              // TODO: Connect to auth valid
        .enc_ready_o(),               // TODO: Connect to encryption ready
        .access_granted_o(access_granted),
        .security_lock_o(security_lock),
        .auth_attempts_o(),           // TODO: Connect to auth attempts
        .security_status_o(),         // TODO: Connect to security status
        .tamper_detect_i(1'b0),      // TODO: Connect to tamper detection
        .power_fault_i(power_fault),
        .clock_glitch_i(1'b0),       // TODO: Connect to clock glitch detection
        .reset_attack_i(1'b0),       // TODO: Connect to reset attack detection
        .security_alert_o(),          // TODO: Connect to security alert
        .alert_level_o(),             // TODO: Connect to alert level
        .audit_trail_o()              // TODO: Connect to audit trail
    );

    // Debug Controller Module
    sdcard_debug_controller #(
        .SDCARD_TRACE_DEPTH(1024),
        .SDCARD_DEBUG_REG_WIDTH(32)
    ) debug_controller (
        .PCLK_i(PCLK_i),
        .PRESETn_i(PRESETn_i),
        .jtag_tck_i(jtag_tck_i),
        .jtag_tms_i(jtag_tms_i),
        .jtag_tdi_i(jtag_tdi_i),
        .jtag_tdo_o(jtag_tdo_o),
        .jtag_trst_n_i(jtag_trst_n_i),
        .debug_enable_i(debug_enable),
        .trace_enable_i(1'b0),        // TODO: Connect to trace enable
        .break_enable_i(1'b0),        // TODO: Connect to break enable
        .step_enable_i(1'b0),         // TODO: Connect to step enable
        .reset_debug_i(1'b0),         // TODO: Connect to debug reset
        .debug_active_o(),             // TODO: Connect to debug active
        .trace_ready_o(),              // TODO: Connect to trace ready
        .break_hit_o(),               // TODO: Connect to break hit
        .step_done_o(),               // TODO: Connect to step done
        .debug_error_o(),             // TODO: Connect to debug error
        .trace_data_i({24'h0, trace_data}),    // TODO: Connect to trace data input
        .trace_valid_i(trace_valid),  // TODO: Connect to trace valid input
        .trace_type_i(4'h0),          // TODO: Connect to trace type
        .trace_data_o(debug_trace_data),
        .trace_valid_o(trace_valid_o),
        .trace_type_o(),              // TODO: Connect to trace type output
        .debug_addr_i(8'h0),          // TODO: Connect to debug address
        .debug_data_i(32'h0),         // TODO: Connect to debug data input
        .debug_write_i(1'b0),         // TODO: Connect to debug write
        .debug_data_o(),              // TODO: Connect to debug data output
        .debug_ready_o(),             // TODO: Connect to debug ready
        .perf_counters_i(16'h0),      // TODO: Connect to performance counters
        .perf_valid_i(1'b0),          // TODO: Connect to performance valid
        .perf_ready_o(),              // TODO: Connect to performance ready
        .error_inject_i(1'b0),        // TODO: Connect to error injection
        .error_type_i(8'h0),          // TODO: Connect to error type
        .error_injected_o(),          // TODO: Connect to error injected
        .error_ready_o()              // TODO: Connect to error ready
    );

    // Test Controller Module
    sdcard_test_controller #(
        .SDCARD_TEST_PATTERN_WIDTH(32),
        .SDCARD_SCAN_CHAIN_LENGTH(256),
        .SDCARD_MEMORY_DEPTH(1024)
    ) test_controller (
        .PCLK_i(PCLK_i),
        .PRESETn_i(PRESETn_i),
        .test_enable_i(1'b0),         // TODO: Connect to test enable
        .test_mode_i(1'b0),           // TODO: Connect to test mode
        .test_type_i(4'h0),           // TODO: Connect to test type
        .test_start_i(cal_start),     // TODO: Connect to test start
        .test_stop_i(1'b0),           // TODO: Connect to test stop
        .test_reset_i(1'b0),          // TODO: Connect to test reset
        .test_active_o(),              // TODO: Connect to test active
        .test_done_o(),                // TODO: Connect to test done
        .test_pass_o(),                // TODO: Connect to test pass
        .test_fail_o(),                // TODO: Connect to test fail
        .test_progress_o(),            // TODO: Connect to test progress
        .test_status_o(),              // TODO: Connect to test status
        .test_data_i(32'h0),          // TODO: Connect to test data input
        .test_data_o(),                // TODO: Connect to test data output
        .test_data_valid_i(1'b0),     // TODO: Connect to test data valid
        .test_data_ready_o(),          // TODO: Connect to test data ready
        .test_data_error_o(),          // TODO: Connect to test data error
        .scan_clk_i(1'b0),            // TODO: Connect to scan clock
        .scan_enable_i(1'b0),         // TODO: Connect to scan enable
        .scan_in_i(1'b0),             // TODO: Connect to scan input
        .scan_out_o(),                 // TODO: Connect to scan output
        .scan_mode_i(1'b0),           // TODO: Connect to scan mode
        .scan_reset_i(1'b0),          // TODO: Connect to scan reset
        .mem_addr_i(10'h0),           // TODO: Connect to memory address
        .mem_data_i(32'h0),           // TODO: Connect to memory data input
        .mem_data_o(),                 // TODO: Connect to memory data output
        .mem_write_i(1'b0),           // TODO: Connect to memory write
        .mem_read_i(1'b0),            // TODO: Connect to memory read
        .mem_ready_o(),                // TODO: Connect to memory ready
        .mem_error_o(),                // TODO: Connect to memory error
        .loopback_enable_i(1'b0),     // TODO: Connect to loopback enable
        .loopback_data_i(8'h0),       // TODO: Connect to loopback data input
        .loopback_data_o(),            // TODO: Connect to loopback data output
        .loopback_valid_i(1'b0),      // TODO: Connect to loopback valid
        .loopback_ready_o(),           // TODO: Connect to loopback ready
        .loopback_error_o(),           // TODO: Connect to loopback error
        .perf_benchmark_i(16'h0),     // TODO: Connect to performance benchmark
        .perf_result_o(),              // TODO: Connect to performance result
        .perf_start_i(1'b0),          // TODO: Connect to performance start
        .perf_done_o(),                // TODO: Connect to performance done
        .perf_pass_o()                 // TODO: Connect to performance pass
    );

    // Error Controller Module
    sdcard_error_controller error_controller (
        .PCLK_i(PCLK_i),
        .PRESETn_i(PRESETn_i),
        .error_status(error_status),
        .error_clear(error_clear),
        .error_interrupt(error_interrupt),
        .cmd_timeout(cmd_timeout),
        .cmd_crc_error(cmd_crc_error),
        .data_crc_error(data_crc_error),
        .dma_error(dma_error),
        .power_fault(power_fault),
        .tamper_detected(tamper_detected),
        .performance_overflow(performance_overflow),
        .cal_busy(cal_busy),
        .power_state(power_state)
    );

    // Performance Controller Module
    sdcard_performance_controller performance_controller (
        .PCLK_i(PCLK_i),
        .PRESETn_i(PRESETn_i),
        .performance_counters(performance_counters),
        .performance_overflow(performance_overflow),
        .cmd_busy(cmd_busy),
        .data_busy(data_busy),
        .dma_busy(dma_busy),
        .fifo_count(fifo_count),
        .power_state(power_state)
    );

    // Calibration Controller Module
    sdcard_calibration_controller calibration_controller (
        .PCLK_i(PCLK_i),
        .PRESETn_i(PRESETn_i),
        .cal_start(cal_start),
        .cal_busy(cal_busy),
        .cal_done(cal_done),
        .cal_result(cal_result),
        .clk_divider(clk_divider),
        .clk_calibrated(clk_calibrated),
        .power_state(power_state),
        .error_status(error_status),
        .error_clear(error_clear)
    );

    // Interrupt Controller Module
    sdcard_interrupt_controller interrupt_controller (
        .PCLK_i(PCLK_i),
        .PRESETn_i(PRESETn_i),
        .sd_irq_o(sd_irq_o),
        .dma_irq_o(dma_irq_o),
        .error_irq_o(error_irq_o),
        .debug_irq_o(debug_irq_o),
        .interrupt_status(interrupt_status),
        .interrupt_enable(interrupt_enable),
        .interrupt_pending(interrupt_pending),
        .cmd_done(cmd_done),
        .data_done(data_done),
        .dma_done(dma_done),
        .error_interrupt(error_interrupt),
        .debug_enable(debug_enable),
        .power_state(power_state),
        .cal_busy(cal_busy),
        .performance_overflow(performance_overflow)
    );

    // SD Interface Module
    sdcard_interface #(
        .SDCARD_DATA_WIDTH(SDCARD_DATA_WIDTH)
    ) sd_interface (
        .PCLK_i(PCLK_i),
        .PRESETn_i(PRESETn_i),
        .sd_cmd_io(sd_cmd_io),
        .sd_dat_io(sd_dat_io),
        .sd_cd_i(sd_cd_i),
        .sd_wp_i(sd_wp_i),
        .cmd_busy(cmd_busy),
        .data_busy(data_busy),
        .power_state(power_state),
        .security_lock(security_lock),
        .access_granted(access_granted),
        .error_status(error_status),
        .error_clear(error_clear)
    );

    // Debug trace data output assignment
    assign trace_data_o = debug_trace_data[7:0];

endmodule
