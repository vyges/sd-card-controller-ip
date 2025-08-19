//=============================================================================
// Module Name: sdcard_debug_controller
//=============================================================================
// Description: Debug Controller for SD Card Controller
//              Manages JTAG interface, trace collection, debug registers,
//              and comprehensive debugging capabilities
//
// Features:
// - JTAG TAP controller interface
// - Real-time trace collection and buffering
// - Debug register access and control
// - Performance monitoring hooks
// - Error injection and testing
// - Debug state management
// - Trace analysis and filtering
//
// Author: Vyges Development Team
// License: Apache-2.0
//=============================================================================

module sdcard_debug_controller #(
    parameter int SDCARD_TRACE_DEPTH = 1024,
    parameter int SDCARD_DEBUG_REG_WIDTH = 32
) (
    // Clock and Reset
    input  logic                    PCLK_i,           // APB clock
    input  logic                    PRESETn_i,        // APB reset, active low
    
    // JTAG Interface
    input  logic                   jtag_tck_i,       // JTAG TCK
    input  logic                   jtag_tms_i,       // JTAG TMS
    input  logic                   jtag_tdi_i,       // JTAG TDI
    output logic                   jtag_tdo_o,       // JTAG TDO
    input  logic                   jtag_trst_n_i,    // JTAG TRST (active low)
    
    // Debug Control Interface
    input  logic                   debug_enable_i,   // Debug enable
    input  logic                   trace_enable_i,   // Trace enable
    input  logic                   break_enable_i,   // Break enable
    input  logic                   step_enable_i,    // Step enable
    input  logic                   reset_debug_i,    // Reset debug state
    
    // Debug Status Interface
    output logic                   debug_active_o,   // Debug active
    output logic                   break_hit_o,      // Break point hit
    output logic                   step_done_o,      // Step completed
    output logic                   debug_error_o,    // Debug error
    
    // Trace Interface
    input  logic [31:0]           trace_data_i,     // Trace data input
    input  logic                   trace_valid_i,    // Trace data valid
    input  logic [3:0]            trace_type_i,     // Trace type
    output logic                   trace_ready_o,    // Trace ready for data
    output logic [31:0]           trace_data_o,     // Trace data output
    output logic                   trace_valid_o,    // Trace data valid
    output logic [3:0]            trace_type_o,     // Trace type output
    
    // Debug Register Interface
    input  logic [7:0]            debug_addr_i,     // Debug register address
    input  logic [SDCARD_DEBUG_REG_WIDTH-1:0] debug_data_i,     // Debug register data in
    input  logic                   debug_write_i,    // Debug register write
    output logic [SDCARD_DEBUG_REG_WIDTH-1:0] debug_data_o,     // Debug register data out
    output logic                   debug_ready_o,    // Debug register ready
    
    // Performance Monitoring
    input  logic [15:0]           perf_counters_i,  // Performance counters
    input  logic                   perf_valid_i,     // Performance data valid
    output logic                   perf_ready_o,     // Performance ready
    
    // Error Injection
    input  logic                   error_inject_i,   // Error injection request
    input  logic [7:0]            error_type_i,     // Error type to inject
    output logic                   error_injected_o, // Error injection done
    output logic                   error_ready_o     // Error injection ready
);

    // Debug state machine states
    typedef enum logic [3:0] {
        DEBUG_IDLE = 4'b0000,
        DEBUG_ACTIVE = 4'b0001,
        DEBUG_TRACE = 4'b0010,
        DEBUG_BREAK = 4'b0011,
        DEBUG_STEP = 4'b0100,
        DEBUG_REG_ACCESS = 4'b0101,
        DEBUG_PERF_MON = 4'b0110,
        DEBUG_ERROR_INJECT = 4'b0111,
        DEBUG_ERROR = 4'b1000
    } debug_state_t;
    
    debug_state_t debug_state, debug_next_state;
    
    // JTAG TAP controller states
    typedef enum logic [3:0] {
        TAP_RESET = 4'b0000,
        TAP_IDLE = 4'b0001,
        TAP_DR_SCAN = 4'b0010,
        TAP_DR_CAPTURE = 4'b0011,
        TAP_DR_SHIFT = 4'b0100,
        TAP_DR_EXIT1 = 4'b0101,
        TAP_DR_PAUSE = 4'b0110,
        TAP_DR_EXIT2 = 4'b0111,
        TAP_DR_UPDATE = 4'b1000,
        TAP_IR_SCAN = 4'b1001,
        TAP_IR_CAPTURE = 4'b1010,
        TAP_IR_SHIFT = 4'b1011,
        TAP_IR_EXIT1 = 4'b1100,
        TAP_IR_PAUSE = 4'b1101,
        TAP_IR_EXIT2 = 4'b1110,
        TAP_IR_UPDATE = 4'b1111
    } tap_state_t;
    
    tap_state_t tap_state, tap_next_state;
    
    // Internal signals
    logic [7:0]                    debug_reg_addr;   // Debug register address
    logic [SDCARD_DEBUG_REG_WIDTH-1:0] debug_reg_data;   // Debug register data
    logic                          debug_reg_write;  // Debug register write
    logic                          debug_reg_read;   // Debug register read
    logic [31:0]                   trace_buffer [SDCARD_TRACE_DEPTH]; // Trace buffer
    logic [9:0]                    trace_wr_ptr;     // Trace write pointer
    logic [9:0]                    trace_rd_ptr;     // Trace read pointer
    logic                          trace_full;       // Trace buffer full
    logic                          trace_empty;      // Trace buffer empty
    logic [31:0]                   trace_counter;   // Trace counter
    logic [15:0]                   break_points [8]; // Break points
    logic [7:0]                    break_enable;    // Break point enable
    logic                          break_condition; // Break condition met
    logic [7:0]                    step_counter;    // Step counter
    logic                          step_condition;  // Step condition met
    logic [15:0]                   perf_data [16];  // Performance data buffer
    logic [3:0]                    perf_wr_ptr;     // Performance write pointer
    logic [3:0]                    perf_rd_ptr;     // Performance read pointer
    logic                          perf_full;       // Performance buffer full
    logic                          perf_empty;      // Performance buffer empty
    logic [7:0]                    error_inject_type; // Error injection type
    logic                          error_inject_active; // Error injection active
    logic [31:0]                   debug_timestamp; // Debug timestamp
    logic                          jtag_shift_en;   // JTAG shift enable
    logic [31:0]                   jtag_shift_data; // JTAG shift data
    logic [4:0]                    jtag_shift_count; // JTAG shift count
    logic                          jtag_capture_en; // JTAG capture enable
    logic                          jtag_update_en;  // JTAG update enable
    
    // Debug constants
    localparam [7:0] DEBUG_REG_CTRL = 8'h00;        // Debug control register
    localparam [7:0] DEBUG_REG_STATUS = 8'h01;      // Debug status register
    localparam [7:0] DEBUG_REG_TRACE_CTRL = 8'h02;  // Trace control register
    localparam [7:0] DEBUG_REG_TRACE_DATA = 8'h03;  // Trace data register
    localparam [7:0] DEBUG_REG_BREAK_CTRL = 8'h04;  // Break point control
    localparam [7:0] DEBUG_REG_STEP_CTRL = 8'h05;   // Step control register
    localparam [7:0] DEBUG_REG_PERF_CTRL = 8'h06;   // Performance control
    localparam [7:0] DEBUG_REG_ERROR_CTRL = 8'h07;  // Error injection control
    
    // Debug state machine
    always_ff @(posedge PCLK_i or negedge PRESETn_i) begin
        if (!PRESETn_i) begin
            debug_state <= DEBUG_IDLE;
        end else begin
            debug_state <= debug_next_state;
        end
    end
    
    // Debug state machine next state logic
    always_comb begin
        debug_next_state = debug_state;
        
        case (debug_state)
            DEBUG_IDLE: begin
                if (debug_enable_i && !reset_debug_i) begin
                    debug_next_state = DEBUG_ACTIVE;
                end
            end
            
            DEBUG_ACTIVE: begin
                if (reset_debug_i) begin
                    debug_next_state = DEBUG_IDLE;
                end else if (trace_enable_i) begin
                    debug_next_state = DEBUG_TRACE;
                end else if (break_enable_i) begin
                    debug_next_state = DEBUG_BREAK;
                end else if (step_enable_i) begin
                    debug_next_state = DEBUG_STEP;
                end else if (debug_write_i || debug_reg_read) begin
                    debug_next_state = DEBUG_REG_ACCESS;
                end else if (perf_valid_i) begin
                    debug_next_state = DEBUG_PERF_MON;
                end else if (error_inject_i) begin
                    debug_next_state = DEBUG_ERROR_INJECT;
                end
            end
            
            DEBUG_TRACE: begin
                if (!trace_enable_i) begin
                    debug_next_state = DEBUG_ACTIVE;
                end else if (trace_full) begin
                    debug_next_state = DEBUG_ERROR;
                end
            end
            
            DEBUG_BREAK: begin
                if (!break_enable_i) begin
                    debug_next_state = DEBUG_ACTIVE;
                end else if (break_condition) begin
                    debug_next_state = DEBUG_ACTIVE;
                end
            end
            
            DEBUG_STEP: begin
                if (!step_enable_i) begin
                    debug_next_state = DEBUG_ACTIVE;
                end else if (step_condition) begin
                    debug_next_state = DEBUG_ACTIVE;
                end
            end
            
            DEBUG_REG_ACCESS: begin
                if (!debug_write_i && !debug_reg_read) begin
                    debug_next_state = DEBUG_ACTIVE;
                end
            end
            
            DEBUG_PERF_MON: begin
                if (!perf_valid_i) begin
                    debug_next_state = DEBUG_ACTIVE;
                end
            end
            
            DEBUG_ERROR_INJECT: begin
                if (!error_inject_i) begin
                    debug_next_state = DEBUG_ACTIVE;
                end
            end
            
            DEBUG_ERROR: begin
                if (reset_debug_i) begin
                    debug_next_state = DEBUG_IDLE;
                end
            end
            
            default: begin
                debug_next_state = DEBUG_IDLE;
            end
        endcase
    end
    
    // JTAG TAP controller state machine
    always_ff @(negedge jtag_tck_i or negedge jtag_trst_n_i) begin
        if (!jtag_trst_n_i) begin
            tap_state <= TAP_RESET;
        end else begin
            tap_state <= tap_next_state;
        end
    end
    
    // JTAG TAP controller next state logic
    always_comb begin
        tap_next_state = tap_state;
        
        case (tap_state)
            TAP_RESET: begin
                if (jtag_tms_i) begin
                    tap_next_state = TAP_IDLE;
                end
            end
            
            TAP_IDLE: begin
                if (!jtag_tms_i) begin
                    tap_next_state = TAP_DR_SCAN;
                end else begin
                    tap_next_state = TAP_IR_SCAN;
                end
            end
            
            TAP_DR_SCAN: begin
                if (!jtag_tms_i) begin
                    tap_next_state = TAP_DR_CAPTURE;
                end else begin
                    tap_next_state = TAP_IR_SCAN;
                end
            end
            
            TAP_DR_CAPTURE: begin
                if (!jtag_tms_i) begin
                    tap_next_state = TAP_DR_SHIFT;
                end else begin
                    tap_next_state = TAP_DR_EXIT1;
                end
            end
            
            TAP_DR_SHIFT: begin
                if (!jtag_tms_i) begin
                    tap_next_state = TAP_DR_SHIFT;
                end else begin
                    tap_next_state = TAP_DR_EXIT1;
                end
            end
            
            TAP_DR_EXIT1: begin
                if (!jtag_tms_i) begin
                    tap_next_state = TAP_DR_PAUSE;
                end else begin
                    tap_next_state = TAP_DR_UPDATE;
                end
            end
            
            TAP_DR_PAUSE: begin
                if (!jtag_tms_i) begin
                    tap_next_state = TAP_DR_PAUSE;
                end else begin
                    tap_next_state = TAP_DR_EXIT2;
                end
            end
            
            TAP_DR_EXIT2: begin
                if (!jtag_tms_i) begin
                    tap_next_state = TAP_DR_SHIFT;
                end else begin
                    tap_next_state = TAP_DR_UPDATE;
                end
            end
            
            TAP_DR_UPDATE: begin
                if (!jtag_tms_i) begin
                    tap_next_state = TAP_DR_SCAN;
                end else begin
                    tap_next_state = TAP_IR_SCAN;
                end
            end
            
            TAP_IR_SCAN: begin
                if (!jtag_tms_i) begin
                    tap_next_state = TAP_IR_CAPTURE;
                end else begin
                    tap_next_state = TAP_DR_SCAN;
                end
            end
            
            TAP_IR_CAPTURE: begin
                if (!jtag_tms_i) begin
                    tap_next_state = TAP_IR_SHIFT;
                end else begin
                    tap_next_state = TAP_IR_EXIT1;
                end
            end
            
            TAP_IR_SHIFT: begin
                if (!jtag_tms_i) begin
                    tap_next_state = TAP_IR_SHIFT;
                end else begin
                    tap_next_state = TAP_IR_EXIT1;
                end
            end
            
            TAP_IR_EXIT1: begin
                if (!jtag_tms_i) begin
                    tap_next_state = TAP_IR_PAUSE;
                end else begin
                    tap_next_state = TAP_IR_UPDATE;
                end
            end
            
            TAP_IR_PAUSE: begin
                if (!jtag_tms_i) begin
                    tap_next_state = TAP_IR_PAUSE;
                end else begin
                    tap_next_state = TAP_IR_EXIT2;
                end
            end
            
            TAP_IR_EXIT2: begin
                if (!jtag_tms_i) begin
                    tap_next_state = TAP_IR_SHIFT;
                end else begin
                    tap_next_state = TAP_IR_UPDATE;
                end
            end
            
            TAP_IR_UPDATE: begin
                if (!jtag_tms_i) begin
                    tap_next_state = TAP_DR_SCAN;
                end else begin
                    tap_next_state = TAP_IR_SCAN;
                end
            end
            
            default: begin
                tap_next_state = TAP_RESET;
            end
        endcase
    end
    
    // Debug control logic
    always_ff @(posedge PCLK_i or negedge PRESETn_i) begin
        if (!PRESETn_i) begin
            debug_reg_addr <= 8'h0;
            debug_reg_data <= {SDCARD_DEBUG_REG_WIDTH{1'b0}};
            debug_reg_write <= 1'b0;
            debug_reg_read <= 1'b0;
            trace_wr_ptr <= 10'h0;
            trace_rd_ptr <= 10'h0;
            trace_full <= 1'b0;
            trace_empty <= 1'b1;
            trace_counter <= 32'h0;
            break_points <= '{8{16'h0}};
            break_enable <= 8'h0;
            break_condition <= 1'b0;
            step_counter <= 8'h0;
            step_condition <= 1'b0;
            perf_wr_ptr <= 4'h0;
            perf_rd_ptr <= 4'h0;
            perf_full <= 1'b0;
            perf_empty <= 1'b1;
            error_inject_type <= 8'h0;
            error_inject_active <= 1'b0;
            debug_timestamp <= 32'h0;
            
            // Output signals
            debug_active_o <= 1'b0;
            trace_ready_o <= 1'b0;
            break_hit_o <= 1'b0;
            step_done_o <= 1'b0;
            debug_error_o <= 1'b0;
            trace_data_o <= 32'h0;
            trace_valid_o <= 1'b0;
            trace_type_o <= 4'h0;
            debug_data_o <= {SDCARD_DEBUG_REG_WIDTH{1'b0}};
            debug_ready_o <= 1'b0;
            perf_ready_o <= 1'b0;
            error_injected_o <= 1'b0;
            error_ready_o <= 1'b0;
        end else begin
            // Default values
            debug_reg_write <= 1'b0;
            debug_reg_read <= 1'b0;
            break_condition <= 1'b0;
            step_condition <= 1'b0;
            trace_valid_o <= 1'b0;
            perf_ready_o <= 1'b0;
            error_injected_o <= 1'b0;
            
            // Update debug timestamp
            debug_timestamp <= debug_timestamp + 32'h1;
            
            case (debug_state)
                DEBUG_IDLE: begin
                    // Reset debug status
                    debug_active_o <= 1'b0;
                    trace_ready_o <= 1'b0;
                    break_hit_o <= 1'b0;
                    step_done_o <= 1'b0;
                    debug_error_o <= 1'b0;
                    debug_ready_o <= 1'b0;
                end
                
                DEBUG_ACTIVE: begin
                    // Active debug state
                    debug_active_o <= 1'b1;
                    debug_ready_o <= 1'b1;
                    
                    // Check for break points
                    for (int i = 0; i < 8; i = i + 1) begin
                        if (break_enable[i] && trace_data_i == break_points[i]) begin
                            break_condition <= 1'b1;
                            break_hit_o <= 1'b1;
                        end
                    end
                    
                    // Check for step completion
                    if (step_enable_i && step_counter >= 8'h1) begin
                        step_condition <= 1'b1;
                        step_done_o <= 1'b1;
                        step_counter <= 8'h0;
                    end
                end
                
                DEBUG_TRACE: begin
                    // Trace collection
                    trace_ready_o <= 1'b1;
                    
                    if (trace_valid_i && !trace_full) begin
                        trace_buffer[trace_wr_ptr] <= trace_data_i;
                        trace_wr_ptr <= (trace_wr_ptr == 10'h3FF) ? 10'h0 : trace_wr_ptr + 10'h1;
                        trace_counter <= trace_counter + 32'h1;
                        
                        if (trace_wr_ptr == trace_rd_ptr) begin
                            trace_full <= 1'b1;
                        end
                        trace_empty <= 1'b0;
                    end
                end
                
                DEBUG_BREAK: begin
                    // Break point monitoring
                    if (break_condition) begin
                        break_hit_o <= 1'b1;
                    end
                end
                
                DEBUG_STEP: begin
                    // Step execution
                    if (trace_valid_i) begin
                        step_counter <= step_counter + 8'h1;
                    end
                end
                
                DEBUG_REG_ACCESS: begin
                    // Debug register access
                    if (debug_write_i) begin
                        debug_reg_write <= 1'b1;
                        debug_reg_addr <= debug_addr_i;
                        debug_reg_data <= debug_data_i;
                        
                        // Handle specific register writes
                        case (debug_addr_i)
                            DEBUG_REG_CTRL: begin
                                // Debug control register
                            end
                            DEBUG_REG_TRACE_CTRL: begin
                                // Trace control register
                            end
                            DEBUG_REG_BREAK_CTRL: begin
                                // Break point control
                                break_enable <= debug_data_i[7:0];
                            end
                            DEBUG_REG_STEP_CTRL: begin
                                // Step control register
                                step_counter <= debug_data_i[7:0];
                            end
                            DEBUG_REG_ERROR_CTRL: begin
                                // Error injection control
                                error_inject_type <= debug_data_i[7:0];
                            end
                        endcase
                    end else if (debug_reg_read) begin
                        debug_reg_read <= 1'b1;
                        debug_reg_addr <= debug_addr_i;
                        
                        // Handle specific register reads
                        case (debug_addr_i)
                            DEBUG_REG_STATUS: begin
                                debug_data_o <= {debug_state, tap_state, trace_counter[23:0]};
                            end
                            DEBUG_REG_TRACE_DATA: begin
                                if (!trace_empty) begin
                                    debug_data_o <= trace_buffer[trace_rd_ptr];
                                    trace_rd_ptr <= (trace_rd_ptr == 10'h3FF) ? 10'h0 : trace_rd_ptr + 10'h1;
                                    
                                    if (trace_rd_ptr == trace_wr_ptr) begin
                                        trace_empty <= 1'b1;
                                    end
                                    trace_full <= 1'b0;
                                end
                            end
                            default: begin
                                debug_data_o <= 32'h0;
                            end
                        endcase
                    end
                end
                
                DEBUG_PERF_MON: begin
                    // Performance monitoring
                    perf_ready_o <= 1'b1;
                    
                    if (perf_valid_i && !perf_full) begin
                        perf_data[perf_wr_ptr] <= perf_counters_i;
                        perf_wr_ptr <= (perf_wr_ptr == 4'hF) ? 4'h0 : perf_wr_ptr + 4'h1;
                        
                        if (perf_wr_ptr == perf_rd_ptr) begin
                            perf_full <= 1'b1;
                        end
                        perf_empty <= 1'b0;
                    end
                end
                
                DEBUG_ERROR_INJECT: begin
                    // Error injection
                    error_ready_o <= 1'b1;
                    
                    if (error_inject_i && !error_inject_active) begin
                        error_inject_active <= 1'b1;
                        error_inject_type <= error_type_i;
                        error_injected_o <= 1'b1;
                    end
                end
                
                DEBUG_ERROR: begin
                    // Debug error state
                    debug_error_o <= 1'b1;
                    debug_active_o <= 1'b0;
                end
                
                default: begin
                    // No action
                end
            endcase
        end
    end
    
    // JTAG TAP controller logic
    always_ff @(posedge jtag_tck_i or negedge jtag_trst_n_i) begin
        if (!jtag_trst_n_i) begin
            jtag_shift_en <= 1'b0;
            jtag_shift_data <= 32'h0;
            jtag_shift_count <= 5'h0;
            jtag_capture_en <= 1'b0;
            jtag_update_en <= 1'b0;
        end else begin
            case (tap_state)
                TAP_DR_CAPTURE: begin
                    jtag_capture_en <= 1'b1;
                    jtag_shift_en <= 1'b0;
                    jtag_update_en <= 1'b0;
                end
                
                TAP_DR_SHIFT: begin
                    jtag_capture_en <= 1'b0;
                    jtag_shift_en <= 1'b1;
                    jtag_update_en <= 1'b0;
                    
                    if (jtag_shift_en) begin
                        jtag_shift_data <= {jtag_tdi_i, jtag_shift_data[31:1]};
                        jtag_shift_count <= jtag_shift_count + 5'h1;
                    end
                end
                
                TAP_DR_UPDATE: begin
                    jtag_capture_en <= 1'b0;
                    jtag_shift_en <= 1'b0;
                    jtag_update_en <= 1'b1;
                    jtag_shift_count <= 5'h0;
                end
                
                default: begin
                    jtag_capture_en <= 1'b0;
                    jtag_shift_en <= 1'b0;
                    jtag_update_en <= 1'b0;
                end
            endcase
        end
    end
    
    // JTAG TDO output
    assign jtag_tdo_o = (tap_state == TAP_DR_SHIFT || tap_state == TAP_IR_SHIFT) ? 
                        jtag_shift_data[0] : 1'b0;
    
    // Trace output interface
    assign trace_ready_o = !trace_full;
    
    // Performance output interface
    assign perf_ready_o = !perf_full;
    
    // Error injection output interface
    assign error_ready_o = !error_inject_active;
    
    // Assertions for debug protocol compliance
    // synthesis translate_off
    // VERILATOR_DISABLED: property debug_state_transition;
        // VERILATOR_DISABLED: // VERILATOR_DISABLED:         @(posedge PCLK_i) (debug_state == DEBUG_IDLE) |-> ##[1:100] (debug_state != DEBUG_IDLE || !debug_enable_i);
    // VERILATOR_DISABLED: endproperty
    
    // VERILATOR_DISABLED: property trace_buffer_management;
        // VERILATOR_DISABLED: // VERILATOR_DISABLED:         @(posedge PCLK_i) (trace_valid_i && !trace_full) |-> ##1 (trace_wr_ptr != trace_rd_ptr || !trace_empty);
    // VERILATOR_DISABLED: endproperty
    
    // VERILATOR_DISABLED: property break_point_detection;
        // VERILATOR_DISABLED: // VERILATOR_DISABLED:         @(posedge PCLK_i) (break_enable_i && trace_valid_i) |-> ##[1:10] (break_condition || !break_enable_i);
    // VERILATOR_DISABLED: endproperty
    
    // VERILATOR_DISABLED: property jtag_state_transition;
        // VERILATOR_DISABLED: // VERILATOR_DISABLED:         @(posedge jtag_tck_i) (tap_state == TAP_RESET) |-> ##[1:16] (tap_state != TAP_RESET || !jtag_trst_n_i);
    // VERILATOR_DISABLED: endproperty
    
    // VERILATOR_DISABLED: property debug_register_access;
        // VERILATOR_DISABLED: // VERILATOR_DISABLED:         @(posedge PCLK_i) (debug_write_i || debug_reg_read) |-> ##[1:10] (debug_state == DEBUG_REG_ACCESS);
    // VERILATOR_DISABLED: endproperty
    
    // VERILATOR_DISABLED: debug_state_transition_check: assert property (debug_state_transition)
    //     else $error("Debug state transition violation");
    
    // VERILATOR_DISABLED: trace_buffer_management_check: assert property (trace_buffer_management)
    //     else $error("Trace buffer management violation");
    
    // VERILATOR_DISABLED: break_point_detection_check: assert property (break_point_detection)
    //     else $error("Break point detection violation");
    
    // VERILATOR_DISABLED: jtag_state_transition_check: assert property (jtag_state_transition)
    //     else $error("JTAG state transition violation");
    
    // VERILATOR_DISABLED: debug_register_access_check: assert property (debug_register_access)
    //     else $error("Debug register access violation");
    // synthesis translate_on

endmodule 