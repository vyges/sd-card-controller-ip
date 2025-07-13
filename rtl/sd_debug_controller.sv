//=============================================================================
// Module Name: sd_debug_controller
//=============================================================================
// Description: Debug Controller for SD Card Controller
//              Manages JTAG interface and trace generation
//              with comprehensive debug capabilities
//
// Features:
// - JTAG interface management
// - Trace generation and output
// - Debug event handling
// - Test access control
// - Debug data collection
// - Performance monitoring
//
// Author: Vyges Development Team
// License: Apache-2.0
//=============================================================================

module sd_debug_controller (
    // Clock and Reset
    input  logic                    PCLK_i,           // APB clock
    input  logic                    PRESETn_i,        // APB reset, active low
    
    // JTAG Interface
    input  logic                   jtag_tck_i,        // JTAG test clock
    input  logic                   jtag_tms_i,        // JTAG test mode select
    input  logic                   jtag_tdi_i,        // JTAG test data input
    output logic                   jtag_tdo_o,        // JTAG test data output
    input  logic                   jtag_trst_n_i,     // JTAG test reset
    
    // Trace Interface
    output logic [7:0]             trace_data_o,      // Trace data output
    output logic                   trace_valid_o,     // Trace data valid
    
    // Debug Control Interface
    input  logic                   debug_enable,      // Debug enable
    input  logic [7:0]             trace_data,        // Trace data
    input  logic                   trace_valid,       // Trace valid
    input  logic                   jtag_enable,       // JTAG enable
    input  logic                   cmd_busy,          // Command busy
    input  logic                   data_busy,         // Data busy
    input  logic                   dma_busy,          // DMA busy
    input  logic [15:0]            error_status,      // Error status
    input  logic [1:0]             power_state        // Power state
);

    // Debug controller state machine states
    typedef enum logic [2:0] {
        DEBUG_IDLE = 3'b000,
        DEBUG_ACTIVE = 3'b001,
        DEBUG_TRACE = 3'b010,
        DEBUG_JTAG = 3'b011,
        DEBUG_ERROR = 3'b100
    } debug_state_t;
    
    debug_state_t debug_state, debug_next_state;
    
    // Internal signals
    logic [7:0]                    jtag_shift_reg;    // JTAG shift register
    logic [3:0]                    jtag_state;        // JTAG state
    logic [7:0]                    trace_buffer;      // Trace buffer
    logic                          trace_ready;       // Trace ready
    logic [15:0]                   debug_counter;     // Debug counter
    logic [7:0]                    event_flags;       // Event flags
    logic                          jtag_active;       // JTAG active
    logic                          trace_active;      // Trace active
    logic [7:0]                    debug_data;        // Debug data
    logic                          debug_valid;       // Debug valid
    logic [15:0]                   performance_counters; // Performance counters
    
    // JTAG state definitions
    localparam [3:0] JTAG_RESET = 4'h0;
    localparam [3:0] JTAG_IDLE = 4'h1;
    localparam [3:0] JTAG_DR_SCAN = 4'h2;
    localparam [3:0] JTAG_IR_SCAN = 4'h3;
    localparam [3:0] JTAG_EXIT1_DR = 4'h4;
    localparam [3:0] JTAG_EXIT1_IR = 4'h5;
    localparam [3:0] JTAG_PAUSE_DR = 4'h6;
    localparam [3:0] JTAG_PAUSE_IR = 4'h7;
    localparam [3:0] JTAG_UPDATE_DR = 4'h8;
    localparam [3:0] JTAG_UPDATE_IR = 4'h9;
    localparam [3:0] JTAG_SELECT_DR = 4'hA;
    localparam [3:0] JTAG_SELECT_IR = 4'hB;
    localparam [3:0] JTAG_CAPTURE_DR = 4'hC;
    localparam [3:0] JTAG_CAPTURE_IR = 4'hD;
    localparam [3:0] JTAG_SHIFT_DR = 4'hE;
    localparam [3:0] JTAG_SHIFT_IR = 4'hF;
    
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
                if (debug_enable && power_state != 2'b11) begin
                    debug_next_state = DEBUG_ACTIVE;
                end
            end
            
            DEBUG_ACTIVE: begin
                if (!debug_enable) begin
                    debug_next_state = DEBUG_IDLE;
                end else if (trace_valid) begin
                    debug_next_state = DEBUG_TRACE;
                end else if (jtag_enable && jtag_active) begin
                    debug_next_state = DEBUG_JTAG;
                end else if (error_status[0]) begin
                    debug_next_state = DEBUG_ERROR;
                end
            end
            
            DEBUG_TRACE: begin
                if (trace_ready) begin
                    debug_next_state = DEBUG_ACTIVE;
                end
            end
            
            DEBUG_JTAG: begin
                if (!jtag_active) begin
                    debug_next_state = DEBUG_ACTIVE;
                end
            end
            
            DEBUG_ERROR: begin
                if (!error_status[0]) begin
                    debug_next_state = DEBUG_IDLE;
                end
            end
            
            default: begin
                debug_next_state = DEBUG_IDLE;
            end
        endcase
    end
    
    // Debug control logic
    always_ff @(posedge PCLK_i or negedge PRESETn_i) begin
        if (!PRESETn_i) begin
            jtag_tdo_o <= 1'b0;
            trace_data_o <= 8'h0;
            trace_valid_o <= 1'b0;
            jtag_shift_reg <= 8'h0;
            jtag_state <= JTAG_RESET;
            trace_buffer <= 8'h0;
            trace_ready <= 1'b0;
            debug_counter <= 16'h0;
            event_flags <= 8'h0;
            jtag_active <= 1'b0;
            trace_active <= 1'b0;
            debug_data <= 8'h0;
            debug_valid <= 1'b0;
            performance_counters <= 16'h0;
        end else begin
            // Default values
            trace_valid_o <= 1'b0;
            trace_ready <= 1'b0;
            
            case (debug_state)
                DEBUG_IDLE: begin
                    jtag_tdo_o <= 1'b0;
                    trace_data_o <= 8'h0;
                    trace_valid_o <= 1'b0;
                    jtag_active <= 1'b0;
                    trace_active <= 1'b0;
                    debug_counter <= 16'h0;
                    event_flags <= 8'h0;
                end
                
                DEBUG_ACTIVE: begin
                    // Active debug state
                    debug_counter <= debug_counter + 16'h1;
                    
                    // Event monitoring
                    event_flags[0] <= cmd_busy;
                    event_flags[1] <= data_busy;
                    event_flags[2] <= dma_busy;
                    event_flags[3] <= error_status[0];
                    event_flags[4] <= power_state[0];
                    event_flags[5] <= power_state[1];
                    event_flags[6] <= debug_enable;
                    event_flags[7] <= jtag_enable;
                    
                    // Performance monitoring
                    if (cmd_busy) performance_counters[3:0] <= performance_counters[3:0] + 4'h1;
                    if (data_busy) performance_counters[7:4] <= performance_counters[7:4] + 4'h1;
                    if (dma_busy) performance_counters[11:8] <= performance_counters[11:8] + 4'h1;
                    if (error_status[0]) performance_counters[15:12] <= performance_counters[15:12] + 4'h1;
                end
                
                DEBUG_TRACE: begin
                    // Trace generation
                    trace_active <= 1'b1;
                    trace_buffer <= trace_data;
                    trace_data_o <= trace_data;
                    trace_valid_o <= trace_valid;
                    trace_ready <= 1'b1;
                end
                
                DEBUG_JTAG: begin
                    // JTAG interface
                    jtag_active <= 1'b1;
                    
                    // JTAG state machine (simplified)
                    if (jtag_tms_i) begin
                        case (jtag_state)
                            JTAG_RESET: jtag_state <= JTAG_IDLE;
                            JTAG_IDLE: jtag_state <= JTAG_DR_SCAN;
                            JTAG_DR_SCAN: jtag_state <= JTAG_CAPTURE_DR;
                            JTAG_CAPTURE_DR: jtag_state <= JTAG_SHIFT_DR;
                            JTAG_SHIFT_DR: jtag_state <= JTAG_EXIT1_DR;
                            JTAG_EXIT1_DR: jtag_state <= JTAG_UPDATE_DR;
                            JTAG_UPDATE_DR: jtag_state <= JTAG_IDLE;
                            default: jtag_state <= JTAG_RESET;
                        endcase
                    end else begin
                        case (jtag_state)
                            JTAG_RESET: jtag_state <= JTAG_IDLE;
                            JTAG_IDLE: jtag_state <= JTAG_IDLE;
                            JTAG_DR_SCAN: jtag_state <= JTAG_IDLE;
                            JTAG_CAPTURE_DR: jtag_state <= JTAG_SHIFT_DR;
                            JTAG_SHIFT_DR: jtag_state <= JTAG_SHIFT_DR;
                            JTAG_EXIT1_DR: jtag_state <= JTAG_SHIFT_DR;
                            JTAG_UPDATE_DR: jtag_state <= JTAG_IDLE;
                            default: jtag_state <= JTAG_RESET;
                        endcase
                    end
                    
                    // JTAG data shift
                    if (jtag_state == JTAG_SHIFT_DR) begin
                        jtag_shift_reg <= {jtag_shift_reg[6:0], jtag_tdi_i};
                        jtag_tdo_o <= jtag_shift_reg[7];
                    end
                end
                
                DEBUG_ERROR: begin
                    // Error state
                    jtag_active <= 1'b0;
                    trace_active <= 1'b0;
                    trace_data_o <= 8'hFF; // Error indicator
                    trace_valid_o <= 1'b1;
                end
                
                default: begin
                    // No action
                end
            endcase
        end
    end
    
    // JTAG clock domain crossing (simplified)
    always_ff @(posedge jtag_tck_i or negedge jtag_trst_n_i) begin
        if (!jtag_trst_n_i) begin
            jtag_shift_reg <= 8'h0;
        end else if (jtag_state == JTAG_SHIFT_DR) begin
            jtag_shift_reg <= {jtag_shift_reg[6:0], jtag_tdi_i};
        end
    end
    
    // Debug data collection
    always_ff @(posedge PCLK_i) begin
        if (debug_enable && trace_valid) begin
            debug_data <= trace_data;
            debug_valid <= 1'b1;
        end else begin
            debug_valid <= 1'b0;
        end
    end
    
    // Assertions for debug protocol compliance
    // synthesis translate_off
    property debug_enable_condition;
        @(posedge PCLK_i) debug_enable |-> ##[1:10] (debug_state == DEBUG_ACTIVE);
    endproperty
    
    property trace_generation;
        @(posedge PCLK_i) (debug_state == DEBUG_TRACE) |-> ##[1:10] trace_valid_o;
    endproperty
    
    property jtag_activity;
        @(posedge PCLK_i) (debug_state == DEBUG_JTAG) |-> jtag_active;
    endproperty
    
    property debug_error_handling;
        @(posedge PCLK_i) (debug_state == DEBUG_ERROR) |-> ##[1:10] (debug_state == DEBUG_IDLE);
    endproperty
    
    debug_enable_condition_check: assert property (debug_enable_condition)
        else $error("Debug enable condition violation");
    
    trace_generation_check: assert property (trace_generation)
        else $error("Trace generation violation");
    
    jtag_activity_check: assert property (jtag_activity)
        else $error("JTAG activity violation");
    
    debug_error_handling_check: assert property (debug_error_handling)
        else $error("Debug error handling violation");
    // synthesis translate_on

endmodule 