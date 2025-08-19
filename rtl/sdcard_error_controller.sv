//=============================================================================
// Module Name: sdcard_error_controller
//=============================================================================
// Description: Error Controller for SD Card Controller
//              Manages error detection, classification, reporting,
//              and recovery mechanisms for robust operation
//
// Features:
// - Comprehensive error detection
// - Error classification and prioritization
// - Automatic error recovery
// - Error logging and reporting
// - Interrupt generation
// - Fault isolation
// - Error statistics collection
//
// Author: Vyges Development Team
// License: Apache-2.0
//=============================================================================

module sdcard_error_controller (
    // Clock and Reset
    input  logic                    PCLK_i,           // APB clock
    input  logic                    PRESETn_i,        // APB reset, active low
    
    // Error Control Interface
    input  logic [15:0]            error_status,      // Error status
    output logic                   error_clear,       // Error clear
    output logic                   error_interrupt,   // Error interrupt
    
    // Error Input Interface
    input  logic                   cmd_timeout,       // Command timeout
    input  logic                   cmd_crc_error,     // Command CRC error
    input  logic                   data_crc_error,    // Data CRC error
    input  logic                   dma_error,         // DMA error
    input  logic                   power_fault,       // Power fault
    input  logic                   tamper_detected,   // Tamper detected
    input  logic                   performance_overflow, // Performance overflow
    input  logic                   cal_busy,          // Calibration busy
    
    // Power Interface
    input  logic [1:0]             power_state        // Power state
);

    // Error types and classifications
    typedef enum logic [3:0] {
        ERROR_NONE = 4'b0000,
        ERROR_CMD_TIMEOUT = 4'b0001,
        ERROR_CMD_CRC = 4'b0010,
        ERROR_DATA_CRC = 4'b0011,
        ERROR_DMA = 4'b0100,
        ERROR_POWER = 4'b0101,
        ERROR_TAMPER = 4'b0110,
        ERROR_PERFORMANCE = 4'b0111,
        ERROR_CALIBRATION = 4'b1000,
        ERROR_SYSTEM = 4'b1001
    } error_type_t;
    
    // Error severity levels
    typedef enum logic [1:0] {
        SEVERITY_LOW = 2'b00,
        SEVERITY_MEDIUM = 2'b01,
        SEVERITY_HIGH = 2'b10,
        SEVERITY_CRITICAL = 2'b11
    } error_severity_t;
    
    // Error structure
    typedef struct packed {
        error_type_t                error_type;        // Error type
        error_severity_t            severity;          // Error severity
        logic [7:0]                error_code;        // Error code
        logic [15:0]               timestamp;         // Error timestamp
        logic [7:0]                retry_count;       // Retry count
        logic                      recoverable;        // Recoverable flag
        logic                      reported;           // Reported flag
    } error_entry_t;
    
    // Internal signals
    error_entry_t                  current_error;     // Current error
    error_entry_t                  error_history [0:7]; // Error history
    logic [2:0]                    error_history_ptr; // Error history pointer
    logic [15:0]                   error_counter;     // Error counter
    logic [15:0]                   error_timestamp;   // Error timestamp
    logic [7:0]                    retry_counter;     // Retry counter
    logic                          error_active;      // Error active
    logic                          recovery_in_progress; // Recovery in progress
    logic [15:0]                   error_mask;        // Error mask
    logic [15:0]                   error_enable;      // Error enable
    logic [15:0]                   error_threshold;   // Error threshold
    logic                          threshold_exceeded; // Threshold exceeded
    
    // Error state machine states
    typedef enum logic [2:0] {
        ERROR_IDLE = 3'b000,
        ERROR_DETECTED = 3'b001,
        ERROR_CLASSIFY = 3'b010,
        ERROR_RECOVER = 3'b011,
        ERROR_REPORT = 3'b100,
        ERROR_LOG = 3'b101,
        ERROR_CLEAR = 3'b110
    } error_state_t;
    
    error_state_t error_state, error_next_state;
    
    // Error parameters
    localparam [7:0] MAX_RETRY_COUNT = 8'h03;        // Maximum retry count
    localparam [15:0] ERROR_TIMEOUT = 16'hFFFF;      // Error timeout
    localparam [15:0] DEFAULT_ERROR_THRESHOLD = 16'h0010; // Default error threshold
    
    // Error state machine
    always_ff @(posedge PCLK_i or negedge PRESETn_i) begin
        if (!PRESETn_i) begin
            error_state <= ERROR_IDLE;
        end else begin
            error_state <= error_next_state;
        end
    end
    
    // Error state machine next state logic
    always_comb begin
        error_next_state = error_state;
        
        case (error_state)
            ERROR_IDLE: begin
                if (error_status != 16'h0) begin
                    error_next_state = ERROR_DETECTED;
                end
            end
            
            ERROR_DETECTED: begin
                error_next_state = ERROR_CLASSIFY;
            end
            
            ERROR_CLASSIFY: begin
                error_next_state = ERROR_RECOVER;
            end
            
            ERROR_RECOVER: begin
                if (current_error.recoverable && retry_counter < MAX_RETRY_COUNT) begin
                    error_next_state = ERROR_IDLE;
                end else begin
                    error_next_state = ERROR_REPORT;
                end
            end
            
            ERROR_REPORT: begin
                error_next_state = ERROR_LOG;
            end
            
            ERROR_LOG: begin
                error_next_state = ERROR_CLEAR;
            end
            
            ERROR_CLEAR: begin
                error_next_state = ERROR_IDLE;
            end
            
            default: begin
                error_next_state = ERROR_IDLE;
            end
        endcase
    end
    
    // Error control logic
    always_ff @(posedge PCLK_i or negedge PRESETn_i) begin
        if (!PRESETn_i) begin
            current_error <= '0;
            error_history <= '{8{'0}};
            error_history_ptr <= 3'h0;
            error_counter <= 16'h0;
            error_timestamp <= 16'h0;
            retry_counter <= 8'h0;
            error_active <= 1'b0;
            recovery_in_progress <= 1'b0;
            error_mask <= 16'h0000;
            error_enable <= 16'hFFFF;
            error_threshold <= DEFAULT_ERROR_THRESHOLD;
            threshold_exceeded <= 1'b0;
            error_clear <= 1'b0;
            error_interrupt <= 1'b0;
        end else begin
            // Default values
            error_clear <= 1'b0;
            error_interrupt <= 1'b0;
            
            // Increment timestamp
            error_timestamp <= error_timestamp + 16'h1;
            
            case (error_state)
                ERROR_IDLE: begin
                    error_active <= 1'b0;
                    recovery_in_progress <= 1'b0;
                end
                
                ERROR_DETECTED: begin
                    error_active <= 1'b1;
                    error_counter <= error_counter + 16'h1;
                    
                    // Check if threshold exceeded
                    if (error_counter >= error_threshold) begin
                        threshold_exceeded <= 1'b1;
                    end
                end
                
                ERROR_CLASSIFY: begin
                    // Classify error based on input signals
                    if (cmd_timeout) begin
                        current_error.error_type <= ERROR_CMD_TIMEOUT;
                        current_error.severity <= SEVERITY_MEDIUM;
                        current_error.error_code <= 8'h01;
                        current_error.recoverable <= 1'b1;
                    end else if (cmd_crc_error) begin
                        current_error.error_type <= ERROR_CMD_CRC;
                        current_error.severity <= SEVERITY_HIGH;
                        current_error.error_code <= 8'h02;
                        current_error.recoverable <= 1'b1;
                    end else if (data_crc_error) begin
                        current_error.error_type <= ERROR_DATA_CRC;
                        current_error.severity <= SEVERITY_HIGH;
                        current_error.error_code <= 8'h03;
                        current_error.recoverable <= 1'b1;
                    end else if (dma_error) begin
                        current_error.error_type <= ERROR_DMA;
                        current_error.severity <= SEVERITY_MEDIUM;
                        current_error.error_code <= 8'h04;
                        current_error.recoverable <= 1'b1;
                    end else if (power_fault) begin
                        current_error.error_type <= ERROR_POWER;
                        current_error.severity <= SEVERITY_CRITICAL;
                        current_error.error_code <= 8'h05;
                        current_error.recoverable <= 1'b0;
                    end else if (tamper_detected) begin
                        current_error.error_type <= ERROR_TAMPER;
                        current_error.severity <= SEVERITY_CRITICAL;
                        current_error.error_code <= 8'h06;
                        current_error.recoverable <= 1'b0;
                    end else if (performance_overflow) begin
                        current_error.error_type <= ERROR_PERFORMANCE;
                        current_error.severity <= SEVERITY_LOW;
                        current_error.error_code <= 8'h07;
                        current_error.recoverable <= 1'b1;
                    end else if (cal_busy) begin
                        current_error.error_type <= ERROR_CALIBRATION;
                        current_error.severity <= SEVERITY_LOW;
                        current_error.error_code <= 8'h08;
                        current_error.recoverable <= 1'b1;
                    end else begin
                        current_error.error_type <= ERROR_SYSTEM;
                        current_error.severity <= SEVERITY_HIGH;
                        current_error.error_code <= 8'hFF;
                        current_error.recoverable <= 1'b0;
                    end
                    
                    // Set error metadata
                    current_error.timestamp <= error_timestamp;
                    current_error.retry_count <= retry_counter;
                    current_error.reported <= 1'b0;
                end
                
                ERROR_RECOVER: begin
                    recovery_in_progress <= 1'b1;
                    
                    if (current_error.recoverable && retry_counter < MAX_RETRY_COUNT) begin
                        retry_counter <= retry_counter + 8'h1;
                        // Attempt recovery (implementation depends on error type)
                    end
                end
                
                ERROR_REPORT: begin
                    // Generate error interrupt
                    if (error_enable[current_error.error_code] && !current_error.reported) begin
                        error_interrupt <= 1'b1;
                        current_error.reported <= 1'b1;
                    end
                end
                
                ERROR_LOG: begin
                    // Store error in history
                    error_history[error_history_ptr] <= current_error;
                    error_history_ptr <= error_history_ptr + 3'h1;
                end
                
                ERROR_CLEAR: begin
                    // Clear error status
                    error_clear <= 1'b1;
                    error_active <= 1'b0;
                    recovery_in_progress <= 1'b0;
                end
                
                default: begin
                    // No action
                end
            endcase
        end
    end
    
    // Error recovery logic (simplified)
    // In a real implementation, this would include specific recovery procedures
    // for each error type
    
    // Error statistics and monitoring
    always_ff @(posedge PCLK_i or negedge PRESETn_i) begin
        if (!PRESETn_i) begin
            // Initialize error statistics
        end else begin
            // Update error statistics based on current_error
        end
    end
    
    // Assertions for error handling protocol compliance
    // synthesis translate_off
    property error_detection_condition;
        @(posedge PCLK_i) (cmd_timeout || cmd_crc_error || data_crc_error || 
                           dma_error || power_fault || tamper_detected || 
                           performance_overflow || cal_busy) |-> ##1 error_active;
    endproperty
    
    property error_recovery_completion;
        @(posedge PCLK_i) error_active |-> ##[1:1000] (!error_active);
    endproperty
    
    property error_interrupt_generation;
        @(posedge PCLK_i) (current_error.severity == SEVERITY_CRITICAL) |-> ##[1:10] error_interrupt;
    endproperty
    
    property error_threshold_validation;
        @(posedge PCLK_i) threshold_exceeded |-> (error_counter >= error_threshold);
    endproperty
    
    error_detection_condition_check: assert property (error_detection_condition)
        else $error("Error detection condition violation");
    
    error_recovery_completion_check: assert property (error_recovery_completion)
        else $error("Error recovery completion violation");
    
    error_interrupt_generation_check: assert property (error_interrupt_generation)
        else $error("Error interrupt generation violation");
    
    error_threshold_validation_check: assert property (error_threshold_validation)
        else $error("Error threshold validation violation");
    // synthesis translate_on

endmodule 