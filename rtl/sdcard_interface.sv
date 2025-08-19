//=============================================================================
// Module Name: sdcard_interface
//=============================================================================
// Description: SD Interface for SD Card Controller
//              Manages SD card physical interface signals,
//              timing control, and interface state management
//
// Features:
// - SD card signal management
// - Bidirectional data line control
// - Card detection and write protect monitoring
// - Interface timing control
// - Power state management
// - Security validation
// - Error detection and reporting
//
// Author: Vyges Development Team
// License: Apache-2.0
//=============================================================================

module sdcard_interface #(
    parameter int SDCARD_DATA_WIDTH = 4
) (
    // Clock and Reset
    input  logic                    PCLK_i,           // APB clock
    input  logic                    PRESETn_i,        // APB reset, active low
    
    // SD Card Interface
    inout  logic                   sd_cmd_io,         // SD command line
    inout  logic [SDCARD_DATA_WIDTH-1:0] sd_dat_io,       // SD data lines
    input  logic                   sd_cd_i,           // Card detect
    input  logic                   sd_wp_i,           // Write protect
    
    // Control Interface
    input  logic                   cmd_busy,          // Command engine busy
    input  logic                   data_busy,         // Data engine busy
    input  logic [1:0]             power_state,       // Power state
    input  logic                   security_lock,     // Security lock
    input  logic                   access_granted,    // Access granted
    
    // Error Interface
    input  logic [15:0]            error_status,      // Error status
    output logic                   error_clear        // Error clear
);

    // SD interface state machine states
    typedef enum logic [2:0] {
        IF_IDLE = 3'b000,
        IF_CMD_MODE = 3'b001,
        IF_DATA_MODE = 3'b010,
        IF_BUSY_MODE = 3'b011,
        IF_ERROR = 3'b100,
        IF_POWER_DOWN = 3'b101
    } interface_state_t;
    
    interface_state_t interface_state, interface_next_state;
    
    // Internal signals
    logic [SDCARD_DATA_WIDTH-1:0]  data_out;          // Data output
    logic [SDCARD_DATA_WIDTH-1:0]  data_out_en;       // Data output enable
    logic [SDCARD_DATA_WIDTH-1:0]  data_in;           // Data input
    logic                          cmd_out;            // Command output
    logic                          cmd_out_en;         // Command output enable
    logic                          cmd_in;             // Command input
    logic                          card_present;       // Card present
    logic                          write_protected;    // Write protected
    logic                          interface_ready;    // Interface ready
    logic                          timing_valid;       // Timing valid
    logic [15:0]                   timing_counter;    // Timing counter
    logic [15:0]                   timing_limit;      // Timing limit
    logic                          security_violation; // Security violation
    logic                          power_good;         // Power good
    logic [7:0]                    error_count;       // Error count
    logic                          error_clear_next;   // Next error clear
    
    // SD interface parameters
    localparam [15:0] CMD_SETUP_TIME = 16'h0004;      // Command setup time
    localparam [15:0] CMD_HOLD_TIME = 16'h0002;       // Command hold time
    localparam [15:0] DATA_SETUP_TIME = 16'h0002;     // Data setup time
    localparam [15:0] DATA_HOLD_TIME = 16'h0001;      // Data hold time
    localparam [15:0] BUSY_TIMEOUT = 16'hFFFF;        // Busy timeout
    localparam [7:0] MAX_ERROR_COUNT = 8'hFF;         // Maximum error count
    
    // SD interface state machine
    always_ff @(posedge PCLK_i or negedge PRESETn_i) begin
        if (!PRESETn_i) begin
            interface_state <= IF_IDLE;
        end else begin
            interface_state <= interface_next_state;
        end
    end
    
    // SD interface state machine next state logic
    always_comb begin
        interface_next_state = interface_state;
        
        case (interface_state)
            IF_IDLE: begin
                if (cmd_busy && power_state != 2'b11) begin
                    interface_next_state = IF_CMD_MODE;
                end else if (data_busy && power_state != 2'b11) begin
                    interface_next_state = IF_DATA_MODE;
                end else if (power_state == 2'b11) begin
                    interface_next_state = IF_POWER_DOWN;
                end
            end
            
            IF_CMD_MODE: begin
                if (!cmd_busy) begin
                    interface_next_state = IF_IDLE;
                end else if (error_status[0]) begin
                    interface_next_state = IF_ERROR;
                end
            end
            
            IF_DATA_MODE: begin
                if (!data_busy) begin
                    interface_next_state = IF_IDLE;
                end else if (error_status[0]) begin
                    interface_next_state = IF_ERROR;
                end
            end
            
            IF_BUSY_MODE: begin
                if (timing_counter >= timing_limit) begin
                    interface_next_state = IF_ERROR;
                end else if (!cmd_busy && !data_busy) begin
                    interface_next_state = IF_IDLE;
                end
            end
            
            IF_ERROR: begin
                if (error_clear_next) begin
                    interface_next_state = IF_IDLE;
                end
            end
            
            IF_POWER_DOWN: begin
                if (power_state != 2'b11) begin
                    interface_next_state = IF_IDLE;
                end
            end
            
            default: begin
                interface_next_state = IF_IDLE;
            end
        endcase
    end
    
    // SD interface control logic
    always_ff @(posedge PCLK_i or negedge PRESETn_i) begin
        if (!PRESETn_i) begin
            data_out <= {SDCARD_DATA_WIDTH{1'b1}};
            data_out_en <= {SDCARD_DATA_WIDTH{1'b0}};
            cmd_out <= 1'b1;
            cmd_out_en <= 1'b0;
            card_present <= 1'b0;
            write_protected <= 1'b0;
            interface_ready <= 1'b0;
            timing_valid <= 1'b0;
            timing_counter <= 16'h0;
            timing_limit <= 16'h0;
            security_violation <= 1'b0;
            power_good <= 1'b0;
            error_count <= 8'h0;
            error_clear_next <= 1'b0;
        end else begin
            // Default values
            error_clear_next <= 1'b0;
            
            // Update card status
            card_present <= sd_cd_i;
            write_protected <= sd_wp_i;
            power_good <= (power_state != 2'b11);
            
            // Update interface ready status
            interface_ready <= card_present && power_good && !security_violation;
            
            case (interface_state)
                IF_IDLE: begin
                    // Reset interface signals
                    data_out_en <= {SDCARD_DATA_WIDTH{1'b0}};
                    cmd_out_en <= 1'b0;
                    timing_valid <= 1'b0;
                    timing_counter <= 16'h0;
                    
                    // Check security
                    if (!access_granted && (cmd_busy || data_busy)) begin
                        security_violation <= 1'b1;
                    end else begin
                        security_violation <= 1'b0;
                    end
                end
                
                IF_CMD_MODE: begin
                    // Command mode timing control
                    if (timing_counter == 16'h0) begin
                        timing_limit <= CMD_SETUP_TIME;
                        timing_valid <= 1'b1;
                    end else if (timing_counter >= CMD_SETUP_TIME) begin
                        cmd_out_en <= 1'b1;
                        timing_limit <= CMD_HOLD_TIME;
                    end else if (timing_counter >= (CMD_SETUP_TIME + CMD_HOLD_TIME)) begin
                        cmd_out_en <= 1'b0;
                        timing_valid <= 1'b0;
                    end
                    
                    if (timing_valid) begin
                        timing_counter <= timing_counter + 16'h1;
                    end
                end
                
                IF_DATA_MODE: begin
                    // Data mode timing control
                    if (timing_counter == 16'h0) begin
                        timing_limit <= DATA_SETUP_TIME;
                        timing_valid <= 1'b1;
                    end else if (timing_counter >= DATA_SETUP_TIME) begin
                        data_out_en <= {SDCARD_DATA_WIDTH{1'b1}};
                        timing_limit <= DATA_HOLD_TIME;
                    end else if (timing_counter >= (DATA_SETUP_TIME + DATA_HOLD_TIME)) begin
                        data_out_en <= {SDCARD_DATA_WIDTH{1'b0}};
                        timing_valid <= 1'b0;
                    end
                    
                    if (timing_valid) begin
                        timing_counter <= timing_counter + 16'h1;
                    end
                end
                
                IF_BUSY_MODE: begin
                    // Busy mode timeout monitoring
                    timing_counter <= timing_counter + 16'h1;
                    timing_limit <= BUSY_TIMEOUT;
                end
                
                IF_ERROR: begin
                    // Error handling
                    error_count <= error_count + 8'h1;
                    
                    if (error_count >= MAX_ERROR_COUNT) begin
                        // Reset interface
                        data_out_en <= {SDCARD_DATA_WIDTH{1'b0}};
                        cmd_out_en <= 1'b0;
                        error_clear_next <= 1'b1;
                        error_count <= 8'h0;
                    end
                end
                
                IF_POWER_DOWN: begin
                    // Power down mode
                    data_out_en <= {SDCARD_DATA_WIDTH{1'b0}};
                    cmd_out_en <= 1'b0;
                    interface_ready <= 1'b0;
                    timing_valid <= 1'b0;
                end
                
                default: begin
                    // No action
                end
            endcase
        end
    end
    
    // SD card signal control
    // Command line control
    assign sd_cmd_io = cmd_out_en ? cmd_out : 1'bz;
    assign cmd_in = sd_cmd_io;
    
    // Data lines control
    generate
        for (genvar i = 0; i < SDCARD_DATA_WIDTH; i = i + 1) begin : data_line_gen
            assign sd_dat_io[i] = data_out_en[i] ? data_out[i] : 1'bz;
            assign data_in[i] = sd_dat_io[i];
        end
    endgenerate
    
    // Error clear output
    assign error_clear = error_clear_next;
    
    // Interface status monitoring
    always_ff @(posedge PCLK_i or negedge PRESETn_i) begin
        if (!PRESETn_i) begin
            // Initialize monitoring
        end else begin
            // Monitor interface status
            if (security_violation) begin
                // Log security violation
            end
            
            if (!card_present && (cmd_busy || data_busy)) begin
                // Log card removal during operation
            end
            
            if (write_protected && data_busy) begin
                // Log write attempt to protected card
            end
        end
    end
    
    // Assertions for SD interface protocol compliance
    // synthesis translate_off
    property interface_state_transition;
        @(posedge PCLK_i) (interface_state == IF_IDLE) |-> ##[1:10] (interface_state != IF_IDLE || !cmd_busy && !data_busy);
    endproperty
    
    property command_timing_validity;
        @(posedge PCLK_i) (interface_state == IF_CMD_MODE) |-> ##[1:100] (interface_state != IF_CMD_MODE || cmd_out_en);
    endproperty
    
    property data_timing_validity;
        @(posedge PCLK_i) (interface_state == IF_DATA_MODE) |-> ##[1:100] (interface_state != IF_DATA_MODE || data_out_en != 0);
    endproperty
    
    property security_violation_detection;
        @(posedge PCLK_i) (!access_granted && (cmd_busy || data_busy)) |-> ##1 security_violation;
    endproperty
    
    property card_presence_monitoring;
        @(posedge PCLK_i) sd_cd_i |-> ##1 card_present;
    endproperty
    
    interface_state_transition_check: assert property (interface_state_transition)
        else $error("Interface state transition violation");
    
    command_timing_validity_check: assert property (command_timing_validity)
        else $error("Command timing validity violation");
    
    data_timing_validity_check: assert property (data_timing_validity)
        else $error("Data timing validity violation");
    
    security_violation_detection_check: assert property (security_violation_detection)
        else $error("Security violation detection violation");
    
    card_presence_monitoring_check: assert property (card_presence_monitoring)
        else $error("Card presence monitoring violation");
    // synthesis translate_on

endmodule 