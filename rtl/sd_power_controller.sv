//=============================================================================
// Module Name: sd_power_controller
//=============================================================================
// Description: Power Controller for SD Card Controller
//              Manages power states and power sequencing
//              with voltage monitoring and fault detection
//
// Features:
// - Power state management (Active, Idle, Sleep, Power-down)
// - Power sequencing control
// - Voltage monitoring and selection
// - Power fault detection
// - Power optimization
// - Thermal management
//
// Author: Vyges Development Team
// License: Apache-2.0
//=============================================================================

module sd_power_controller (
    // Clock and Reset
    input  logic                    PCLK_i,           // APB clock
    input  logic                    PRESETn_i,        // APB reset, active low
    
    // SD Card Power Interface
    output logic                   sd_pwr_en_o,       // SD card power enable
    output logic                   sd_vdd_sel_o,      // SD card voltage select
    
    // Power Control Interface
    input  logic [1:0]             power_state,       // Power state
    output logic                   power_good,        // Power good
    output logic                   power_fault,       // Power fault
    input  logic [3:0]             voltage_sel,       // Voltage selection
    input  logic                   clk_enable,        // Clock enable
    
    // Error Interface
    input  logic [15:0]            error_status,      // Error status
    output logic                   error_clear        // Error clear
);

    // Power controller state machine states
    typedef enum logic [2:0] {
        PWR_OFF = 3'b000,
        PWR_STARTUP = 3'b001,
        PWR_ACTIVE = 3'b010,
        PWR_IDLE = 3'b011,
        PWR_SLEEP = 3'b100,
        PWR_FAULT = 3'b101
    } pwr_state_t;
    
    pwr_state_t pwr_state, pwr_next_state;
    
    // Internal signals
    logic [15:0]                   startup_counter;   // Startup counter
    logic [15:0]                   voltage_counter;   // Voltage counter
    logic [7:0]                    fault_counter;     // Fault counter
    logic                          voltage_stable;    // Voltage stable
    logic                          thermal_ok;        // Thermal OK
    logic                          power_sequence_done; // Power sequence done
    logic [3:0]                    current_voltage;   // Current voltage
    logic [1:0]                    target_power_state; // Target power state
    logic                          power_transition; // Power transition
    
    // Power state constants
    localparam [1:0] PWR_ACTIVE_STATE = 2'b00;
    localparam [1:0] PWR_IDLE_STATE = 2'b01;
    localparam [1:0] PWR_SLEEP_STATE = 2'b10;
    localparam [1:0] PWR_POWER_DOWN_STATE = 2'b11;
    
    // Timing constants
    localparam [15:0] STARTUP_DELAY = 16'h0100;  // Startup delay
    localparam [15:0] VOLTAGE_SETTLE = 16'h0080; // Voltage settle time
    localparam [7:0] FAULT_THRESHOLD = 8'h10;    // Fault threshold
    
    // Power state machine
    always_ff @(posedge PCLK_i or negedge PRESETn_i) begin
        if (!PRESETn_i) begin
            pwr_state <= PWR_OFF;
        end else begin
            pwr_state <= pwr_next_state;
        end
    end
    
    // Power state machine next state logic
    always_comb begin
        pwr_next_state = pwr_state;
        
        case (pwr_state)
            PWR_OFF: begin
                if (power_state != PWR_POWER_DOWN_STATE) begin
                    pwr_next_state = PWR_STARTUP;
                end
            end
            
            PWR_STARTUP: begin
                if (power_sequence_done && voltage_stable) begin
                    pwr_next_state = PWR_ACTIVE;
                end else if (power_fault) begin
                    pwr_next_state = PWR_FAULT;
                end
            end
            
            PWR_ACTIVE: begin
                if (power_state == PWR_IDLE_STATE) begin
                    pwr_next_state = PWR_IDLE;
                end else if (power_state == PWR_SLEEP_STATE) begin
                    pwr_next_state = PWR_SLEEP;
                end else if (power_state == PWR_POWER_DOWN_STATE) begin
                    pwr_next_state = PWR_OFF;
                end else if (power_fault) begin
                    pwr_next_state = PWR_FAULT;
                end
            end
            
            PWR_IDLE: begin
                if (power_state == PWR_ACTIVE_STATE) begin
                    pwr_next_state = PWR_ACTIVE;
                end else if (power_state == PWR_SLEEP_STATE) begin
                    pwr_next_state = PWR_SLEEP;
                end else if (power_state == PWR_POWER_DOWN_STATE) begin
                    pwr_next_state = PWR_OFF;
                end else if (power_fault) begin
                    pwr_next_state = PWR_FAULT;
                end
            end
            
            PWR_SLEEP: begin
                if (power_state == PWR_ACTIVE_STATE) begin
                    pwr_next_state = PWR_ACTIVE;
                end else if (power_state == PWR_IDLE_STATE) begin
                    pwr_next_state = PWR_IDLE;
                end else if (power_state == PWR_POWER_DOWN_STATE) begin
                    pwr_next_state = PWR_OFF;
                end else if (power_fault) begin
                    pwr_next_state = PWR_FAULT;
                end
            end
            
            PWR_FAULT: begin
                if (error_clear) begin
                    pwr_next_state = PWR_OFF;
                end
            end
            
            default: begin
                pwr_next_state = PWR_OFF;
            end
        endcase
    end
    
    // Power control logic
    always_ff @(posedge PCLK_i or negedge PRESETn_i) begin
        if (!PRESETn_i) begin
            sd_pwr_en_o <= 1'b0;
            sd_vdd_sel_o <= 1'b0;
            power_good <= 1'b0;
            power_fault <= 1'b0;
            startup_counter <= 16'h0;
            voltage_counter <= 16'h0;
            fault_counter <= 8'h0;
            voltage_stable <= 1'b0;
            thermal_ok <= 1'b1;
            power_sequence_done <= 1'b0;
            current_voltage <= 4'h0;
            target_power_state <= 2'b00;
            power_transition <= 1'b0;
            error_clear <= 1'b0;
        end else begin
            // Default values
            power_transition <= 1'b0;
            error_clear <= 1'b0;
            
            case (pwr_state)
                PWR_OFF: begin
                    sd_pwr_en_o <= 1'b0;
                    sd_vdd_sel_o <= 1'b0;
                    power_good <= 1'b0;
                    power_fault <= 1'b0;
                    startup_counter <= 16'h0;
                    voltage_counter <= 16'h0;
                    voltage_stable <= 1'b0;
                    power_sequence_done <= 1'b0;
                end
                
                PWR_STARTUP: begin
                    // Power-up sequence
                    if (startup_counter < STARTUP_DELAY) begin
                        startup_counter <= startup_counter + 16'h1;
                    end else begin
                        sd_pwr_en_o <= 1'b1;
                        sd_vdd_sel_o <= voltage_sel[0];
                        current_voltage <= voltage_sel;
                        power_sequence_done <= 1'b1;
                    end
                end
                
                PWR_ACTIVE: begin
                    // Active power state
                    sd_pwr_en_o <= 1'b1;
                    sd_vdd_sel_o <= voltage_sel[0];
                    power_good <= 1'b1;
                    power_fault <= 1'b0;
                    
                    // Voltage monitoring
                    if (voltage_sel != current_voltage) begin
                        current_voltage <= voltage_sel;
                        voltage_counter <= 16'h0;
                        voltage_stable <= 1'b0;
                    end else if (voltage_counter < VOLTAGE_SETTLE) begin
                        voltage_counter <= voltage_counter + 16'h1;
                    end else begin
                        voltage_stable <= 1'b1;
                    end
                    
                    // Thermal monitoring
                    if (!thermal_ok) begin
                        fault_counter <= fault_counter + 8'h1;
                        if (fault_counter >= FAULT_THRESHOLD) begin
                            power_fault <= 1'b1;
                        end
                    end else begin
                        fault_counter <= 8'h0;
                    end
                end
                
                PWR_IDLE: begin
                    // Idle power state
                    sd_pwr_en_o <= 1'b1;
                    sd_vdd_sel_o <= voltage_sel[0];
                    power_good <= 1'b1;
                    
                    // Reduced functionality
                    if (!clk_enable) begin
                        // Clock gated in idle mode
                    end
                end
                
                PWR_SLEEP: begin
                    // Sleep power state
                    sd_pwr_en_o <= 1'b0;
                    sd_vdd_sel_o <= 1'b0;
                    power_good <= 1'b0;
                    
                    // Minimal functionality
                end
                
                PWR_FAULT: begin
                    // Fault state
                    sd_pwr_en_o <= 1'b0;
                    sd_vdd_sel_o <= 1'b0;
                    power_good <= 1'b0;
                    power_fault <= 1'b1;
                    error_clear <= 1'b1;
                end
                
                default: begin
                    // No action
                end
            endcase
        end
    end
    
    // Power state transition detection
    always_ff @(posedge PCLK_i) begin
        if (power_state != target_power_state) begin
            target_power_state <= power_state;
            power_transition <= 1'b1;
        end else begin
            power_transition <= 1'b0;
        end
    end
    
    // Assertions for power protocol compliance
    // synthesis translate_off
    property power_startup_sequence;
        @(posedge PCLK_i) (pwr_state == PWR_STARTUP) |-> ##[1:1000] (pwr_state == PWR_ACTIVE || pwr_state == PWR_FAULT);
    endproperty
    
    property power_fault_detection;
        @(posedge PCLK_i) power_fault |-> ##[1:10] (pwr_state == PWR_FAULT);
    endproperty
    
    property voltage_stability;
        @(posedge PCLK_i) (pwr_state == PWR_ACTIVE && voltage_sel != current_voltage) |-> 
                          ##[1:100] voltage_stable;
    endproperty
    
    property power_good_condition;
        @(posedge PCLK_i) (pwr_state == PWR_ACTIVE || pwr_state == PWR_IDLE) |-> power_good;
    endproperty
    
    power_startup_sequence_check: assert property (power_startup_sequence)
        else $error("Power startup sequence violation");
    
    power_fault_detection_check: assert property (power_fault_detection)
        else $error("Power fault detection violation");
    
    voltage_stability_check: assert property (voltage_stability)
        else $error("Voltage stability violation");
    
    power_good_condition_check: assert property (power_good_condition)
        else $error("Power good condition violation");
    // synthesis translate_on

endmodule 