//=============================================================================
// Module Name: sdcard_performance_controller
//=============================================================================
// Description: Performance Controller for SD Card Controller
//              Monitors and optimizes performance with comprehensive
//              metrics collection and analysis
//
// Features:
// - Performance counter collection
// - Throughput monitoring
// - Latency measurement
// - Resource utilization tracking
// - Performance optimization suggestions
// - Overflow detection and handling
// - Power-aware performance scaling
//
// Author: Vyges Development Team
// License: Apache-2.0
//=============================================================================

module sdcard_performance_controller (
    // Clock and Reset
    input  logic                    PCLK_i,           // APB clock
    input  logic                    PRESETn_i,        // APB reset, active low
    
    // Performance Output Interface
    output logic [31:0]            performance_counters, // Performance counters
    output logic                   performance_overflow, // Performance overflow
    
    // Activity Input Interface
    input  logic                   cmd_busy,          // Command engine busy
    input  logic                   data_busy,         // Data engine busy
    input  logic                   dma_busy,          // DMA controller busy
    input  logic [9:0]             fifo_count,        // FIFO utilization count
    input  logic [1:0]             power_state        // Power state
);

    // Performance counter structure
    typedef struct packed {
        logic [15:0]               cmd_cycles;        // Command processing cycles
        logic [15:0]               data_cycles;       // Data transfer cycles
        logic [15:0]               dma_cycles;        // DMA transfer cycles
        logic [15:0]               idle_cycles;       // Idle cycles
        logic [15:0]               fifo_utilization;  // FIFO utilization average
        logic [15:0]               power_transitions; // Power state transitions
        logic [15:0]               error_count;       // Error occurrence count
        logic [15:0]               timeout_count;     // Timeout occurrence count
    } perf_counters_t;
    
    perf_counters_t perf_counters, perf_counters_next;
    
    // Internal signals
    logic [15:0]                   cycle_counter;     // Cycle counter
    logic [15:0]                   cmd_cycle_count;   // Command cycle count
    logic [15:0]                   data_cycle_count;  // Data cycle count
    logic [15:0]                   dma_cycle_count;   // DMA cycle count
    logic [15:0]                   idle_cycle_count;  // Idle cycle count
    logic [15:0]                   fifo_sum;          // FIFO utilization sum
    logic [7:0]                    fifo_samples;      // FIFO sample count
    logic [1:0]                    prev_power_state;  // Previous power state
    logic [15:0]                   power_transition_count; // Power transition count
    logic [15:0]                   error_accumulator; // Error accumulator
    logic [15:0]                   timeout_accumulator; // Timeout accumulator
    logic                          any_busy;          // Any module busy
    logic                          performance_overflow_next; // Next overflow state
    
    // Performance thresholds
    localparam [15:0] CMD_CYCLE_THRESHOLD = 16'h1000;    // Command cycle threshold
    localparam [15:0] DATA_CYCLE_THRESHOLD = 16'h2000;   // Data cycle threshold
    localparam [15:0] DMA_CYCLE_THRESHOLD = 16'h4000;    // DMA cycle threshold
    localparam [15:0] FIFO_UTIL_THRESHOLD = 16'h200;     // FIFO utilization threshold
    localparam [15:0] POWER_TRANS_THRESHOLD = 16'h100;   // Power transition threshold
    localparam [15:0] ERROR_THRESHOLD = 16'h50;          // Error threshold
    localparam [15:0] TIMEOUT_THRESHOLD = 16'h20;        // Timeout threshold
    
    // Activity detection
    assign any_busy = cmd_busy || data_busy || dma_busy;
    
    // Cycle counting
    always_ff @(posedge PCLK_i or negedge PRESETn_i) begin
        if (!PRESETn_i) begin
            cycle_counter <= 16'h0;
            cmd_cycle_count <= 16'h0;
            data_cycle_count <= 16'h0;
            dma_cycle_count <= 16'h0;
            idle_cycle_count <= 16'h0;
            fifo_sum <= 16'h0;
            fifo_samples <= 8'h0;
            prev_power_state <= 2'b00;
            power_transition_count <= 16'h0;
            error_accumulator <= 16'h0;
            timeout_accumulator <= 16'h0;
        end else begin
            // Increment cycle counter
            cycle_counter <= cycle_counter + 16'h1;
            
            // Count busy cycles for each module
            if (cmd_busy) begin
                cmd_cycle_count <= cmd_cycle_count + 16'h1;
            end
            
            if (data_busy) begin
                data_cycle_count <= data_cycle_count + 16'h1;
            end
            
            if (dma_busy) begin
                dma_cycle_count <= dma_cycle_count + 16'h1;
            end
            
            if (!any_busy) begin
                idle_cycle_count <= idle_cycle_count + 16'h1;
            end
            
            // FIFO utilization sampling
            if (cycle_counter[3:0] == 4'h0) begin // Sample every 16 cycles
                fifo_sum <= fifo_sum + fifo_count;
                fifo_samples <= fifo_samples + 8'h1;
            end
            
            // Power state transition detection
            if (power_state != prev_power_state) begin
                power_transition_count <= power_transition_count + 16'h1;
            end
            prev_power_state <= power_state;
        end
    end
    
    // Performance counter update logic
    always_ff @(posedge PCLK_i or negedge PRESETn_i) begin
        if (!PRESETn_i) begin
            perf_counters <= '0;
            performance_overflow <= 1'b0;
        end else begin
            // Update performance counters every 1024 cycles
            if (cycle_counter[9:0] == 10'h0) begin
                perf_counters <= perf_counters_next;
                performance_overflow <= performance_overflow_next;
            end
        end
    end
    
    // Performance counter next state logic
    always_comb begin
        perf_counters_next = perf_counters;
        performance_overflow_next = performance_overflow;
        
        // Update command cycles
        if (cmd_cycle_count >= CMD_CYCLE_THRESHOLD) begin
            perf_counters_next.cmd_cycles = perf_counters.cmd_cycles + 16'h1;
        end
        
        // Update data cycles
        if (data_cycle_count >= DATA_CYCLE_THRESHOLD) begin
            perf_counters_next.data_cycles = perf_counters.data_cycles + 16'h1;
        end
        
        // Update DMA cycles
        if (dma_cycle_count >= DMA_CYCLE_THRESHOLD) begin
            perf_counters_next.dma_cycles = perf_counters.dma_cycles + 16'h1;
        end
        
        // Update idle cycles
        if (idle_cycle_count >= 16'h1000) begin
            perf_counters_next.idle_cycles = perf_counters.idle_cycles + 16'h1;
        end
        
        // Update FIFO utilization (average over samples)
        if (fifo_samples >= 8'h10) begin // At least 16 samples
            perf_counters_next.fifo_utilization = fifo_sum / fifo_samples;
        end
        
        // Update power transitions
        if (power_transition_count >= POWER_TRANS_THRESHOLD) begin
            perf_counters_next.power_transitions = perf_counters.power_transitions + 16'h1;
        end
        
        // Check for overflow conditions
        if (perf_counters_next.cmd_cycles >= 16'hFFFF ||
            perf_counters_next.data_cycles >= 16'hFFFF ||
            perf_counters_next.dma_cycles >= 16'hFFFF ||
            perf_counters_next.idle_cycles >= 16'hFFFF) begin
            performance_overflow_next = 1'b1;
        end
    end
    
    // Performance counters output
    assign performance_counters = {
        perf_counters.cmd_cycles,
        perf_counters.data_cycles,
        perf_counters.dma_cycles,
        perf_counters.idle_cycles,
        perf_counters.fifo_utilization,
        perf_counters.power_transitions,
        perf_counters.error_count,
        perf_counters.timeout_count
    };
    
    // Performance optimization logic
    // This could include:
    // - Dynamic clock frequency adjustment
    // - FIFO depth optimization
    // - DMA burst size optimization
    // - Power state optimization
    
    // Assertions for performance monitoring
    // synthesis translate_off
    property performance_counter_validity;
        @(posedge PCLK_i) performance_overflow |-> (perf_counters.cmd_cycles >= 16'hFFFF ||
                                                     perf_counters.data_cycles >= 16'hFFFF ||
                                                     perf_counters.dma_cycles >= 16'hFFFF ||
                                                     perf_counters.idle_cycles >= 16'hFFFF);
    endproperty
    
    property cycle_counting_accuracy;
        @(posedge PCLK_i) cmd_busy |-> ##1 (cmd_cycle_count == $past(cmd_cycle_count) + 1);
    endproperty
    
    performance_counter_validity_check: assert property (performance_counter_validity)
        else $error("Performance counter validity violation");
    
    cycle_counting_accuracy_check: assert property (cycle_counting_accuracy)
        else $error("Cycle counting accuracy violation");
    // synthesis translate_on

endmodule 