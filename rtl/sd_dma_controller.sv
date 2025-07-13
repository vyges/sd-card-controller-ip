//=============================================================================
// Module Name: sd_dma_controller
//=============================================================================
// Description: DMA Controller for SD Card Controller
//              Handles high-speed data transfers with burst support
//              and cache management
//
// Features:
// - DMA request and acknowledge protocol
// - Burst transfer support
// - Address generation and management
// - Cache attribute control
// - Transfer completion monitoring
// - Error handling and recovery
//
// Author: Vyges Development Team
// License: Apache-2.0
//=============================================================================

module sd_dma_controller (
    // Clock and Reset
    input  logic                    PCLK_i,           // APB clock
    input  logic                    PRESETn_i,        // APB reset, active low
    
    // DMA Interface
    output logic                   dma_req_o,         // DMA request
    input  logic                   dma_ack_i,         // DMA acknowledge
    output logic [31:0]            dma_addr_o,        // DMA address
    output logic [15:0]            dma_len_o,         // DMA length
    output logic                   dma_we_o,          // DMA write enable
    output logic                   dma_burst_o,       // DMA burst mode
    output logic [3:0]             dma_cache_o,       // DMA cache attributes
    
    // DMA Control Interface
    input  logic                   dma_enable,        // DMA enable
    input  logic [31:0]            dma_base_addr,     // DMA base address
    input  logic [15:0]            dma_length,        // DMA length
    output logic                   dma_busy,          // DMA busy
    output logic                   dma_done,          // DMA done
    output logic                   dma_error,         // DMA error
    
    // FIFO Interface
    input  logic [31:0]            fifo_data_out,     // FIFO data output
    output logic                   fifo_read,         // FIFO read enable
    input  logic                   fifo_empty,        // FIFO empty
    
    // Power and Security Interface
    input  logic [1:0]             power_state,       // Power state
    input  logic                   security_lock,     // Security lock
    input  logic                   access_granted,    // Access granted
    
    // Error Interface
    input  logic [15:0]            error_status,      // Error status
    output logic                   error_clear        // Error clear
);

    // DMA controller state machine states
    typedef enum logic [2:0] {
        DMA_IDLE = 3'b000,
        DMA_REQUEST = 3'b001,
        DMA_TRANSFER = 3'b010,
        DMA_BURST = 3'b011,
        DMA_COMPLETE = 3'b100,
        DMA_ERROR = 3'b101
    } dma_state_t;
    
    dma_state_t dma_state, dma_next_state;
    
    // Internal signals
    logic [31:0]                   current_addr;      // Current address
    logic [15:0]                   transfer_count;    // Transfer count
    logic [15:0]                   burst_count;       // Burst count
    logic [7:0]                    burst_size;        // Burst size
    logic                          transfer_active;   // Transfer active
    logic                          burst_active;      // Burst active
    logic                          transfer_complete; // Transfer complete
    logic                          transfer_error;    // Transfer error
    logic [31:0]                   data_buffer;       // Data buffer
    logic                          data_valid;        // Data valid
    logic                          data_ready;        // Data ready
    
    // DMA configuration
    localparam [7:0] MAX_BURST_SIZE = 8'h10;  // Maximum burst size
    localparam [15:0] BURST_TIMEOUT = 16'hFFFF; // Burst timeout
    
    // DMA state machine
    always_ff @(posedge PCLK_i or negedge PRESETn_i) begin
        if (!PRESETn_i) begin
            dma_state <= DMA_IDLE;
        end else begin
            dma_state <= dma_next_state;
        end
    end
    
    // DMA state machine next state logic
    always_comb begin
        dma_next_state = dma_state;
        
        case (dma_state)
            DMA_IDLE: begin
                if (dma_enable && !security_lock && access_granted && !fifo_empty) begin
                    dma_next_state = DMA_REQUEST;
                end
            end
            
            DMA_REQUEST: begin
                if (dma_ack_i) begin
                    dma_next_state = DMA_TRANSFER;
                end else if (transfer_error) begin
                    dma_next_state = DMA_ERROR;
                end
            end
            
            DMA_TRANSFER: begin
                if (transfer_complete) begin
                    dma_next_state = DMA_COMPLETE;
                end else if (burst_active && burst_count >= burst_size) begin
                    dma_next_state = DMA_BURST;
                end else if (transfer_error) begin
                    dma_next_state = DMA_ERROR;
                end
            end
            
            DMA_BURST: begin
                if (dma_ack_i) begin
                    dma_next_state = DMA_TRANSFER;
                end else if (transfer_error) begin
                    dma_next_state = DMA_ERROR;
                end
            end
            
            DMA_COMPLETE: begin
                dma_next_state = DMA_IDLE;
            end
            
            DMA_ERROR: begin
                dma_next_state = DMA_IDLE;
            end
            
            default: begin
                dma_next_state = DMA_IDLE;
            end
        endcase
    end
    
    // DMA control logic
    always_ff @(posedge PCLK_i or negedge PRESETn_i) begin
        if (!PRESETn_i) begin
            dma_req_o <= 1'b0;
            dma_addr_o <= 32'h0;
            dma_len_o <= 16'h0;
            dma_we_o <= 1'b0;
            dma_burst_o <= 1'b0;
            dma_cache_o <= 4'h0;
            dma_busy <= 1'b0;
            dma_done <= 1'b0;
            dma_error <= 1'b0;
            current_addr <= 32'h0;
            transfer_count <= 16'h0;
            burst_count <= 16'h0;
            burst_size <= 8'h0;
            transfer_active <= 1'b0;
            burst_active <= 1'b0;
            transfer_complete <= 1'b0;
            transfer_error <= 1'b0;
            data_buffer <= 32'h0;
            data_valid <= 1'b0;
            data_ready <= 1'b0;
            fifo_read <= 1'b0;
            error_clear <= 1'b0;
        end else begin
            // Default values
            dma_done <= 1'b0;
            dma_error <= 1'b0;
            transfer_complete <= 1'b0;
            transfer_error <= 1'b0;
            error_clear <= 1'b0;
            
            case (dma_state)
                DMA_IDLE: begin
                    dma_busy <= 1'b0;
                    dma_req_o <= 1'b0;
                    transfer_active <= 1'b0;
                    burst_active <= 1'b0;
                    current_addr <= dma_base_addr;
                    transfer_count <= 16'h0;
                    burst_count <= 16'h0;
                    burst_size <= MAX_BURST_SIZE;
                end
                
                DMA_REQUEST: begin
                    dma_busy <= 1'b1;
                    dma_req_o <= 1'b1;
                    dma_addr_o <= current_addr;
                    dma_len_o <= (dma_length - transfer_count < burst_size) ? 
                                (dma_length - transfer_count) : burst_size;
                    dma_we_o <= 1'b1; // Write to memory
                    dma_burst_o <= 1'b1;
                    dma_cache_o <= 4'hF; // Cacheable, write-back
                    
                    // Read data from FIFO
                    if (!fifo_empty) begin
                        fifo_read <= 1'b1;
                        data_buffer <= fifo_data_out;
                        data_valid <= 1'b1;
                    end
                end
                
                DMA_TRANSFER: begin
                    transfer_active <= 1'b1;
                    dma_req_o <= 1'b0;
                    
                    if (data_valid) begin
                        // Transfer data
                        transfer_count <= transfer_count + 16'h1;
                        burst_count <= burst_count + 16'h1;
                        current_addr <= current_addr + 32'h4;
                        data_valid <= 1'b0;
                        
                        // Check for transfer completion
                        if (transfer_count >= dma_length) begin
                            transfer_complete <= 1'b1;
                        end
                    end
                    
                    // Check for burst completion
                    if (burst_count >= burst_size) begin
                        burst_active <= 1'b1;
                    end
                end
                
                DMA_BURST: begin
                    burst_active <= 1'b0;
                    burst_count <= 16'h0;
                    
                    // Prepare next burst
                    if (transfer_count < dma_length) begin
                        dma_req_o <= 1'b1;
                        dma_addr_o <= current_addr;
                        dma_len_o <= (dma_length - transfer_count < burst_size) ? 
                                    (dma_length - transfer_count) : burst_size;
                    end
                end
                
                DMA_COMPLETE: begin
                    dma_done <= 1'b1;
                    dma_busy <= 1'b0;
                    transfer_active <= 1'b0;
                    burst_active <= 1'b0;
                end
                
                DMA_ERROR: begin
                    dma_error <= 1'b1;
                    dma_busy <= 1'b0;
                    transfer_active <= 1'b0;
                    burst_active <= 1'b0;
                    error_clear <= 1'b1;
                end
                
                default: begin
                    // No action
                end
            endcase
        end
    end
    
    // Error detection
    always_ff @(posedge PCLK_i) begin
        if (transfer_active && !dma_ack_i && transfer_count > BURST_TIMEOUT) begin
            transfer_error <= 1'b1;
        end
    end
    
    // Assertions for DMA protocol compliance
    // synthesis translate_off
    property dma_request_acknowledge;
        @(posedge PCLK_i) dma_req_o |-> ##[1:100] dma_ack_i;
    endproperty
    
    property dma_completion;
        @(posedge PCLK_i) dma_busy |-> ##[1:10000] (dma_done || dma_error);
    endproperty
    
    property dma_error_valid;
        @(posedge PCLK_i) dma_error |-> !dma_done;
    endproperty
    
    property dma_address_increment;
        @(posedge PCLK_i) (dma_state == DMA_TRANSFER && data_valid) |-> 
                          ##1 (dma_addr_o == $past(dma_addr_o) + 32'h4);
    endproperty
    
    dma_request_acknowledge_check: assert property (dma_request_acknowledge)
        else $error("DMA request acknowledge violation");
    
    dma_completion_check: assert property (dma_completion)
        else $error("DMA completion violation");
    
    dma_error_valid_check: assert property (dma_error_valid)
        else $error("DMA error validity violation");
    
    dma_address_increment_check: assert property (dma_address_increment)
        else $error("DMA address increment violation");
    // synthesis translate_on

endmodule 