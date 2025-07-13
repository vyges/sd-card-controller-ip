//=============================================================================
// Module Name: sd_apb_interface
//=============================================================================
// Description: APB3 slave interface for SD Card Controller
//              Implements standard APB3 protocol with error handling
//              and register access control
//
// Features:
// - APB3 slave protocol compliance
// - Register read/write access
// - Error handling and reporting
// - Access control and protection
// - Ready signal management
// - Address decoding
//
// Author: Vyges Development Team
// License: Apache-2.0
//=============================================================================

module sd_apb_interface #(
    parameter int APB_ADDR_WIDTH = 16
) (
    // APB Slave Interface
    input  logic                    PCLK_i,           // APB clock
    input  logic                    PRESETn_i,        // APB reset, active low
    input  logic                    PSEL_i,           // APB select
    input  logic                    PENABLE_i,        // APB enable
    input  logic                    PWRITE_i,         // APB write enable
    input  logic [APB_ADDR_WIDTH-1:0] PADDR_i,        // APB address bus
    input  logic [31:0]            PWDATA_i,          // APB write data
    output logic [31:0]            PRDATA_o,          // APB read data
    output logic                   PREADY_o,          // APB ready
    output logic                   PSLVERR_o,         // APB slave error
    
    // Register Interface
    output logic [31:0]            reg_data_out,      // Data to register file
    input  logic [31:0]            reg_data_in,       // Data from register file
    output logic [15:0]            reg_addr,          // Register address
    output logic                   reg_read,          // Register read enable
    output logic                   reg_write,         // Register write enable
    input  logic                   reg_ready,         // Register ready
    input  logic                   reg_error          // Register error
);

    // APB state machine states
    typedef enum logic [1:0] {
        APB_IDLE = 2'b00,
        APB_SETUP = 2'b01,
        APB_ACCESS = 2'b10,
        APB_WAIT = 2'b11
    } apb_state_t;
    
    apb_state_t apb_state, apb_next_state;
    
    // Internal signals
    logic [31:0]                   read_data_reg;
    logic                          access_done;
    logic                          access_error;
    logic [15:0]                   decoded_addr;
    logic                          addr_valid;
    logic                          write_pending;
    logic                          read_pending;
    
    // Address decoding
    always_comb begin
        decoded_addr = PADDR_i[15:0];
        addr_valid = (PADDR_i >= 16'h0000) && (PADDR_i <= 16'h005C);
    end
    
    // APB state machine
    always_ff @(posedge PCLK_i or negedge PRESETn_i) begin
        if (!PRESETn_i) begin
            apb_state <= APB_IDLE;
        end else begin
            apb_state <= apb_next_state;
        end
    end
    
    // APB state machine next state logic
    always_comb begin
        apb_next_state = apb_state;
        
        case (apb_state)
            APB_IDLE: begin
                if (PSEL_i && !PENABLE_i) begin
                    apb_next_state = APB_SETUP;
                end
            end
            
            APB_SETUP: begin
                if (PSEL_i && PENABLE_i) begin
                    apb_next_state = APB_ACCESS;
                end else if (!PSEL_i) begin
                    apb_next_state = APB_IDLE;
                end
            end
            
            APB_ACCESS: begin
                if (access_done) begin
                    apb_next_state = APB_IDLE;
                end else if (!reg_ready) begin
                    apb_next_state = APB_WAIT;
                end
            end
            
            APB_WAIT: begin
                if (reg_ready || reg_error) begin
                    apb_next_state = APB_IDLE;
                end
            end
            
            default: begin
                apb_next_state = APB_IDLE;
            end
        endcase
    end
    
    // APB control signals
    always_ff @(posedge PCLK_i or negedge PRESETn_i) begin
        if (!PRESETn_i) begin
            reg_read <= 1'b0;
            reg_write <= 1'b0;
            reg_addr <= 16'h0;
            reg_data_out <= 32'h0;
            read_data_reg <= 32'h0;
            access_done <= 1'b0;
            access_error <= 1'b0;
            write_pending <= 1'b0;
            read_pending <= 1'b0;
        end else begin
            // Default values
            reg_read <= 1'b0;
            reg_write <= 1'b0;
            access_done <= 1'b0;
            access_error <= 1'b0;
            
            case (apb_state)
                APB_SETUP: begin
                    if (PSEL_i && PENABLE_i) begin
                        if (addr_valid) begin
                            reg_addr <= decoded_addr;
                            if (PWRITE_i) begin
                                reg_data_out <= PWDATA_i;
                                write_pending <= 1'b1;
                                read_pending <= 1'b0;
                            end else begin
                                read_pending <= 1'b1;
                                write_pending <= 1'b0;
                            end
                        end else begin
                            access_error <= 1'b1;
                            access_done <= 1'b1;
                        end
                    end
                end
                
                APB_ACCESS: begin
                    if (write_pending) begin
                        reg_write <= 1'b1;
                        write_pending <= 1'b0;
                    end else if (read_pending) begin
                        reg_read <= 1'b1;
                        read_pending <= 1'b0;
                    end
                    
                    if (reg_ready) begin
                        if (reg_error) begin
                            access_error <= 1'b1;
                        end else if (reg_read) begin
                            read_data_reg <= reg_data_in;
                        end
                        access_done <= 1'b1;
                    end
                end
                
                APB_WAIT: begin
                    if (reg_ready) begin
                        if (reg_error) begin
                            access_error <= 1'b1;
                        end else if (read_pending) begin
                            read_data_reg <= reg_data_in;
                        end
                        access_done <= 1'b1;
                    end
                end
                
                default: begin
                    // No action
                end
            endcase
        end
    end
    
    // APB output signals
    assign PREADY_o = (apb_state == APB_ACCESS && access_done) || 
                      (apb_state == APB_WAIT && (reg_ready || reg_error));
    
    assign PSLVERR_o = access_error || reg_error;
    
    assign PRDATA_o = read_data_reg;
    
    // Assertions for APB protocol compliance
    // synthesis translate_off
    property apb_setup_hold;
        @(posedge PCLK_i) PSEL_i && !PENABLE_i |-> ##1 PSEL_i;
    endproperty
    
    property apb_access_cycle;
        @(posedge PCLK_i) PSEL_i && PENABLE_i |-> PREADY_o;
    endproperty
    
    property apb_write_data_stable;
        @(posedge PCLK_i) PSEL_i && PENABLE_i && PWRITE_i |-> $stable(PWDATA_i);
    endproperty
    
    property apb_address_stable;
        @(posedge PCLK_i) PSEL_i && PENABLE_i |-> $stable(PADDR_i);
    endproperty
    
    apb_setup_hold_check: assert property (apb_setup_hold)
        else $error("APB setup phase violation");
    
    apb_access_cycle_check: assert property (apb_access_cycle)
        else $error("APB access cycle violation");
    
    apb_write_data_stable_check: assert property (apb_write_data_stable)
        else $error("APB write data not stable");
    
    apb_address_stable_check: assert property (apb_address_stable)
        else $error("APB address not stable");
    // synthesis translate_on

endmodule 