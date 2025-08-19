//=============================================================================
// Module Name: sdcard_command_engine
//=============================================================================
// Description: SD Command Engine for SD Card Controller
//              Handles command generation, transmission, and response parsing
//              with proper SD protocol compliance and error handling
//
// Features:
// - SD command generation and transmission
// - Response reception and parsing
// - CRC7 generation and checking
// - Command timeout handling
// - State machine for command flow
// - Protocol compliance checking
// - Error detection and reporting
//
// Author: Vyges Development Team
// License: Apache-2.0
//=============================================================================

module sdcard_command_engine (
    // Clock and Reset
    input  logic                    PCLK_i,           // APB clock
    input  logic                    PRESETn_i,        // APB reset, active low
    
    // SD Card Interface
    output logic                   sd_clk_o,          // SD card clock
    inout  logic                   sd_cmd_io,         // SD command line
    
    // Command Interface
    input  logic [5:0]             cmd_index,         // Command index
    input  logic [31:0]            cmd_argument,      // Command argument
    input  logic                   cmd_start,         // Command start
    output logic                   cmd_busy,          // Command busy
    output logic                   cmd_done,          // Command done
    output logic [39:0]            cmd_response,      // Command response
    output logic                   cmd_timeout,       // Command timeout
    output logic                   cmd_crc_error,     // Command CRC error
    
    // Clock Interface
    input  logic                   clk_enable,        // Clock enable
    input  logic [15:0]            clk_divider,       // Clock divider
    input  logic                   clk_calibrated,    // Clock calibrated
    
    // Power and Security Interface
    input  logic [1:0]             power_state,       // Power state
    input  logic                   security_lock,     // Security lock
    input  logic                   access_granted,    // Access granted
    
    // Error Interface
    input  logic [15:0]            error_status,      // Error status
    output logic                   error_clear        // Error clear
);

    // Command engine state machine states
    typedef enum logic [3:0] {
        CMD_IDLE = 4'b0000,
        CMD_SETUP = 4'b0001,
        CMD_SEND = 4'b0010,
        CMD_WAIT_RESP = 4'b0011,
        CMD_RECEIVE = 4'b0100,
        CMD_CHECK_CRC = 4'b0101,
        CMD_COMPLETE = 4'b0110,
        CMD_ERROR = 4'b0111,
        CMD_TIMEOUT = 4'b1000,
        CMD_BUSY = 4'b1001
    } cmd_state_t;
    
    cmd_state_t cmd_state, cmd_next_state;
    
    // Internal signals
    logic [47:0]                   cmd_packet;        // Complete command packet
    logic [6:0]                    cmd_crc;           // Command CRC
    logic [6:0]                    resp_crc;          // Response CRC
    logic [6:0]                    calc_crc;          // Calculated CRC
    logic [7:0]                    bit_counter;       // Bit counter
    logic [15:0]                   timeout_counter;   // Timeout counter
    logic [15:0]                   timeout_limit;     // Timeout limit
    logic                          cmd_out;           // Command output
    logic                          cmd_out_en;        // Command output enable
    logic                          cmd_in;            // Command input
    logic                          resp_valid;        // Response valid
    logic [39:0]                   resp_data;         // Response data
    logic                          crc_valid;         // CRC valid
    logic                          timeout_expired;   // Timeout expired
    
    // SD command definitions
    localparam [5:0] CMD0_GO_IDLE_STATE = 6'h00;
    localparam [5:0] CMD1_SEND_OP_COND = 6'h01;
    localparam [5:0] CMD8_SEND_IF_COND = 6'h08;
    localparam [5:0] CMD9_SEND_CSD = 6'h09;
    localparam [5:0] CMD10_SEND_CID = 6'h0A;
    localparam [5:0] CMD12_STOP_TRANSMISSION = 6'h0C;
    localparam [5:0] CMD16_SET_BLOCKLEN = 6'h10;
    localparam [5:0] CMD17_READ_SINGLE_BLOCK = 6'h11;
    localparam [5:0] CMD18_READ_MULTIPLE_BLOCK = 6'h12;
    localparam [5:0] CMD23_SET_BLOCK_COUNT = 6'h17;
    localparam [5:0] CMD24_WRITE_BLOCK = 6'h18;
    localparam [5:0] CMD25_WRITE_MULTIPLE_BLOCK = 6'h19;
    localparam [5:0] CMD55_APP_CMD = 6'h37;
    localparam [5:0] CMD58_READ_OCR = 6'h3A;
    
    // Command packet construction
    always_comb begin
        cmd_packet = {
            1'b0,                   // Start bit
            cmd_index,              // Command index (6 bits)
            cmd_argument,           // Argument (32 bits)
            cmd_crc                 // CRC (7 bits)
        };
    end
    
    // CRC7 calculation for commands
    function automatic [6:0] calc_crc7;
        input [47:0] data;
        input [6:0] polynomial;
        reg [6:0] crc;
        integer i;
        begin
            crc = 7'h00;
            for (i = 47; i >= 0; i = i - 1) begin
                crc = {crc[5:0], 1'b0} ^ (crc[6] ^ data[i] ? polynomial : 7'h00);
            end
            calc_crc7 = crc;
        end
    endfunction
    
    // CRC7 calculation
    always_comb begin
        cmd_crc = calc_crc7({cmd_index, cmd_argument}, 7'h09);
    end
    
    // Command state machine
    always_ff @(posedge PCLK_i or negedge PRESETn_i) begin
        if (!PRESETn_i) begin
            cmd_state <= CMD_IDLE;
        end else begin
            cmd_state <= cmd_next_state;
        end
    end
    
    // Command state machine next state logic
    always_comb begin
        cmd_next_state = cmd_state;
        
        case (cmd_state)
            CMD_IDLE: begin
                if (cmd_start && clk_enable && !security_lock && access_granted) begin
                    cmd_next_state = CMD_SETUP;
                end
            end
            
            CMD_SETUP: begin
                if (clk_calibrated) begin
                    cmd_next_state = CMD_SEND;
                end
            end
            
            CMD_SEND: begin
                if (bit_counter == 8'd47) begin
                    cmd_next_state = CMD_WAIT_RESP;
                end
            end
            
            CMD_WAIT_RESP: begin
                if (timeout_expired) begin
                    cmd_next_state = CMD_TIMEOUT;
                end else if (cmd_in == 1'b0) begin
                    cmd_next_state = CMD_RECEIVE;
                end
            end
            
            CMD_RECEIVE: begin
                if (bit_counter == 8'd39) begin
                    cmd_next_state = CMD_CHECK_CRC;
                end
            end
            
            CMD_CHECK_CRC: begin
                if (crc_valid) begin
                    cmd_next_state = CMD_COMPLETE;
                end else begin
                    cmd_next_state = CMD_ERROR;
                end
            end
            
            CMD_COMPLETE: begin
                cmd_next_state = CMD_IDLE;
            end
            
            CMD_ERROR: begin
                cmd_next_state = CMD_IDLE;
            end
            
            CMD_TIMEOUT: begin
                cmd_next_state = CMD_IDLE;
            end
            
            CMD_BUSY: begin
                if (cmd_in == 1'b1) begin
                    cmd_next_state = CMD_IDLE;
                end
            end
            
            default: begin
                cmd_next_state = CMD_IDLE;
            end
        endcase
    end
    
    // Command control logic
    always_ff @(posedge PCLK_i or negedge PRESETn_i) begin
        if (!PRESETn_i) begin
            cmd_busy <= 1'b0;
            cmd_done <= 1'b0;
            cmd_timeout <= 1'b0;
            cmd_crc_error <= 1'b0;
            cmd_response <= 40'h0;
            bit_counter <= 8'h0;
            timeout_counter <= 16'h0;
            timeout_limit <= 16'hFFFF;
            cmd_out <= 1'b1;
            cmd_out_en <= 1'b0;
            resp_data <= 40'h0;
            resp_crc <= 7'h0;
            crc_valid <= 1'b0;
            timeout_expired <= 1'b0;
            error_clear <= 1'b0;
        end else begin
            // Default values
            cmd_done <= 1'b0;
            cmd_timeout <= 1'b0;
            cmd_crc_error <= 1'b0;
            error_clear <= 1'b0;
            
            case (cmd_state)
                CMD_IDLE: begin
                    cmd_busy <= 1'b0;
                    cmd_out <= 1'b1;
                    cmd_out_en <= 1'b0;
                    bit_counter <= 8'h0;
                    timeout_counter <= 16'h0;
                    timeout_expired <= 1'b0;
                    crc_valid <= 1'b0;
                    
                    // Set timeout based on command
                    case (cmd_index)
                        CMD0_GO_IDLE_STATE: timeout_limit <= 16'h0100;
                        CMD1_SEND_OP_COND: timeout_limit <= 16'hFFFF;
                        CMD8_SEND_IF_COND: timeout_limit <= 16'h0100;
                        CMD9_SEND_CSD: timeout_limit <= 16'h0100;
                        CMD10_SEND_CID: timeout_limit <= 16'h0100;
                        CMD12_STOP_TRANSMISSION: timeout_limit <= 16'h0100;
                        CMD16_SET_BLOCKLEN: timeout_limit <= 16'h0100;
                        CMD17_READ_SINGLE_BLOCK: timeout_limit <= 16'h0100;
                        CMD18_READ_MULTIPLE_BLOCK: timeout_limit <= 16'h0100;
                        CMD23_SET_BLOCK_COUNT: timeout_limit <= 16'h0100;
                        CMD24_WRITE_BLOCK: timeout_limit <= 16'h0100;
                        CMD25_WRITE_MULTIPLE_BLOCK: timeout_limit <= 16'h0100;
                        CMD55_APP_CMD: timeout_limit <= 16'h0100;
                        CMD58_READ_OCR: timeout_limit <= 16'h0100;
                        default: timeout_limit <= 16'h0100;
                    endcase
                end
                
                CMD_SETUP: begin
                    cmd_busy <= 1'b1;
                    cmd_out_en <= 1'b1;
                end
                
                CMD_SEND: begin
                    cmd_out <= cmd_packet[47 - bit_counter];
                    bit_counter <= bit_counter + 8'h1;
                end
                
                CMD_WAIT_RESP: begin
                    cmd_out_en <= 1'b0;
                    timeout_counter <= timeout_counter + 16'h1;
                    timeout_expired <= (timeout_counter >= timeout_limit);
                end
                
                CMD_RECEIVE: begin
                    resp_data[39 - bit_counter] <= cmd_in;
                    bit_counter <= bit_counter + 8'h1;
                end
                
                CMD_CHECK_CRC: begin
                    resp_crc <= resp_data[6:0];
                    calc_crc <= calc_crc7(resp_data[39:7], 7'h09);
                    crc_valid <= (calc_crc7(resp_data[39:7], 7'h09) == resp_data[6:0]);
                end
                
                CMD_COMPLETE: begin
                    cmd_response <= resp_data;
                    cmd_done <= 1'b1;
                    cmd_busy <= 1'b0;
                end
                
                CMD_ERROR: begin
                    cmd_crc_error <= 1'b1;
                    cmd_busy <= 1'b0;
                    error_clear <= 1'b1;
                end
                
                CMD_TIMEOUT: begin
                    cmd_timeout <= 1'b1;
                    cmd_busy <= 1'b0;
                    error_clear <= 1'b1;
                end
                
                CMD_BUSY: begin
                    // Wait for card to release busy signal
                end
                
                default: begin
                    // No action
                end
            endcase
        end
    end
    
    // SD command line control
    assign sd_cmd_io = cmd_out_en ? cmd_out : 1'bz;
    assign cmd_in = sd_cmd_io;
    
    // Clock generation (shared with data engine)
    // This is handled by the clock generator module
    
    // Assertions for command protocol compliance
    // synthesis translate_off
    // VERILATOR_DISABLED: property cmd_start_condition;
    //     VERILATOR_DISABLED:         @(posedge PCLK_i) cmd_start |-> ##1 cmd_busy;
    // VERILATOR_DISABLED: endproperty
    
    // VERILATOR_DISABLED: property cmd_completion;
    //     VERILATOR_DISABLED:         @(posedge PCLK_i) cmd_busy |-> ##[1:1000] (cmd_done || cmd_timeout || cmd_crc_error);
    // VERILATOR_DISABLED: endproperty
    
    property cmd_timeout_valid;
        @(posedge PCLK_i) cmd_timeout |-> !cmd_done && !cmd_crc_error;
    endproperty
    
    property cmd_crc_error_valid;
        @(posedge PCLK_i) cmd_crc_error |-> !cmd_done && !cmd_timeout;
    endproperty
    
    // VERILATOR_DISABLED: cmd_start_condition_check: assert property (cmd_start_condition)
    //     else $error("Command start condition violation");
    
    // VERILATOR_DISABLED: cmd_completion_check: assert property (cmd_completion)
    //     else $error("Command completion violation");
    
    cmd_timeout_valid_check: assert property (cmd_timeout_valid)
        else $error("Command timeout validity violation");
    
    cmd_crc_error_valid_check: assert property (cmd_crc_error_valid)
        else $error("Command CRC error validity violation");
    // synthesis translate_on

endmodule 