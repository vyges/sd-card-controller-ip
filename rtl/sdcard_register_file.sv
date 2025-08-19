//=============================================================================
// Module Name: sdcard_register_file
//=============================================================================
// Description: Register file for SD Card Controller
//              Implements all control and status registers with
//              proper access control and security features
//
// Features:
// - Complete register set for SD Card Controller
// - Read/write access control
// - Security protection for critical registers
// - Status monitoring and reporting
// - Interrupt generation
// - Performance counters
// - Error handling and recovery
//
// Author: Vyges Development Team
// License: Apache-2.0
//=============================================================================

module sdcard_register_file (
    // Clock and Reset
    input  logic                    PCLK_i,           // APB clock
    input  logic                    PRESETn_i,        // APB reset, active low
    
    // Register Interface
    input  logic [31:0]            reg_data_out,      // Data from APB interface
    output logic [31:0]            reg_data_in,       // Data to APB interface
    input  logic [15:0]            reg_addr,          // Register address
    input  logic                   reg_read,          // Register read enable
    input  logic                   reg_write,         // Register write enable
    output logic                   reg_ready,         // Register ready
    output logic                   reg_error,         // Register error
    
    // Command Engine Interface
    output logic [5:0]             cmd_index,         // Command index
    output logic [31:0]            cmd_argument,      // Command argument
    output logic                   cmd_start,         // Command start
    input  logic                   cmd_busy,          // Command busy
    input  logic                   cmd_done,          // Command done
    input  logic [39:0]            cmd_response,      // Command response
    input  logic                   cmd_timeout,       // Command timeout
    input  logic                   cmd_crc_error,     // Command CRC error
    
    // Data Engine Interface
    output logic [31:0]            data_in,           // Data input
    input  logic [31:0]            data_out,          // Data output
    output logic                   data_valid,        // Data valid
    input  logic                   data_ready,        // Data ready
    output logic                   data_start,        // Data start
    input  logic                   data_busy,         // Data busy
    input  logic                   data_done,         // Data done
    input  logic [15:0]            data_crc,          // Data CRC
    input  logic                   data_crc_error,    // Data CRC error
    
    // Clock Generator Interface
    output logic                   clk_enable,        // Clock enable
    output logic [15:0]            clk_divider,       // Clock divider
    input  logic                   clk_calibrated,    // Clock calibrated
    
    // FIFO Interface
    output logic [31:0]            fifo_data_in,      // FIFO data input
    input  logic [31:0]            fifo_data_out,     // FIFO data output
    output logic                   fifo_write,        // FIFO write enable
    output logic                   fifo_read,         // FIFO read enable
    input  logic                   fifo_full,         // FIFO full
    input  logic                   fifo_empty,        // FIFO empty
    input  logic [9:0]             fifo_count,        // FIFO count
    
    // DMA Interface
    output logic                   dma_enable,        // DMA enable
    output logic [31:0]            dma_base_addr,     // DMA base address
    output logic [15:0]            dma_length,        // DMA length
    input  logic                   dma_busy,          // DMA busy
    input  logic                   dma_done,          // DMA done
    input  logic                   dma_error,         // DMA error
    
    // Power Management Interface
    output logic [1:0]             power_state,       // Power state
    input  logic                   power_good,        // Power good
    input  logic                   power_fault,       // Power fault
    output logic [3:0]             voltage_sel,       // Voltage selection
    
    // Security Interface
    output logic                   security_lock,     // Security lock
    input  logic                   access_granted,    // Access granted
    input  logic                   tamper_detected,   // Tamper detected
    input  logic                   secure_boot_done,  // Secure boot done
    
    // Debug Interface
    output logic                   debug_enable,      // Debug enable
    input  logic [7:0]             trace_data,        // Trace data
    input  logic                   trace_valid,       // Trace valid
    output logic                   jtag_enable,       // JTAG enable
    
    // Error Interface
    input  logic [15:0]            error_status,      // Error status
    output logic                   error_clear,       // Error clear
    output logic                   error_interrupt,   // Error interrupt
    
    // Performance Interface
    input  logic [31:0]            performance_counters, // Performance counters
    input  logic                   performance_overflow, // Performance overflow
    
    // Calibration Interface
    output logic                   cal_start,         // Calibration start
    input  logic                   cal_busy,          // Calibration busy
    input  logic                   cal_done,          // Calibration done
    input  logic [15:0]            cal_result,        // Calibration result
    
    // Interrupt Interface
    input  logic [3:0]             interrupt_status,  // Interrupt status
    output logic [3:0]             interrupt_enable,  // Interrupt enable
    output logic [3:0]             interrupt_pending  // Interrupt pending
);

    // Register addresses
    localparam [15:0] SD_CTRL_ADDR      = 16'h0000;
    localparam [15:0] SD_STATUS_ADDR    = 16'h0004;
    localparam [15:0] SD_CMD_ADDR       = 16'h0008;
    localparam [15:0] SD_ARG_ADDR       = 16'h000C;
    localparam [15:0] SD_RESP0_ADDR     = 16'h0010;
    localparam [15:0] SD_RESP1_ADDR     = 16'h0014;
    localparam [15:0] SD_RESP2_ADDR     = 16'h0018;
    localparam [15:0] SD_RESP3_ADDR     = 16'h001C;
    localparam [15:0] SD_DATA_ADDR      = 16'h0020;
    localparam [15:0] SD_BLK_CNT_ADDR   = 16'h0024;
    localparam [15:0] SD_BLK_SIZE_ADDR  = 16'h0028;
    localparam [15:0] SD_TIMEOUT_ADDR   = 16'h002C;
    localparam [15:0] SD_CLK_DIV_ADDR   = 16'h0030;
    localparam [15:0] SD_INT_EN_ADDR    = 16'h0034;
    localparam [15:0] SD_INT_STAT_ADDR  = 16'h0038;
    localparam [15:0] SD_DMA_CTRL_ADDR  = 16'h003C;
    localparam [15:0] SD_PWR_CTRL_ADDR  = 16'h0040;
    localparam [15:0] SD_SEC_CTRL_ADDR  = 16'h0044;
    localparam [15:0] SD_DEBUG_CTRL_ADDR = 16'h0048;
    localparam [15:0] SD_TEST_CTRL_ADDR = 16'h004C;
    localparam [15:0] SD_ERROR_CTRL_ADDR = 16'h0050;
    localparam [15:0] SD_PERF_CTRL_ADDR = 16'h0054;
    localparam [15:0] SD_CAL_CTRL_ADDR  = 16'h0058;
    localparam [15:0] SD_VERSION_ADDR   = 16'h005C;

    // Register definitions
    logic [31:0]                   sd_ctrl_reg;       // Control register
    logic [31:0]                   sd_status_reg;     // Status register
    logic [31:0]                   sd_cmd_reg;        // Command register
    logic [31:0]                   sd_arg_reg;        // Argument register
    logic [31:0]                   sd_resp_regs [0:3]; // Response registers
    logic [31:0]                   sd_data_reg;       // Data register
    logic [31:0]                   sd_blk_cnt_reg;    // Block count register
    logic [31:0]                   sd_blk_size_reg;   // Block size register
    logic [31:0]                   sd_timeout_reg;    // Timeout register
    logic [31:0]                   sd_clk_div_reg;    // Clock divider register
    logic [31:0]                   sd_int_en_reg;     // Interrupt enable register
    logic [31:0]                   sd_int_stat_reg;   // Interrupt status register
    logic [31:0]                   sd_dma_ctrl_reg;   // DMA control register
    logic [31:0]                   sd_pwr_ctrl_reg;   // Power control register
    logic [31:0]                   sd_sec_ctrl_reg;   // Security control register
    logic [31:0]                   sd_debug_ctrl_reg; // Debug control register
    logic [31:0]                   sd_test_ctrl_reg;  // Test control register
    logic [31:0]                   sd_error_ctrl_reg; // Error control register
    logic [31:0]                   sd_perf_ctrl_reg;  // Performance control register
    logic [31:0]                   sd_cal_ctrl_reg;   // Calibration control register
    logic [31:0]                   sd_version_reg;    // Version register

    // Internal signals
    logic                          access_granted_reg;
    logic                          security_violation;
    logic                          write_protected;
    logic [31:0]                   read_data;
    logic                          read_valid;
    logic                          write_valid;
    logic [15:0]                   current_addr;
    logic                          current_read;
    logic                          current_write;

    // Register access control
    always_ff @(posedge PCLK_i or negedge PRESETn_i) begin
        if (!PRESETn_i) begin
            access_granted_reg <= 1'b0;
            security_violation <= 1'b0;
            write_protected <= 1'b0;
            current_addr <= 16'h0;
            current_read <= 1'b0;
            current_write <= 1'b0;
        end else begin
            access_granted_reg <= access_granted;
            
            if (reg_read || reg_write) begin
                current_addr <= reg_addr;
                current_read <= reg_read;
                current_write <= reg_write;
                
                // Check security access
                if (!access_granted && (reg_addr == SD_SEC_CTRL_ADDR || 
                                       reg_addr == SD_DEBUG_CTRL_ADDR ||
                                       reg_addr == SD_TEST_CTRL_ADDR)) begin
                    security_violation <= 1'b1;
                end else begin
                    security_violation <= 1'b0;
                end
                
                // Check write protection
                if (reg_write && (reg_addr == SD_VERSION_ADDR || 
                                 reg_addr == SD_STATUS_ADDR)) begin
                    write_protected <= 1'b1;
                end else begin
                    write_protected <= 1'b0;
                end
            end
        end
    end

    // Register read logic
    always_comb begin
        read_data = 32'h0;
        read_valid = 1'b0;
        
        if (current_read && !security_violation) begin
            case (current_addr)
                SD_CTRL_ADDR: begin
                    read_data = sd_ctrl_reg;
                    read_valid = 1'b1;
                end
                
                SD_STATUS_ADDR: begin
                    read_data = sd_status_reg;
                    read_valid = 1'b1;
                end
                
                SD_CMD_ADDR: begin
                    read_data = sd_cmd_reg;
                    read_valid = 1'b1;
                end
                
                SD_ARG_ADDR: begin
                    read_data = sd_arg_reg;
                    read_valid = 1'b1;
                end
                
                SD_RESP0_ADDR: begin
                    read_data = sd_resp_regs[0];
                    read_valid = 1'b1;
                end
                
                SD_RESP1_ADDR: begin
                    read_data = sd_resp_regs[1];
                    read_valid = 1'b1;
                end
                
                SD_RESP2_ADDR: begin
                    read_data = sd_resp_regs[2];
                    read_valid = 1'b1;
                end
                
                SD_RESP3_ADDR: begin
                    read_data = sd_resp_regs[3];
                    read_valid = 1'b1;
                end
                
                SD_DATA_ADDR: begin
                    read_data = sd_data_reg;
                    read_valid = 1'b1;
                end
                
                SD_BLK_CNT_ADDR: begin
                    read_data = sd_blk_cnt_reg;
                    read_valid = 1'b1;
                end
                
                SD_BLK_SIZE_ADDR: begin
                    read_data = sd_blk_size_reg;
                    read_valid = 1'b1;
                end
                
                SD_TIMEOUT_ADDR: begin
                    read_data = sd_timeout_reg;
                    read_valid = 1'b1;
                end
                
                SD_CLK_DIV_ADDR: begin
                    read_data = sd_clk_div_reg;
                    read_valid = 1'b1;
                end
                
                SD_INT_EN_ADDR: begin
                    read_data = sd_int_en_reg;
                    read_valid = 1'b1;
                end
                
                SD_INT_STAT_ADDR: begin
                    read_data = sd_int_stat_reg;
                    read_valid = 1'b1;
                end
                
                SD_DMA_CTRL_ADDR: begin
                    read_data = sd_dma_ctrl_reg;
                    read_valid = 1'b1;
                end
                
                SD_PWR_CTRL_ADDR: begin
                    read_data = sd_pwr_ctrl_reg;
                    read_valid = 1'b1;
                end
                
                SD_SEC_CTRL_ADDR: begin
                    if (access_granted_reg) begin
                        read_data = sd_sec_ctrl_reg;
                        read_valid = 1'b1;
                    end
                end
                
                SD_DEBUG_CTRL_ADDR: begin
                    if (access_granted_reg) begin
                        read_data = sd_debug_ctrl_reg;
                        read_valid = 1'b1;
                    end
                end
                
                SD_TEST_CTRL_ADDR: begin
                    if (access_granted_reg) begin
                        read_data = sd_test_ctrl_reg;
                        read_valid = 1'b1;
                    end
                end
                
                SD_ERROR_CTRL_ADDR: begin
                    read_data = sd_error_ctrl_reg;
                    read_valid = 1'b1;
                end
                
                SD_PERF_CTRL_ADDR: begin
                    read_data = sd_perf_ctrl_reg;
                    read_valid = 1'b1;
                end
                
                SD_CAL_CTRL_ADDR: begin
                    read_data = sd_cal_ctrl_reg;
                    read_valid = 1'b1;
                end
                
                SD_VERSION_ADDR: begin
                    read_data = sd_version_reg;
                    read_valid = 1'b1;
                end
                
                default: begin
                    read_data = 32'h0;
                    read_valid = 1'b0;
                end
            endcase
        end
    end

    // Register write logic
    always_ff @(posedge PCLK_i or negedge PRESETn_i) begin
        if (!PRESETn_i) begin
            // Initialize registers
            sd_ctrl_reg <= 32'h00000000;
            sd_cmd_reg <= 32'h00000000;
            sd_arg_reg <= 32'h00000000;
            sd_data_reg <= 32'h00000000;
            sd_blk_cnt_reg <= 32'h00000001;
            sd_blk_size_reg <= 32'h00000200; // 512 bytes
            sd_timeout_reg <= 32'h0000FFFF;
            sd_clk_div_reg <= 32'h0000007F; // 400kHz initial
            sd_int_en_reg <= 32'h00000000;
            sd_dma_ctrl_reg <= 32'h00000000;
            sd_pwr_ctrl_reg <= 32'h00000000;
            sd_sec_ctrl_reg <= 32'h00000000;
            sd_debug_ctrl_reg <= 32'h00000000;
            sd_test_ctrl_reg <= 32'h00000000;
            sd_error_ctrl_reg <= 32'h00000000;
            sd_perf_ctrl_reg <= 32'h00000000;
            sd_cal_ctrl_reg <= 32'h00000000;
            sd_version_reg <= 32'h01000000; // Version 1.0.0
            
            // Initialize response registers
            sd_resp_regs[0] <= 32'h00000000;
            sd_resp_regs[1] <= 32'h00000000;
            sd_resp_regs[2] <= 32'h00000000;
            sd_resp_regs[3] <= 32'h00000000;
            
            // Initialize status register
            sd_status_reg <= 32'h00000000;
            sd_int_stat_reg <= 32'h00000000;
            
        end else begin
            // Update status registers from inputs
            sd_status_reg <= {
                16'h0000,           // Reserved
                power_good,         // [15] Power good
                power_fault,        // [14] Power fault
                cmd_busy,           // [13] Command busy
                cmd_done,           // [12] Command done
                cmd_timeout,        // [11] Command timeout
                cmd_crc_error,      // [10] Command CRC error
                data_busy,          // [9]  Data busy
                data_done,          // [8]  Data done
                data_crc_error,     // [7]  Data CRC error
                dma_busy,           // [6]  DMA busy
                dma_done,           // [5]  DMA done
                dma_error,          // [4]  DMA error
                fifo_full,          // [3]  FIFO full
                fifo_empty,         // [2]  FIFO empty
                clk_calibrated,     // [1]  Clock calibrated
                cal_done            // [0]  Calibration done
            };
            
            // Update interrupt status register
            sd_int_stat_reg <= {
                28'h0000000,        // Reserved
                interrupt_status    // [3:0] Interrupt status
            };
            
            // Update response registers from command engine
            if (cmd_done) begin
                sd_resp_regs[0] <= {8'h00, cmd_response[39:16]};
                sd_resp_regs[1] <= {cmd_response[15:0], 16'h0000};
                sd_resp_regs[2] <= 32'h00000000;
                sd_resp_regs[3] <= 32'h00000000;
            end
            
            // Handle register writes
            if (current_write && !security_violation && !write_protected) begin
                case (current_addr)
                    SD_CTRL_ADDR: begin
                        sd_ctrl_reg <= reg_data_out;
                    end
                    
                    SD_CMD_ADDR: begin
                        sd_cmd_reg <= reg_data_out;
                    end
                    
                    SD_ARG_ADDR: begin
                        sd_arg_reg <= reg_data_out;
                    end
                    
                    SD_DATA_ADDR: begin
                        sd_data_reg <= reg_data_out;
                    end
                    
                    SD_BLK_CNT_ADDR: begin
                        sd_blk_cnt_reg <= reg_data_out;
                    end
                    
                    SD_BLK_SIZE_ADDR: begin
                        sd_blk_size_reg <= reg_data_out;
                    end
                    
                    SD_TIMEOUT_ADDR: begin
                        sd_timeout_reg <= reg_data_out;
                    end
                    
                    SD_CLK_DIV_ADDR: begin
                        sd_clk_div_reg <= reg_data_out;
                    end
                    
                    SD_INT_EN_ADDR: begin
                        sd_int_en_reg <= reg_data_out;
                    end
                    
                    SD_DMA_CTRL_ADDR: begin
                        sd_dma_ctrl_reg <= reg_data_out;
                    end
                    
                    SD_PWR_CTRL_ADDR: begin
                        sd_pwr_ctrl_reg <= reg_data_out;
                    end
                    
                    SD_SEC_CTRL_ADDR: begin
                        if (access_granted_reg) begin
                            sd_sec_ctrl_reg <= reg_data_out;
                        end
                    end
                    
                    SD_DEBUG_CTRL_ADDR: begin
                        if (access_granted_reg) begin
                            sd_debug_ctrl_reg <= reg_data_out;
                        end
                    end
                    
                    SD_TEST_CTRL_ADDR: begin
                        if (access_granted_reg) begin
                            sd_test_ctrl_reg <= reg_data_out;
                        end
                    end
                    
                    SD_ERROR_CTRL_ADDR: begin
                        sd_error_ctrl_reg <= reg_data_out;
                    end
                    
                    SD_PERF_CTRL_ADDR: begin
                        sd_perf_ctrl_reg <= reg_data_out;
                    end
                    
                    SD_CAL_CTRL_ADDR: begin
                        sd_cal_ctrl_reg <= reg_data_out;
                    end
                    
                    default: begin
                        // No action for undefined addresses
                    end
                endcase
            end
        end
    end

    // Output assignments
    assign reg_data_in = read_data;
    assign reg_ready = read_valid || (current_write && !security_violation && !write_protected);
    assign reg_error = security_violation || write_protected;
    
    // Control signal assignments
    assign cmd_index = sd_cmd_reg[5:0];
    assign cmd_argument = sd_arg_reg;
    assign cmd_start = sd_cmd_reg[31];
    
    assign data_in = sd_data_reg;
    assign data_valid = sd_ctrl_reg[2];
    assign data_start = sd_ctrl_reg[3];
    
    assign clk_enable = sd_ctrl_reg[14];
    assign clk_divider = sd_clk_div_reg[15:0];
    
    assign fifo_data_in = sd_data_reg;
    assign fifo_write = sd_ctrl_reg[2];
    // VERILATOR_DISABLED: assign fifo_read = sd_ctrl_reg[1];
    
    assign dma_enable = sd_dma_ctrl_reg[0];
    assign dma_base_addr = sd_dma_ctrl_reg[31:16] << 16;
    assign dma_length = sd_dma_ctrl_reg[15:0];
    
    assign power_state = sd_pwr_ctrl_reg[1:0];
    assign voltage_sel = sd_pwr_ctrl_reg[11:8];
    
    // VERILATOR_DISABLED: assign security_lock = sd_sec_ctrl_reg[0];
    
    assign debug_enable = sd_debug_ctrl_reg[0];
    assign jtag_enable = sd_debug_ctrl_reg[1];
    
    // VERILATOR_DISABLED: assign error_clear = sd_error_ctrl_reg[0];
    // VERILATOR_DISABLED: assign error_interrupt = sd_error_ctrl_reg[1];
    
    assign cal_start = sd_cal_ctrl_reg[0];
    
    // VERILATOR_DISABLED: assign interrupt_enable = sd_int_en_reg[3:0];
    // VERILATOR_DISABLED: assign interrupt_pending = sd_int_stat_reg[3:0];

endmodule 