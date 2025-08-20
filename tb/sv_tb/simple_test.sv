//=============================================================================
// Simple SD Card Controller Testbench
//=============================================================================
// Description: Basic testbench for SD Card Controller IP
// Author: Vyges AI
// Date: 2025
// License: MIT
//=============================================================================

`timescale 1ns/1ps

module simple_test;

  // Clock and reset signals
  logic PCLK_i;
  logic PRESETn_i;
  
  // APB interface signals
  logic        PSEL_i;
  logic        PENABLE_i;
  logic        PWRITE_i;
  logic [15:0] PADDR_i;
  logic [31:0] PWDATA_i;
  logic [31:0] PRDATA_o;
  logic        PREADY_o;
  logic        PSLVERR_o;
  
  // SD Card interface signals
  logic        sd_clk_o;
  logic        sd_cmd_io;
  logic [3:0]  sd_dat_io;
  logic        sd_cd_i;
  logic        sd_wp_i;
  logic        sd_pwr_en_o;
  logic        sd_vdd_sel_o;
  
  // Interrupt signals
  logic        sd_irq_o;
  logic        dma_irq_o;
  logic        error_irq_o;
  logic        debug_irq_o;
  
  // DMA interface signals
  logic        dma_req_o;
  logic        dma_ack_i;
  logic [31:0] dma_addr_o;
  logic [15:0] dma_len_o;
  logic        dma_we_o;
  logic        dma_burst_o;
  logic [3:0]  dma_cache_o;
  
  // Debug interface signals
  logic        jtag_tck_i;
  logic        jtag_tms_i;
  logic        jtag_tdi_i;
  logic        jtag_tdo_o;
  logic        jtag_trst_n_i;
  logic [7:0]  trace_data_o;
  logic        trace_valid_o;
  
  // Clock generation
  initial begin
    PCLK_i = 0;
    forever #5 PCLK_i = ~PCLK_i; // 100MHz clock
  end
  
  // Reset generation
  initial begin
    PRESETn_i = 0;
    #100 PRESETn_i = 1;
  end
  
  // DUT instantiation
  sdcard_controller dut (
    .PCLK_i       (PCLK_i),
    .PRESETn_i    (PRESETn_i),
    .PSEL_i       (PSEL_i),
    .PENABLE_i    (PENABLE_i),
    .PWRITE_i     (PWRITE_i),
    .PADDR_i      (PADDR_i),
    .PWDATA_i     (PWDATA_i),
    .PRDATA_o     (PRDATA_o),
    .PREADY_o     (PREADY_o),
    .PSLVERR_o    (PSLVERR_o),
    .sd_clk_o     (sd_clk_o),
    .sd_cmd_io    (sd_cmd_io),
    .sd_dat_io    (sd_dat_io),
    .sd_cd_i      (sd_cd_i),
    .sd_wp_i      (sd_wp_i),
    .sd_pwr_en_o  (sd_pwr_en_o),
    .sd_vdd_sel_o (sd_vdd_sel_o),
    .sd_irq_o     (sd_irq_o),
    .dma_irq_o    (dma_irq_o),
    .error_irq_o  (error_irq_o),
    .debug_irq_o  (debug_irq_o),
    .dma_req_o    (dma_req_o),
    .dma_ack_i    (dma_ack_i),
    .dma_addr_o   (dma_addr_o),
    .dma_len_o    (dma_len_o),
    .dma_we_o     (dma_we_o),
    .dma_burst_o  (dma_burst_o),
    .dma_cache_o  (dma_cache_o),
    .jtag_tck_i   (jtag_tck_i),
    .jtag_tms_i   (jtag_tms_i),
    .jtag_tdi_i   (jtag_tdi_i),
    .jtag_tdo_o   (jtag_tdo_o),
    .jtag_trst_n_i(jtag_trst_n_i),
    .trace_data_o (trace_data_o),
    .trace_valid_o(trace_valid_o)
  );
  
  // Test stimulus
  initial begin
    // Initialize signals
    PSEL_i = 0;
    PENABLE_i = 0;
    PWRITE_i = 0;
    PADDR_i = 0;
    PWDATA_i = 0;
    sd_cd_i = 1;      // Card detected
    sd_wp_i = 0;      // Write protect off
    dma_ack_i = 0;
    jtag_tck_i = 0;
    jtag_tms_i = 0;
    jtag_tdi_i = 0;
    jtag_trst_n_i = 1;
    
    // Wait for reset to complete
    wait(PRESETn_i);
    #100;
    
    $display("Starting SD Card Controller Test");
    
    // Test 1: Basic APB write
    $display("Test 1: Basic APB write");
    apb_write(16'h000, 32'h00000001); // Write to control register
    
    // Test 2: Basic APB read
    $display("Test 2: Basic APB read");
    apb_read(16'h000); // Read from control register
    
    // Test 3: Check SD card power
    $display("Test 3: Check SD card power");
    if (sd_pwr_en_o) begin
      $display("  SD card power enabled");
    end else begin
      $display("  SD card power disabled");
    end
    
    // Test 4: Check clock generation
    $display("Test 4: Check clock generation");
    if (sd_clk_o !== 1'b0 && sd_clk_o !== 1'b1) begin
      $display("  SD clock is toggling");
    end else begin
      $display("  SD clock is static");
    end
    
    // Run for additional time to observe behavior
    #1000;
    
    $display("All tests completed");
    $finish;
  end
  
  // APB write task
  task automatic apb_write(input logic [15:0] addr, input logic [31:0] data);
    @(posedge PCLK_i);
    PSEL_i = 1;
    PENABLE_i = 0;
    PWRITE_i = 1;
    PADDR_i = addr;
    PWDATA_i = data;
    @(posedge PCLK_i);
    PENABLE_i = 1;
    wait(PREADY_o);
    @(posedge PCLK_i);
    PSEL_i = 0;
    PENABLE_i = 0;
    $display("APB Write: addr=0x%04X, data=0x%08X", addr, data);
  endtask
  
  // APB read task
  task automatic apb_read(input logic [15:0] addr);
    @(posedge PCLK_i);
    PSEL_i = 1;
    PENABLE_i = 0;
    PWRITE_i = 0;
    PADDR_i = addr;
    @(posedge PCLK_i);
    PENABLE_i = 1;
    wait(PREADY_o);
    @(posedge PCLK_i);
    PSEL_i = 0;
    PENABLE_i = 0;
    $display("APB Read: addr=0x%04X, data=0x%08X", addr, PRDATA_o);
  endtask
  
  // Monitor interrupt
  always @(posedge sd_irq_o) begin
    $display("SD Interrupt asserted at time %0t", $time);
  end
  
  // Monitor DMA request
  always @(posedge dma_req_o) begin
    $display("DMA Request asserted at time %0t", $time);
  end
  
  // Waveform dumping
  initial begin
    $dumpfile("simple_test.vcd");
    $dumpvars(0, simple_test);
  end
  
  // Timeout
  initial begin
    #10000;
    $display("Simulation timeout");
    $finish;
  end

endmodule
