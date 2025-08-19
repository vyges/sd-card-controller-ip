//=============================================================================
// SD Card Controller Top-Level Testbench
//=============================================================================
// Description: Top-level testbench for SD Card Controller IP
// Author: Vyges AI
// Date: 2025
// License: MIT
//=============================================================================

`timescale 1ns/1ps

module sdcard_controller_tb;

  // Clock and reset signals
  logic clk_i;
  logic reset_n_i;
  
  // APB interface signals
  logic        psel_i;
  logic        penable_i;
  logic        pwrite_i;
  logic [11:0] paddr_i;
  logic [31:0] pwdata_i;
  logic [31:0] prdata_o;
  logic        pready_o;
  logic        pslverr_o;
  
  // SD Card interface signals
  logic        sdcard_clk_o;
  logic        sdcard_cmd_io;
  logic [3:0]  sdcard_data_io;
  logic        sdcard_cd_i;
  logic        sdcard_wp_i;
  
  // Interrupt signals
  logic        irq_o;
  
  // Debug interface signals
  logic        debug_clk_o;
  logic        debug_data_o;
  logic        debug_valid_o;
  
  // Test interface signals
  logic        test_mode_i;
  logic        test_clk_i;
  logic        test_data_i;
  logic        test_valid_i;
  
  // Clock generation
  initial begin
    clk_i = 0;
    forever #5 clk_i = ~clk_i; // 100MHz clock
  end
  
  // Reset generation
  initial begin
    reset_n_i = 0;
    #100 reset_n_i = 1;
  end
  
  // DUT instantiation
  sdcard_controller dut (
    .clk_i        (clk_i),
    .reset_n_i    (reset_n_i),
    .psel_i       (psel_i),
    .penable_i    (penable_i),
    .pwrite_i     (pwrite_i),
    .paddr_i      (paddr_i),
    .pwdata_i     (pwdata_i),
    .prdata_o     (prdata_o),
    .pready_o     (pready_o),
    .pslverr_o    (pslverr_o),
    .sdcard_clk_o     (sdcard_clk_o),
    .sdcard_cmd_io    (sdcard_cmd_io),
    .sdcard_data_io   (sdcard_data_io),
    .sdcard_cd_i      (sdcard_cd_i),
    .sdcard_wp_i      (sdcard_wp_i),
    .irq_o        (irq_o),
    .debug_clk_o  (debug_clk_o),
    .debug_data_o (debug_data_o),
    .debug_valid_o(debug_valid_o),
    .test_mode_i  (test_mode_i),
    .test_clk_i   (test_clk_i),
    .test_data_i  (test_data_i),
    .test_valid_i (test_valid_i)
  );
  
  // Test stimulus
  initial begin
    // Initialize signals
    psel_i = 0;
    penable_i = 0;
    pwrite_i = 0;
    paddr_i = 0;
    pwdata_i = 0;
    sdcard_cd_i = 1;  // Card detected
    sdcard_wp_i = 0;  // Write protect off
    test_mode_i = 0;
    test_clk_i = 0;
    test_data_i = 0;
    test_valid_i = 0;
    
    // Wait for reset to complete
    wait(reset_n_i);
    #100;
    
    // Test 1: Basic APB read/write
    $display("Test 1: Basic APB read/write");
    apb_write(12'h000, 32'h12345678);
    apb_read(12'h000);
    
    // Test 2: Register configuration
    $display("Test 2: Register configuration");
    apb_write(12'h004, 32'h00000001); // Enable controller
    apb_write(12'h008, 32'h00000001); // Set clock divider
    apb_write(12'h00C, 32'h00000000); // Clear status
    
    // Test 3: Command interface
    $display("Test 3: Command interface");
    apb_write(12'h010, 32'h00000040); // CMD0 (GO_IDLE_STATE)
    apb_write(12'h014, 32'h00000000); // No arguments
    apb_write(12'h018, 32'h00000001); // Start command
    
    // Wait for command completion
    wait_command_complete();
    
    // Test 4: Data transfer
    $display("Test 4: Data transfer");
    apb_write(12'h020, 32'h00000001); // Enable data transfer
    apb_write(12'h024, 32'h00000100); // Set block size (256 bytes)
    apb_write(12'h028, 32'h00000001); // Single block transfer
    
    // Test 5: Interrupt handling
    $display("Test 5: Interrupt handling");
    apb_write(12'h030, 32'h00000001); // Enable interrupts
    
    // Test 6: Power management
    $display("Test 6: Power management");
    apb_write(12'h040, 32'h00000001); // Enable power management
    
    // Test 7: Security features
    $display("Test 7: Security features");
    apb_write(12'h050, 32'h00000001); // Enable security
    
    // Test 8: Debug interface
    $display("Test 8: Debug interface");
    apb_write(12'h060, 32'h00000001); // Enable debug
    
    // Test 9: Performance monitoring
    $display("Test 9: Performance monitoring");
    apb_write(12'h070, 32'h00000001); // Enable performance monitoring
    
    // Test 10: Error handling
    $display("Test 10: Error handling");
    apb_write(12'h080, 32'h00000001); // Enable error reporting
    
    // Run for additional time to observe behavior
    #1000;
    
    $display("All tests completed");
    $finish;
  end
  
  // APB write task
  task automatic apb_write(input logic [11:0] addr, input logic [31:0] data);
    @(posedge clk_i);
    psel_i = 1;
    penable_i = 0;
    pwrite_i = 1;
    paddr_i = addr;
    pwdata_i = data;
    @(posedge clk_i);
    penable_i = 1;
    wait(pready_o);
    @(posedge clk_i);
    psel_i = 0;
    penable_i = 0;
    $display("APB Write: addr=0x%03X, data=0x%08X", addr, data);
  endtask
  
  // APB read task
  task automatic apb_read(input logic [11:0] addr);
    @(posedge clk_i);
    psel_i = 1;
    penable_i = 0;
    pwrite_i = 0;
    paddr_i = addr;
    @(posedge clk_i);
    penable_i = 1;
    wait(pready_o);
    @(posedge clk_i);
    psel_i = 0;
    penable_i = 0;
    $display("APB Read: addr=0x%03X, data=0x%08X", addr, prdata_o);
  endtask
  
  // Wait for command completion
  task automatic wait_command_complete();
    logic [31:0] status;
    do begin
      apb_read(12'h00C); // Read status register
      status = prdata_o;
      #10;
    end while ((status & 32'h00000001) == 0); // Wait for command done bit
    $display("Command completed");
  endtask
  
  // Monitor interrupt
  always @(posedge irq_o) begin
    $display("Interrupt asserted at time %0t", $time);
  end
  
  // Monitor debug output
  always @(posedge debug_valid_o) begin
    $display("Debug data: 0x%02X at time %0t", debug_data_o, $time);
  end
  
  // Waveform dumping
  initial begin
    $dumpfile("sdcard_card_controller_tb.vcd");
    $dumpvars(0, sdcard_card_controller_tb);
  end
  
  // Timeout
  initial begin
    #10000;
    $display("Simulation timeout");
    $finish;
  end

endmodule 