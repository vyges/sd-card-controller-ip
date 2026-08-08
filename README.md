[![Vyges IP](https://img.shields.io/badge/ip-vyges--sd--card--controller-blue)](https://github.com/vyges/sd-card-controller-ip)
![License: Apache-2.0](https://img.shields.io/badge/License-Apache--2.0-blue.svg)
![Build](https://github.com/vyges/sd-card-controller-ip/actions/workflows/test.yml/badge.svg)

# SD Card Controller IP

A high-performance SD Card controller with APB interface supporting SD/SDHC/SDXC cards with SPI and SD modes, DMA support, and comprehensive error handling.

> ## ⚠️ Status: in development
>
> This IP is an early design and is not ready to be integrated. The feature and
> specification lists below describe the intended design; not all of it is
> implemented yet.
>
> In particular:
>
> - The **security, debug, and test controllers** are present in RTL but their
>   ports are tied off at the top level, so those features are inert today.
>   Security is designed to interface with separate cryptographic IP rather than
>   implement ciphers itself, and that connection has not been made.
> - **Performance, power, and reliability figures are design targets.** No timing,
>   power, or reliability characterisation has been run.
> - **Compliance and certification entries are targets**, not achieved
>   qualifications.
>
> The register map, pin list, and module descriptions in the documentation are
> generated from the RTL and are accurate.

## 🚀 Features

- **Protocol Support**: SD 1.0/1.1, SDHC 2.0, SDXC 3.0
- **Interface Modes**: SPI mode and SD mode operation
- **APB Interface**: Standard APB slave interface for easy integration
- **DMA Support**: Optional DMA controller for high-speed transfers
- **Security**: Hardware-based encryption and authentication
- **Power Management**: Dynamic voltage and frequency scaling
- **Debug Interface**: Comprehensive debugging and monitoring capabilities
- **Performance Monitoring**: Real-time performance metrics and optimization
- **Error Handling**: Robust error detection and recovery mechanisms
- **Calibration Support**: Automatic timing and signal calibration
- **Test Interface**: Built-in self-test and manufacturing test support
- **Performance**: 25MB/s (SD mode), 12.5MB/s (SPI mode) — design targets, not measured
- **Target Platforms**: ASIC (Sky130B) and FPGA (Xilinx, Intel)

## 📋 Specifications

- **Clock Frequency**: Up to 100MHz (APB), 50MHz (SD mode), 25MHz (SPI mode)
- **Data Transfer Rate**: Up to 25MB/s (SD mode), 12.5MB/s (SPI mode)
- **Command Response Time**: < 1μs typical
- **Block Transfer Time**: < 1ms per 512-byte block
- **Power Consumption**: < 50mW active, < 5mW idle
- **Security**: AES-256 encryption, SHA-256 authentication
- **Debug Interface**: Real-time monitoring and performance counters
- **Error Handling**: Comprehensive error detection and recovery
- **Test Coverage**: 95% functional coverage, 90% code coverage

## 🏗️ Architecture

The SD Card Controller consists of the following key modules:

- **APB Interface** (`sdcard_apb_interface`): Standard APB slave interface
- **Register File** (`sdcard_register_file`): Control and status register management
- **Command Engine** (`sdcard_command_engine`): SD command generation and response parsing
- **Data Engine** (`sdcard_data_engine`): Data block transmission/reception with CRC
- **Clock Generator** (`sdcard_clock_generator`): Configurable SD card clock generation
- **DMA Controller** (`sdcard_dma_controller`): Optional DMA support for high-speed transfers
- **Power Controller** (`sdcard_power_controller`): Dynamic power management and voltage scaling
- **Security Controller** (`sdcard_security_controller`): Hardware-based encryption and authentication
- **Debug Controller** (`sdcard_debug_controller`): Comprehensive debugging and monitoring
- **Test Controller** (`sdcard_test_controller`): Built-in self-test and manufacturing test support
- **Error Controller** (`sdcard_error_controller`): Robust error detection and recovery
- **Performance Controller** (`sdcard_performance_controller`): Real-time performance metrics
- **Calibration Controller** (`sdcard_calibration_controller`): Automatic timing and signal calibration
- **Interrupt Controller** (`sdcard_interrupt_controller`): Event-driven interrupt generation
- **Interface Module** (`sdcard_interface`): SD card physical interface management

## 📖 Documentation

- **[Design Specification](docs/sd_card_controller_design_spec.md)**: Complete design specification
- **[Architecture Guide](docs/architecture.md)**: Detailed architecture documentation with block diagrams
- **[Overview](docs/overview.md)**: High-level overview and use cases
- **[User Guide](docs/user_guide.md)**: Integration and usage instructions
- **[API Reference](docs/api_reference.md)**: Register map and programming interface
- **[Developer Guide](Developer_Guide.md)**: Development and integration guide

## 🔧 Quickstart

1. **Clone the repository:**
   ```bash
   git clone https://github.com/vyges/sd-card-controller-ip.git
   cd sd-card-controller-ip
   ```

2. **Initialize the project:**
   ```bash
   vyges init --interactive
   ```

3. **Run simulation tests:**
   ```bash
   vyges test --simulation
   ```

4. **Synthesize for ASIC:**
   ```bash
   vyges build --target asic
   ```

5. **Synthesize for FPGA:**
   ```bash
   vyges build --target fpga
   ```

## 🔌 Integration

### Basic Instantiation

Port names and widths are taken from `rtl/sdcard_controller.sv`.

```systemverilog
sdcard_controller #(
    .SDCARD_APB_ADDR_WIDTH  (16),
    .SDCARD_DATA_WIDTH      (4),
    .SDCARD_FIFO_DEPTH      (512),
    .SDCARD_DMA_ENABLE      (1'b1),
    .SDCARD_SPI_MODE_ENABLE (1'b1)
) sdcard_ctrl (
    // APB slave
    .PCLK_i        (system_clk),
    .PRESETn_i     (system_reset_n),
    .PSEL_i        (apb_psel),
    .PENABLE_i     (apb_penable),
    .PWRITE_i      (apb_pwrite),
    .PADDR_i       (apb_paddr),        // [SDCARD_APB_ADDR_WIDTH-1:0]
    .PWDATA_i      (apb_pwdata),
    .PRDATA_o      (apb_prdata),
    .PREADY_o      (apb_pready),
    .PSLVERR_o     (apb_pslverr),

    // SD card
    .sd_clk_o      (sd_clk),
    .sd_cmd_io     (sd_cmd),
    .sd_dat_io     (sd_dat),           // [SDCARD_DATA_WIDTH-1:0]
    .sd_cd_i       (sd_card_detect),
    .sd_wp_i       (sd_write_protect),
    .sd_pwr_en_o   (sd_power_enable),
    .sd_vdd_sel_o  (sd_voltage_select),

    // Interrupts, four separate lines
    .sd_irq_o      (sd_interrupt),
    .dma_irq_o     (dma_interrupt),
    .error_irq_o   (error_interrupt),
    .debug_irq_o   (debug_interrupt),

    // DMA
    .dma_req_o     (dma_req),
    .dma_ack_i     (dma_ack),
    .dma_addr_o    (dma_addr),
    .dma_len_o     (dma_len),
    .dma_we_o      (dma_we),
    .dma_burst_o   (dma_burst),
    .dma_cache_o   (dma_cache),

    // JTAG and trace
    .jtag_tck_i    (jtag_tck),
    .jtag_tms_i    (jtag_tms),
    .jtag_tdi_i    (jtag_tdi),
    .jtag_tdo_o    (jtag_tdo),
    .jtag_trst_n_i (jtag_trst_n),
    .trace_data_o  (trace_data),
    .trace_valid_o (trace_valid)
);
```

### Pinout Table

All 35 top-level ports. Bus widths shown as declared; `PADDR_i` and `sd_dat_io`
follow their parameters, with defaults of 16 and 4 bits.

| Pin Name | Direction | Type | Description |
| ---------- | ----------- | ------ | ------------- |
| PCLK_i | Input | Clock | APB clock |
| PRESETn_i | Input | Reset | APB reset, active low |
| PSEL_i | Input | Control | APB select |
| PENABLE_i | Input | Control | APB enable |
| PWRITE_i | Input | Control | APB write enable |
| PADDR_i[SDCARD_APB_ADDR_WIDTH-1:0] | Input | Address | APB address bus |
| PWDATA_i[31:0] | Input | Data | APB write data |
| PRDATA_o[31:0] | Output | Data | APB read data |
| PREADY_o | Output | Control | APB ready |
| PSLVERR_o | Output | Control | APB slave error |
| sd_clk_o | Output | Clock | SD card clock |
| sd_cmd_io | Bidirectional | Data | SD command line |
| sd_dat_io[SDCARD_DATA_WIDTH-1:0] | Bidirectional | Data | SD data lines |
| sd_cd_i | Input | Status | Card detect |
| sd_wp_i | Input | Status | Write protect |
| sd_pwr_en_o | Output | Control | SD card power enable |
| sd_vdd_sel_o | Output | Control | SD card voltage select |
| sd_irq_o | Output | Interrupt | SD card interrupt |
| dma_irq_o | Output | Interrupt | DMA transfer complete interrupt |
| error_irq_o | Output | Interrupt | Error condition interrupt |
| debug_irq_o | Output | Interrupt | Debug event interrupt |
| dma_req_o | Output | Control | DMA request |
| dma_ack_i | Input | Control | DMA acknowledge |
| dma_addr_o[31:0] | Output | Address | DMA address |
| dma_len_o[15:0] | Output | Control | DMA length |
| dma_we_o | Output | Control | DMA write enable |
| dma_burst_o | Output | Control | DMA burst mode |
| dma_cache_o[3:0] | Output | Control | DMA cache attributes |
| jtag_tck_i | Input | Debug | JTAG test clock |
| jtag_tms_i | Input | Debug | JTAG test mode select |
| jtag_tdi_i | Input | Debug | JTAG test data input |
| jtag_tdo_o | Output | Debug | JTAG test data output |
| jtag_trst_n_i | Input | Debug | JTAG test reset |
| trace_data_o[7:0] | Output | Debug | Trace data output |
| trace_valid_o | Output | Debug | Trace data valid |

### Register Map

Offsets from `rtl/sdcard_register_file.sv`. Base address is chosen by the
integrator; the IP decodes `0x000`–`0x05C` only. Bit-level detail is in
[docs/api_reference.md](docs/api_reference.md).

| Offset | Register | Access | Description |
| -------- | ---------- | -------- | ------------- |
| 0x000 | `SD_CTRL` | R/W | Control register |
| 0x004 | `SD_STATUS` | R | Status register |
| 0x008 | `SD_CMD` | R/W | Command register |
| 0x00C | `SD_ARG` | R/W | Command argument |
| 0x010 | `SD_RESP0` | R | Command response word 0 |
| 0x014 | `SD_RESP1` | R | Command response word 1 |
| 0x018 | `SD_RESP2` | R | Command response word 2 |
| 0x01C | `SD_RESP3` | R | Command response word 3 |
| 0x020 | `SD_DATA` | R/W | Data register |
| 0x024 | `SD_BLK_CNT` | R/W | Block count |
| 0x028 | `SD_BLK_SIZE` | R/W | Block size |
| 0x02C | `SD_TIMEOUT` | R/W | Timeout value |
| 0x030 | `SD_CLK_DIV` | R/W | Clock divider |
| 0x034 | `SD_INT_EN` | R/W | Interrupt enable |
| 0x038 | `SD_INT_STAT` | R | Interrupt status |
| 0x03C | `SD_DMA_CTRL` | R/W | DMA control |
| 0x040 | `SD_PWR_CTRL` | R/W | Power control |
| 0x044 | `SD_SEC_CTRL` | R/W | Security control |
| 0x048 | `SD_DEBUG_CTRL` | R/W | Debug control |
| 0x04C | `SD_TEST_CTRL` | R/W | Test control |
| 0x050 | `SD_ERROR_CTRL` | R/W | Error control |
| 0x054 | `SD_PERF_CTRL` | R/W | Performance control |
| 0x058 | `SD_CAL_CTRL` | R/W | Calibration control |
| 0x05C | `SD_VERSION` | R | Version, reads 0x0100_0000 |

## 🧪 Testing

The project includes comprehensive testbenches and verification infrastructure:

- **SystemVerilog Testbenches**: Complete testbenches for all 16 modules
- **Cocotb Python Testbenches**: Python-based verification for all modules
- **Unit Tests**: Individual module verification with coverage
- **Integration Tests**: Interface integration verification
- **Protocol Tests**: SD card protocol compliance testing
- **Performance Tests**: Timing and throughput verification
- **Error Tests**: Error injection and recovery testing
- **Security Tests**: Encryption and authentication verification
- **Automated Test Suite**: Comprehensive test automation script

### Test Infrastructure

- **Top-level Testbench**: `tb/sv_tb/sd_card_controller_tb.sv`
- **Module Testbenches**: 16 SystemVerilog testbenches in `tb/sv_tb/`
- **Cocotb Tests**: 16 Python testbenches in `tb/cocotb/`
- **Test Automation**: `test/run_tests.sh` with comprehensive validation
- **CI/CD Pipeline**: GitHub Actions with multiple simulators

### Running Tests

```bash
# Run comprehensive test suite
./test/run_tests.sh

# Run specific simulator tests
cd tb
make SIM=iverilog run
make SIM=verilator run
make SIM=cocotb run

# Run individual test categories
make test
make lint
make coverage
```

## 📦 Supported Platforms

### ASIC

- **PDK**: Sky130B
- **Tools**: OpenLane, Yosys, OpenROAD
- **Clock**: Up to 50MHz
- **Area**: ~0.05mm²

### FPGA

- **Boards**: Arty-A7-35, compatible with CFU Playground
- **Tools**: Vivado, Quartus
- **Clock**: Up to 100MHz
- **Resources**: ~2000 LUTs, ~1500 FFs, 2 BRAMs

## 🤝 Contributing

1. Fork the repository
2. Create a feature branch
3. Make your changes
4. Add tests for new functionality
5. Ensure all tests pass
6. Submit a pull request

## 📄 License

Apache-2.0 License - see [LICENSE](LICENSE) file for details.

**Important**: The Apache-2.0 license applies to the **hardware IP content** (RTL, documentation, testbenches, etc.) that you create using this template. The template structure, build processes, tooling workflows, and AI context/processing engine are provided as-is for your use but are not themselves licensed under Apache-2.0.

For detailed licensing information, see [LICENSE_SCOPE.md](LICENSE_SCOPE.md).

## 🙏 Acknowledgments

- Built with the Vyges IP development ecosystem
- Follows Vyges conventions for hardware IP development

---

*Built with ❤️ by the Vyges team*
