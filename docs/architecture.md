# Architecture: SD Card Controller IP

## Overview

This document describes the internal architecture, interfaces, and design details of the SD Card Controller IP. The controller supports SD/SDHC/SDXC cards with both SPI and SD modes, includes comprehensive power management, security features, debug capabilities, and DMA support.

---

## Block Diagram

```
                    SD Card Controller Architecture
                    ===============================

┌─────────────────────────────────────────────────────────────────────────────┐
│                           SD Card Controller                                │
├─────────────────────────────────────────────────────────────────────────────┤
│                                                                             │
│  ┌─────────────────┐    ┌─────────────────┐    ┌─────────────────┐        │
│  │   APB Interface │    │  Command Engine │    │   Data Engine   │        │
│  │                 │    │                 │    │                 │        │
│  │ PCLK_i         │    │ CMD Generation   │    │ Data TX/RX      │        │
│  │ PRESETn_i      │    │ Response Parse   │    │ CRC Gen/Check   │        │
│  │ PSEL_i         │    │ Timeout Handle   │    │ FIFO Control    │        │
│  │ PENABLE_i      │    │ State Machine    │    │ Block Control   │        │
│  │ PWRITE_i       │    │ Error Handling   │    │ DMA Interface   │        │
│  │ PADDR_i[15:0]  │    │ Protocol Check   │    │ Performance Opt │        │
│  │ PWDATA_i[31:0] │    │                 │    │                 │        │
│  │ PRDATA_o[31:0] │    │                 │    │                 │        │
│  │ PREADY_o       │    │                 │    │                 │        │
│  │ PSLVERR_o      │    │                 │    │                 │        │
│  └─────────────────┘    └─────────────────┘    └─────────────────┘        │
│           │                       │                       │                │
│           │                       │                       │                │
│           ▼                       ▼                       ▼                │
│  ┌─────────────────┐    ┌─────────────────┐    ┌─────────────────┐        │
│  │  Register File  │    │   Clock Gen     │    │   Data FIFO     │        │
│  │                 │    │                 │    │                 │        │
│  │ SD_CTRL         │    │ Configurable    │    │ TX FIFO         │        │
│  │ SD_STATUS       │    │ Clock Divider   │    │ RX FIFO         │        │
│  │ SD_CMD          │    │ Enable/Disable  │    │ Flow Control    │        │
│  │ SD_ARG          │    │ Frequency Scale │    │ Status Flags    │        │
│  │ SD_RESP[0:3]    │    │ Calibration     │    │ Error Handling  │        │
│  │ SD_DATA         │    │                 │    │                 │        │
│  │ SD_BLK_CNT      │    │                 │    │                 │        │
│  │ SD_BLK_SIZE     │    │                 │    │                 │        │
│  │ SD_TIMEOUT      │    │                 │    │                 │        │
│  │ SD_CLK_DIV      │    │                 │    │                 │        │
│  │ SD_INT_EN       │    │                 │    │                 │        │
│  │ SD_INT_STAT     │    │                 │    │                 │        │
│  │ SD_DMA_CTRL     │    │                 │    │                 │        │
│  │ SD_PWR_CTRL     │    │                 │    │                 │        │
│  │ SD_SEC_CTRL     │    │                 │    │                 │        │
│  │ SD_DEBUG_CTRL   │    │                 │    │                 │        │
│  │ SD_TEST_CTRL    │    │                 │    │                 │        │
│  │ SD_ERROR_CTRL   │    │                 │    │                 │        │
│  │ SD_PERF_CTRL    │    │                 │    │                 │        │
│  │ SD_CAL_CTRL     │    │                 │    │                 │        │
│  │ SD_VERSION      │    │                 │    │                 │        │
│  └─────────────────┘    └─────────────────┘    └─────────────────┘        │
│           │                       │                       │                │
│           │                       │                       │                │
│           ▼                       ▼                       ▼                │
│  ┌─────────────────┐    ┌─────────────────┐    ┌─────────────────┐        │
│  │  Interrupt Ctrl │    │   SD Interface  │    │   DMA Controller│        │
│  │                 │    │                 │    │                 │        │
│  │ IRQ Generation  │    │ Signal Control  │    │ DMA Request     │        │
│  │ Status Monitor  │    │ Tri-state Ctrl  │    │ Address Gen     │        │
│  │ Edge Detection  │    │ Level Shifting  │    │ Length Control  │        │
│  │ Mask Control    │    │ Timing Control  │    │ Burst Control   │        │
│  │ Priority Ctrl   │    │ Power Control   │    │ Cache Control   │        │
│  └─────────────────┘    └─────────────────┘    └─────────────────┘        │
│           │                       │                       │                │
│           │                       │                       │                │
│           ▼                       ▼                       ▼                │
│  ┌─────────────────┐    ┌─────────────────┐    ┌─────────────────┐        │
│  │ Power Controller│    │ Security Ctrl   │    │ Debug Controller│        │
│  │                 │    │                 │    │                 │        │
│  │ Power State Mgmt│    │ Access Control  │    │ JTAG Interface  │        │
│  │ Power Sequencing│    │ Secure Boot     │    │ Trace Generation│        │
│  │ Voltage Monitor │    │ Tamper Detection│    │ Debug Events    │        │
│  │ Power Fault Det │    │ Encryption      │    │ Test Access     │        │
│  │ Power Optimize  │    │ Security Logging│    │ Debug Data Coll │        │
│  └─────────────────┘    └─────────────────┘    └─────────────────┘        │
│           │                       │                       │                │
│           │                       │                       │                │
│           ▼                       ▼                       ▼                │
│  ┌─────────────────┐    ┌─────────────────┐    ┌─────────────────┐        │
│  │ Test Controller │    │ Error Controller│    │ Performance Ctrl│        │
│  │                 │    │                 │    │                 │        │
│  │ BIST Control    │    │ Error Detection │    │ Performance Mon │        │
│  │ Scan Chain Ctrl │    │ Error Recovery  │    │ Performance Opt │        │
│  │ Test Mode Ctrl  │    │ Error Reporting │    │ Performance Tune│        │
│  │ Test Coverage   │    │ Error Prevention│    │ Performance Adapt│       │
│  └─────────────────┘    └─────────────────┘    └─────────────────┘        │
│           │                       │                       │                │
└───────────┼───────────────────────┼───────────────────────┼────────────────┘
            │                       │                       │
            │                       │                       │
            ▼                       ▼                       ▼
    ┌─────────────┐         ┌─────────────┐         ┌─────────────┐
    │   APB Bus   │         │   SD Card   │         │   DMA Bus   │
    │             │         │             │         │             │
    │ PCLK        │         │ sd_clk_o    │         │ dma_req_o   │
    │ PRESETn     │         │ sd_cmd_io   │         │ dma_ack_i   │
    │ PSEL        │         │ sd_dat_io   │         │ dma_addr_o  │
    │ PENABLE     │         │ sd_cd_i     │         │ dma_len_o   │
    │ PWRITE      │         │ sd_wp_i     │         │ dma_we_o    │
    │ PADDR       │         │ sd_pwr_en_o │         │ dma_burst_o │
    │ PWDATA      │         │ sd_vdd_sel_o│         │ dma_cache_o │
    │ PRDATA      │         │             │         │             │
    │ PREADY      │         │             │         │             │
    │ PSLVERR     │         │             │         │             │
    └─────────────┘         └─────────────┘         └─────────────┘
            │                       │                       │
            │                       │                       │
            ▼                       ▼                       ▼
    ┌─────────────┐         ┌─────────────┐         ┌─────────────┐
    │ Interrupts  │         │ Debug I/F   │         │ Power I/F   │
    │             │         │             │         │             │
    │ sd_irq_o    │         │ jtag_tck_i  │         │ Power Domains│
    │ dma_irq_o   │         │ jtag_tms_i  │         │ Core Domain │
    │ error_irq_o │         │ jtag_tdi_i  │         │ I/O Domain  │
    │ debug_irq_o │         │ jtag_tdo_o  │         │ SD Domain   │
    │             │         │ jtag_trst_n │         │ Clock Domain│
    │             │         │ trace_data_o│         │             │
    │             │         │ trace_valid_o│        │             │
    └─────────────┘         └─────────────┘         └─────────────┘
```

---

## Parameters

| Parameter | Type | Default | Description |
|-----------|------|---------|-------------|
| `APB_ADDR_WIDTH` | int | 16 | Width of APB address bus |
| `SD_DATA_WIDTH` | int | 4 | SD card data width (1, 4, or 8 bits) |
| `FIFO_DEPTH` | int | 512 | FIFO depth for data buffering |
| `DMA_ENABLE` | bool | true | Enable DMA support |
| `SPI_MODE_ENABLE` | bool | true | Enable SPI mode support |

---

## Interfaces

### APB Slave Interface

| Signal | Direction | Width | Description |
|--------|-----------|-------|-------------|
| `PCLK_i` | input | 1 | APB clock |
| `PRESETn_i` | input | 1 | APB reset, active low |
| `PSEL_i` | input | 1 | APB select |
| `PENABLE_i` | input | 1 | APB enable |
| `PWRITE_i` | input | 1 | APB write enable |
| `PADDR_i` | input | 16 | APB address bus |
| `PWDATA_i` | input | 32 | APB write data |
| `PRDATA_o` | output | 32 | APB read data |
| `PREADY_o` | output | 1 | APB ready |
| `PSLVERR_o` | output | 1 | APB slave error |

### SD Card Interface

| Signal | Direction | Width | Description |
|--------|-----------|-------|-------------|
| `sd_clk_o` | output | 1 | SD card clock |
| `sd_cmd_io` | bidir | 1 | SD command line |
| `sd_dat_io` | bidir | 4 | SD data lines |
| `sd_cd_i` | input | 1 | Card detect |
| `sd_wp_i` | input | 1 | Write protect |
| `sd_pwr_en_o` | output | 1 | SD card power enable |
| `sd_vdd_sel_o` | output | 1 | SD card voltage select |

### Interrupt Interface

| Signal | Direction | Width | Description |
|--------|-----------|-------|-------------|
| `sd_irq_o` | output | 1 | SD card interrupt |
| `dma_irq_o` | output | 1 | DMA transfer complete interrupt |
| `error_irq_o` | output | 1 | Error condition interrupt |
| `debug_irq_o` | output | 1 | Debug event interrupt |

### DMA Interface (Optional)

| Signal | Direction | Width | Description |
|--------|-----------|-------|-------------|
| `dma_req_o` | output | 1 | DMA request |
| `dma_ack_i` | input | 1 | DMA acknowledge |
| `dma_addr_o` | output | 32 | DMA address |
| `dma_len_o` | output | 16 | DMA length |
| `dma_we_o` | output | 1 | DMA write enable |
| `dma_burst_o` | output | 1 | DMA burst mode |
| `dma_cache_o` | output | 4 | DMA cache attributes |

### Debug Interface

| Signal | Direction | Width | Description |
|--------|-----------|-------|-------------|
| `jtag_tck_i` | input | 1 | JTAG test clock |
| `jtag_tms_i` | input | 1 | JTAG test mode select |
| `jtag_tdi_i` | input | 1 | JTAG test data input |
| `jtag_tdo_o` | output | 1 | JTAG test data output |
| `jtag_trst_n_i` | input | 1 | JTAG test reset |
| `trace_data_o` | output | 8 | Trace data output |
| `trace_valid_o` | output | 1 | Trace data valid |

---

## Register Map

| Address | Register Name | Access | Description |
|---------|---------------|--------|-------------|
| 0x00 | SD_CTRL | R/W | Control register |
| 0x04 | SD_STATUS | R | Status register |
| 0x08 | SD_CMD | R/W | Command register |
| 0x0C | SD_ARG | R/W | Command argument |
| 0x10 | SD_RESP[0] | R | Response register 0 |
| 0x14 | SD_RESP[1] | R | Response register 1 |
| 0x18 | SD_RESP[2] | R | Response register 2 |
| 0x1C | SD_RESP[3] | R | Response register 3 |
| 0x20 | SD_DATA | R/W | Data register |
| 0x24 | SD_BLK_CNT | R/W | Block count register |
| 0x28 | SD_BLK_SIZE | R/W | Block size register |
| 0x2C | SD_TIMEOUT | R/W | Timeout register |
| 0x30 | SD_CLK_DIV | R/W | Clock divider register |
| 0x34 | SD_INT_EN | R/W | Interrupt enable register |
| 0x38 | SD_INT_STAT | R/W | Interrupt status register |
| 0x3C | SD_DMA_CTRL | R/W | DMA control register |
| 0x40 | SD_PWR_CTRL | R/W | Power control register |
| 0x44 | SD_SEC_CTRL | R/W | Security control register |
| 0x48 | SD_DEBUG_CTRL | R/W | Debug control register |
| 0x4C | SD_TEST_CTRL | R/W | Test control register |
| 0x50 | SD_ERROR_CTRL | R/W | Error control register |
| 0x54 | SD_PERF_CTRL | R/W | Performance control register |
| 0x58 | SD_CAL_CTRL | R/W | Calibration control register |
| 0x5C | SD_VERSION | R | Version register |

---

## Internal Modules

### Core Functional Modules

- **APB Interface**: Implements APB3 slave protocol with error handling
- **Command Engine**: Handles SD command generation, transmission, and response parsing
- **Data Engine**: Manages data block transmission/reception with CRC checking
- **Clock Generator**: Provides configurable SD card clock with calibration
- **FIFO Controller**: Manages data buffering with flow control
- **CRC Generator**: Implements CRC7 for commands and CRC16 for data
- **DMA Controller**: Optional DMA support for high-speed transfers

### Power Management Modules

- **Power Controller**: Manages power states and power sequencing
- **Voltage Monitor**: Monitors voltage levels and detects faults
- **Power Optimizer**: Optimizes power consumption based on usage

### Security Modules

- **Security Controller**: Implements access control and secure boot
- **Tamper Detection**: Detects hardware, clock, voltage, and temperature tampering
- **Encryption Engine**: Optional data encryption support
- **Security Logger**: Logs security events and access attempts

### Debug and Test Modules

- **Debug Controller**: Manages JTAG interface and trace generation
- **Test Controller**: Implements BIST, scan chains, and test modes
- **Error Controller**: Handles error detection, recovery, and reporting
- **Performance Controller**: Monitors and optimizes performance

### Support Modules

- **Interrupt Controller**: Manages interrupt generation and prioritization
- **SD Interface**: Handles SD card signal control and timing
- **Calibration Controller**: Manages clock and timing calibration

---

## Clock Domains

### Primary Clock Domains

- **APB Clock (PCLK_i)**: 50MHz - 100MHz, used by APB interface and core logic
- **SD Card Clock (sd_clk_o)**: 400kHz - 50MHz, configurable for SD card operation
- **Debug Clock**: Independent debug clock domain for JTAG and trace

### Clock Domain Crossing

- **APB ↔ Internal**: Synchronizer and handshake mechanisms
- **Internal ↔ SD**: FIFO-based crossing with proper timing
- **Debug ↔ Core**: Dedicated debug clock domain with synchronization

---

## Power Domains

### Power Domain Structure

- **Core Domain**: Main controller logic (1.2V nominal)
- **I/O Domain**: APB and SD card interfaces (3.3V nominal)
- **SD Card Domain**: SD card power supply (3.3V nominal)
- **Clock Domain**: Clock generation circuits (1.2V nominal)

### Power States

- **Active State**: Full functionality, 50mW typical power consumption
- **Idle State**: Reduced functionality, 5mW typical power consumption
- **Sleep State**: Minimal functionality, 1mW typical power consumption
- **Power-down State**: Complete shutdown, <100μW power consumption

---

## State Machine

### Main Controller States

```
┌─────────────┐    ┌─────────────┐    ┌─────────────┐    ┌─────────────┐
│   IDLE      │───▶│  INIT       │───▶│  READY      │───▶│  CMD        │
│             │    │             │    │             │    │  SEND       │
│ - Wait for  │    │ - Power up  │    │ - Wait for  │    │             │
│   command   │    │ - Clock     │    │   command   │    │ - Send      │
│ - Reset     │    │   enable    │    │ - Card      │    │   command   │
│   state     │    │ - Card      │    │   ready     │    │ - Wait for  │
│             │    │   detect    │    │             │    │   response  │
└─────────────┘    └─────────────┘    └─────────────┘    └─────────────┘
       ▲                   │                   │                   │
       │                   │                   │                   │
       │                   ▼                   ▼                   ▼
       │            ┌─────────────┐    ┌─────────────┐    ┌─────────────┐
       │            │   ERROR     │    │   DATA      │    │  RESPONSE   │
       │            │             │    │  TRANSFER   │    │  RECEIVE    │
       │            │ - Error     │    │             │    │             │
       │            │   handling  │    │ - Read/     │    │ - Receive   │
       │            │ - Status    │    │   Write     │    │   response  │
       │            │   report    │    │   data      │    │ - Parse     │
       │            │ - Recovery  │    │ - CRC check │    │   response  │
       │            │             │    │ - DMA xfer  │    │ - Check     │
       │            └─────────────┘    └─────────────┘    │   status    │
       │                       ▲                   │                   │
       │                       │                   │                   │
       └───────────────────────┼───────────────────┼───────────────────┘
                               │                   │
                               ▼                   ▼
                       ┌─────────────┐    ┌─────────────┐
                       │   BUSY      │    │  COMPLETE   │
                       │             │    │             │
                       │ - Wait for  │    │ - Command   │
                       │   card      │    │   complete  │
                       │   ready     │    │ - Update    │
                       │ - Timeout   │    │   status    │
                       │   check     │    │ - Generate  │
                       │             │    │   interrupt │
                       └─────────────┘    └─────────────┘
```

---

## Signal Flow Diagram

### APB Interface Flow

```
                    SD Card Controller Signal Flow
                    ===============================

APB Interface Flow:
┌─────────┐    ┌─────────────┐    ┌─────────────┐    ┌─────────────┐
│  APB    │───▶│   APB       │───▶│  Register   │───▶│  Control    │
│  Master │    │  Interface  │    │   File      │    │  Logic      │
└─────────┘    └─────────────┘    └─────────────┘    └─────────────┘
     ▲                │                   │                   │
     │                │                   │                   │
     └────────────────┼───────────────────┼───────────────────┘
                      │                   │                   │
                      ▼                   ▼                   ▼
               ┌─────────────┐    ┌─────────────┐    ┌─────────────┐
               │  Interrupt  │    │  Command    │    │   Data      │
               │  Controller │    │  Engine     │    │  Engine     │
               └─────────────┘    └─────────────┘    └─────────────┘
                      │                   │                   │
                      ▼                   ▼                   ▼
               ┌─────────────┐    ┌─────────────┐    ┌─────────────┐
               │   IRQ       │    │   SD        │    │   DMA       │
               │  Outputs    │    │  Interface  │    │  Controller │
               └─────────────┘    └─────────────┘    └─────────────┘
                      │                   │                   │
                      ▼                   ▼                   ▼
               ┌─────────────┐    ┌─────────────┐    ┌─────────────┐
               │ sd_irq_o    │    │ sd_clk_o    │    │ dma_req_o   │
               │ dma_irq_o   │    │ sd_cmd_io   │    │ dma_ack_i   │
               └─────────────┘    │ sd_dat_io   │    │ dma_addr_o  │
                                  │ sd_cd_i     │    │ dma_len_o   │
                                  │ sd_wp_i     │    │ dma_we_o    │
                                  └─────────────┘    └─────────────┘
```

---

## Clock Domain Diagram

### Clock Domain Distribution

```
                    Clock Domain Distribution
                    =========================

┌─────────────────────────────────────────────────────────────────────────────┐
│                           Clock Domains                                    │
├─────────────────────────────────────────────────────────────────────────────┤
│                                                                             │
│  ┌─────────────────┐    ┌─────────────────┐    ┌─────────────────┐        │
│  │   APB Clock     │    │   SD Card Clock │    │  Internal Clock │        │
│  │   (PCLK_i)      │    │   (sd_clk_o)    │    │   (PCLK_i)      │        │
│  │                 │    │                 │    │                 │        │
│  │ Frequency:      │    │ Frequency:      │    │ Frequency:      │        │
│  │ 50-100 MHz      │    │ 400kHz-50MHz    │    │ 50-100 MHz      │        │
│  │                 │    │                 │    │                 │        │
│  │ Used by:        │    │ Used by:        │    │ Used by:        │        │
│  │ - APB Interface │    │ - SD Interface  │    │ - Command Engine│        │
│  │ - Register File │    │ - Data Engine   │    │ - Data Engine   │        │
│  │ - Interrupt Ctrl│    │ - Clock Gen     │    │ - DMA Controller│        │
│  │ - DMA Controller│    │                 │    │ - Interrupt Ctrl│        │
│  └─────────────────┘    └─────────────────┘    └─────────────────┘        │
│           │                       │                       │                │
│           │                       │                       │                │
│           ▼                       ▼                       ▼                │
│  ┌─────────────────┐    ┌─────────────────┐    ┌─────────────────┐        │
│  │ Clock Domain    │    │ Clock Domain    │    │ Clock Domain    │        │
│  │ Crossing        │    │ Crossing        │    │ Crossing        │        │
│  │ (APB ↔ Internal)│    │ (Internal ↔ SD) │    │ (SD ↔ APB)      │        │
│  │                 │    │                 │    │                 │        │
│  │ - Synchronizer  │    │ - Synchronizer  │    │ - Synchronizer  │        │
│  │ - Handshake     │    │ - Handshake     │    │ - Handshake     │        │
│  │ - FIFO          │    │ - FIFO          │    │ - FIFO          │        │
│  └─────────────────┘    └─────────────────┘    └─────────────────┘        │
└─────────────────────────────────────────────────────────────────────────────┘
```

---

## Performance Characteristics

### Timing Specifications

- **APB Clock**: 50MHz - 100MHz operation
- **SD Card Clock**: 400kHz - 50MHz configurable
- **Command Response**: < 100μs typical
- **Data Transfer**: < 1ms per 512-byte block
- **Interrupt Latency**: < 10μs

### Throughput Specifications

- **Sustained Transfer Rate**: 20MB/s minimum
- **Burst Transfer Rate**: 25MB/s maximum
- **Command Processing**: 1000 commands/second
- **Queue Depth**: Up to 8 pending commands

### Power Specifications

- **Active Power**: 50mW typical, 75mW maximum
- **Idle Power**: 5mW typical, 10mW maximum
- **Sleep Power**: 1mW typical, 2mW maximum
- **Power-down**: < 100μW

---

## Security Features

### Access Control

- **Register Protection**: Critical registers protected by access control
- **Privilege Levels**: User and supervisor privilege levels
- **Secure Access**: Secure access to configuration registers
- **Lock Mechanisms**: Register lock/unlock mechanisms

### Tamper Detection

- **Hardware Tamper**: Physical tamper detection
- **Clock Tamper**: Clock frequency tamper detection
- **Voltage Tamper**: Voltage level tamper detection
- **Temperature Tamper**: Temperature range tamper detection

### Secure Boot

- **Secure Initialization**: Secure boot sequence validation
- **Integrity Check**: Firmware integrity verification
- **Authentication**: Secure authentication mechanisms
- **Key Management**: Secure key storage and management

---

## Debug and Test Features

### Debug Interface

- **JTAG Support**: IEEE 1149.1 compliant JTAG interface
- **Trace Output**: Real-time trace for command/response and data transfer
- **Debug Registers**: Debug control and status registers
- **Breakpoint Support**: Hardware breakpoint capabilities

### Test Features

- **Built-in Self-Test**: Memory, logic, interface, and clock BIST
- **Scan Chains**: Full scan chain implementation for DFT
- **Test Modes**: Multiple test mode configurations
- **Test Coverage**: >95% fault coverage target

---

## Compliance and Standards

### SD Association Compliance

- **SD Host Controller Specification**: Version 2.0 compliance
- **SD Memory Card Specification**: Version 3.0 compliance
- **SDIO Specification**: Version 2.0 compliance
- **Test Compliance**: SD Association test suite compliance

### Industry Standards

- **IEEE 1149.1**: JTAG boundary scan compliance
- **IEEE 1500**: Embedded core test compliance
- **IEEE 1800**: SystemVerilog standard compliance

### Safety Standards

- **ISO 26262**: Automotive functional safety (ASIL-B)
- **IEC 61508**: Industrial functional safety (SIL-2)
- **IEC 60730**: Household appliance safety

### Environmental Compliance

- **RoHS**: Restriction of Hazardous Substances compliance
- **REACH**: Registration, Evaluation, Authorization of Chemicals
- **WEEE**: Waste Electrical and Electronic Equipment

---

## Notes

- Reset (`PRESETn_i`) clears all registers and control logic
- Interrupt signals are level-high and should be cleared via register writes
- Power sequencing must be followed for proper operation
- Security features require proper initialization sequence
- Debug interface is independent of main controller operation
- All timing specifications are at maximum operating temperature
- Power consumption varies with clock frequency and activity level

---
