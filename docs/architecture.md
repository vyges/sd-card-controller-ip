# Architecture: SD Card Controller IP

## Overview

This document describes the internal architecture, interfaces, and design details of the SD Card Controller IP. The controller supports SD/SDHC/SDXC cards with both SPI and SD modes, includes comprehensive power management, security features, debug capabilities, and DMA support.

---

## Block Diagram

```text
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
│  │ SDCARD_CTRL         │    │ Configurable    │    │ TX FIFO         │        │
│  │ SDCARD_STATUS       │    │ Clock Divider   │    │ RX FIFO         │        │
│  │ SDCARD_CMD          │    │ Enable/Disable  │    │ Flow Control    │        │
│  │ SDCARD_ARG          │    │ Frequency Scale │    │ Status Flags    │        │
│  │ SDCARD_RESP[0:3]    │    │ Calibration     │    │ Error Handling  │        │
│  │ SDCARD_DATA         │    │                 │    │                 │        │
│  │ SDCARD_BLK_CNT      │    │                 │    │                 │        │
│  │ SDCARD_BLK_SIZE     │    │                 │    │                 │        │
│  │ SDCARD_TIMEOUT      │    │                 │    │                 │        │
│  │ SDCARD_CLK_DIV      │    │                 │    │                 │        │
│  │ SDCARD_INT_EN       │    │                 │    │                 │        │
│  │ SDCARD_INT_STAT     │    │                 │    │                 │        │
│  │ SDCARD_DMA_CTRL     │    │                 │    │                 │        │
│  │ SDCARD_PWR_CTRL     │    │                 │    │                 │        │
│  │ SDCARD_SEC_CTRL     │    │                 │    │                 │        │
│  │ SDCARD_DEBUG_CTRL   │    │                 │    │                 │        │
│  │ SDCARD_TEST_CTRL    │    │                 │    │                 │        │
│  │ SDCARD_ERROR_CTRL   │    │                 │    │                 │        │
│  │ SDCARD_PERF_CTRL    │    │                 │    │                 │        │
│  │ SDCARD_CAL_CTRL     │    │                 │    │                 │        │
│  │ SDCARD_VERSION      │    │                 │    │                 │        │
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

The diagram is a functional view, not a module hierarchy. Some labelled functions
are implemented inside a larger module rather than as a block of their own — the
data FIFO and CRC generation live in the data and command engines — and three
labels have **no implementation in the current RTL** at all: *Voltage Monitor* and
*Power Optimize* in the power controller, and *Security Logging* in the security
controller. See Internal Modules below for the mapping onto `rtl/`.

---

## Parameters

All parameters carry the `SDCARD_` block prefix, per the Vyges namespace-isolation
convention, so that several IP blocks can be integrated without collisions.

| Parameter | Type | Default | Description |
| ----------- | ------ | --------- | ------------- |
| `SDCARD_APB_ADDR_WIDTH` | int | 16 | Width of APB address bus |
| `SDCARD_DATA_WIDTH` | int | 4 | SD card data width (1, 4, or 8 bits) |
| `SDCARD_FIFO_DEPTH` | int | 512 | FIFO depth for data buffering |
| `SDCARD_DMA_ENABLE` | bit | 1'b1 | Enable DMA support |
| `SDCARD_SPI_MODE_ENABLE` | bit | 1'b1 | Enable SPI mode support |

---

## Interfaces

### APB Slave Interface

| Signal | Direction | Width | Description |
| -------- | ----------- | ------- | ------------- |
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
| -------- | ----------- | ------- | ------------- |
| `sd_clk_o` | output | 1 | SD card clock |
| `sd_cmd_io` | bidir | 1 | SD command line |
| `sd_dat_io` | bidir | 4 | SD data lines |
| `sd_cd_i` | input | 1 | Card detect |
| `sd_wp_i` | input | 1 | Write protect |
| `sd_pwr_en_o` | output | 1 | SD card power enable |
| `sd_vdd_sel_o` | output | 1 | SD card voltage select |

### Interrupt Interface

| Signal | Direction | Width | Description |
| -------- | ----------- | ------- | ------------- |
| `sd_irq_o` | output | 1 | SD card interrupt |
| `dma_irq_o` | output | 1 | DMA transfer complete interrupt |
| `error_irq_o` | output | 1 | Error condition interrupt |
| `debug_irq_o` | output | 1 | Debug event interrupt |

### DMA Interface (Optional)

| Signal | Direction | Width | Description |
| -------- | ----------- | ------- | ------------- |
| `dma_req_o` | output | 1 | DMA request |
| `dma_ack_i` | input | 1 | DMA acknowledge |
| `dma_addr_o` | output | 32 | DMA address |
| `dma_len_o` | output | 16 | DMA length |
| `dma_we_o` | output | 1 | DMA write enable |
| `dma_burst_o` | output | 1 | DMA burst mode |
| `dma_cache_o` | output | 4 | DMA cache attributes |

### Debug Interface

| Signal | Direction | Width | Description |
| -------- | ----------- | ------- | ------------- |
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
| --------- | --------------- | -------- | ------------- |
| 0x00 | SDCARD_CTRL | R/W | Control register |
| 0x04 | SDCARD_STATUS | R | Status register |
| 0x08 | SDCARD_CMD | R/W | Command register |
| 0x0C | SDCARD_ARG | R/W | Command argument |
| 0x10 | SDCARD_RESP[0] | R | Response register 0 |
| 0x14 | SDCARD_RESP[1] | R | Response register 1 |
| 0x18 | SDCARD_RESP[2] | R | Response register 2 |
| 0x1C | SDCARD_RESP[3] | R | Response register 3 |
| 0x20 | SDCARD_DATA | R/W | Data register |
| 0x24 | SDCARD_BLK_CNT | R/W | Block count register |
| 0x28 | SDCARD_BLK_SIZE | R/W | Block size register |
| 0x2C | SDCARD_TIMEOUT | R/W | Timeout register |
| 0x30 | SDCARD_CLK_DIV | R/W | Clock divider register |
| 0x34 | SDCARD_INT_EN | R/W | Interrupt enable register |
| 0x38 | SDCARD_INT_STAT | R/W | Interrupt status register |
| 0x3C | SDCARD_DMA_CTRL | R/W | DMA control register |
| 0x40 | SDCARD_PWR_CTRL | R/W | Power control register |
| 0x44 | SDCARD_SEC_CTRL | R/W | Security control register |
| 0x48 | SDCARD_DEBUG_CTRL | R/W | Debug control register |
| 0x4C | SDCARD_TEST_CTRL | R/W | Test control register |
| 0x50 | SDCARD_ERROR_CTRL | R/W | Error control register |
| 0x54 | SDCARD_PERF_CTRL | R/W | Performance control register |
| 0x58 | SDCARD_CAL_CTRL | R/W | Calibration control register |
| 0x5C | SDCARD_VERSION | R | Version register |

---

## Internal Modules

`sdcard_controller` is a purely structural top level: it declares no logic of its
own and instantiates the fifteen modules below. Each entry names the RTL file
that implements it, so this list can be checked against `rtl/` directly.

### Core Functional Modules

- **`sdcard_apb_interface`**: Implements APB3 slave protocol with error handling
- **`sdcard_register_file`**: Holds the register map and handles read/write decode
- **`sdcard_command_engine`**: Handles SD command generation, transmission, and response parsing
- **`sdcard_data_engine`**: Manages data block transmission/reception with CRC checking
- **`sdcard_clock_generator`**: Provides configurable SD card clock with calibration
- **`sdcard_dma_controller`**: Optional DMA support for high-speed transfers

### Power Management Modules

- **`sdcard_power_controller`**: Manages power states and power sequencing

### Security Modules

- **`sdcard_security_controller`**: Implements access control, authentication, lock and recovery states

### Debug and Test Modules

- **`sdcard_debug_controller`**: Manages JTAG interface, trace generation, and breakpoints
- **`sdcard_test_controller`**: Implements BIST, scan chains, and test modes
- **`sdcard_error_controller`**: Handles error detection, recovery, and reporting
- **`sdcard_performance_controller`**: Monitors and optimizes performance

### Support Modules

- **`sdcard_interrupt_controller`**: Manages interrupt generation, queueing, and prioritization
- **`sdcard_interface`**: Handles SD card signal control and timing
- **`sdcard_calibration_controller`**: Manages clock and timing calibration

### Functions implemented inline, not as separate modules

These are real behaviours of the design, but they live inside the modules above
rather than in dedicated RTL files. Earlier revisions of this document listed
them as modules of their own, which did not match `rtl/`.

- **FIFO buffering** and **CRC7/CRC16 generation**: inside the data and command engines
- **Tamper detection** and **secure-boot / encryption hooks**: inside `sdcard_security_controller`

Voltage monitoring, power optimisation, and security event logging appear in the
feature narrative below but have **no implementation in the current RTL**. They
are design intent, not delivered function.

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

`sdcard_power_controller` implements six states (`pwr_state_t`). Power figures are
design targets, not measurements — see Performance Characteristics below.

| State | Encoding | Description |
| ------- | ---------- | ------------- |
| `PWR_OFF` | 3'b000 | Complete shutdown |
| `PWR_STARTUP` | 3'b001 | Power-up sequencing before active operation |
| `PWR_ACTIVE` | 3'b010 | Full functionality |
| `PWR_IDLE` | 3'b011 | Reduced functionality |
| `PWR_SLEEP` | 3'b100 | Minimal functionality |
| `PWR_FAULT` | 3'b101 | Power fault detected; requires recovery |

---

## State Machine

### Top level has no state machine

`sdcard_controller` is a structural wrapper containing no procedural logic. Control
is distributed across the submodules, each with its own FSM. Earlier revisions of
this document showed a single top-level IDLE / INIT / READY / CMD SEND flow; no
such machine exists in `rtl/`.

The command engine below carries the command-response sequence that diagram was
describing. The other FSMs are named alongside it.

### Command Engine States (`cmd_state_t`, `sdcard_command_engine`)

```text
                    ┌──────────────┐
             ┌─────▶│  CMD_IDLE    │◀────────────────┬──────────────┐
             │      └──────┬───────┘                 │              │
             │             │ command request         │              │
             │             ▼                         │              │
             │      ┌──────────────┐                 │              │
             │      │  CMD_SETUP   │                 │              │
             │      └──────┬───────┘                 │              │
             │             ▼                         │              │
             │      ┌──────────────┐                 │              │
             │      │  CMD_SEND    │                 │              │
             │      └──────┬───────┘                 │              │
             │             ▼                         │              │
             │      ┌──────────────┐   timeout   ┌───┴──────────┐   │
             │      │CMD_WAIT_RESP ├────────────▶│ CMD_TIMEOUT  │   │
             │      └──────┬───────┘             └──────────────┘   │
             │             │ response received                      │
             │             ▼                                        │
             │      ┌──────────────┐                                │
             │      │ CMD_RECEIVE  │                                │
             │      └──────┬───────┘                                │
             │             ▼                                        │
             │      ┌──────────────┐   CRC fail  ┌──────────────┐   │
             │      │CMD_CHECK_CRC ├────────────▶│  CMD_ERROR   ├───┘
             │      └──────┬───────┘             └──────────────┘
             │             │ CRC pass
             │             ▼
             │      ┌──────────────┐
             └──────┤ CMD_COMPLETE │
                    └──────────────┘

  CMD_BUSY is entered while the card holds the line busy and returns to CMD_IDLE.
```

| State | Encoding | Description |
| ------- | ---------- | ------------- |
| `CMD_IDLE` | 4'b0000 | Wait for a command request |
| `CMD_SETUP` | 4'b0001 | Latch command index and argument |
| `CMD_SEND` | 4'b0010 | Shift the command out with CRC7 |
| `CMD_WAIT_RESP` | 4'b0011 | Await response, or time out |
| `CMD_RECEIVE` | 4'b0100 | Shift the response in |
| `CMD_CHECK_CRC` | 4'b0101 | Validate the response CRC |
| `CMD_COMPLETE` | 4'b0110 | Update status, raise completion |
| `CMD_ERROR` | 4'b0111 | CRC or protocol error, return to idle |
| `CMD_TIMEOUT` | 4'b1000 | No response in time, return to idle |
| `CMD_BUSY` | 4'b1001 | Card signalling busy |

### Other state machines

Each of these is defined in the module named, and none of them is visible at the
top level:

| Module | Type | States |
| -------- | ------ | -------- |
| `sdcard_data_engine` | data block transfer | see `rtl/sdcard_data_engine.sv` |
| `sdcard_power_controller` | `pwr_state_t` | 6, listed under Power Domains above |
| `sdcard_interrupt_controller` | `interrupt_state_t` | 7: IDLE, DETECT, QUEUE, PRIORITIZE, GENERATE, ACKNOWLEDGE, CLEAR |
| `sdcard_security_controller` | security FSM | IDLE, AUTH, ACCESS, LOCK, MONITOR, ALERT, RECOVERY, ENCRYPT, DECRYPT |
| `sdcard_error_controller` | `error_state_t` | see `rtl/sdcard_error_controller.sv` |
| `sdcard_dma_controller` | DMA transfer | see `rtl/sdcard_dma_controller.sv` |
| `sdcard_apb_interface` | APB protocol | see `rtl/sdcard_apb_interface.sv` |
| `sdcard_clock_generator`, `sdcard_calibration_controller`, `sdcard_debug_controller`, `sdcard_test_controller`, `sdcard_interface` | various | see the respective files |

---

## Signal Flow Diagram

### APB Interface Flow

```text
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

```text
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

> **These are design targets, not measured results.** No timing, power, or
> throughput characterisation has been run on this IP: the repository contains no
> STA reports, no power analysis, and no silicon or FPGA measurements. Treat every
> number below as an objective to design and sign off against, and do not quote
> any of it as a specification until it is backed by a characterisation run.

### Timing Specifications (targets)

- **APB Clock**: 50MHz - 100MHz operation
- **SD Card Clock**: 400kHz - 50MHz configurable
- **Command Response**: < 100μs typical
- **Data Transfer**: < 1ms per 512-byte block
- **Interrupt Latency**: < 10μs

### Throughput Specifications (targets)

- **Sustained Transfer Rate**: 20MB/s minimum
- **Burst Transfer Rate**: 25MB/s maximum
- **Command Processing**: 1000 commands/second
- **Queue Depth**: Up to 8 pending commands

### Power Specifications (targets)

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
