# SD Card Controller User Guide

## Quick Start

### Basic Integration

```systemverilog
// Instantiate the SD Card Controller
sdcard_controller sdcard_ctrl (
    .clk_i        (system_clk),
    .reset_n_i    (system_reset_n),
    .psel_i       (apb_psel),
    .penable_i    (apb_penable),
    .pwrite_i     (apb_pwrite),
    .paddr_i      (apb_paddr),
    .pwdata_i     (apb_pwdata),
    .prdata_o     (apb_prdata),
    .pready_o     (apb_pready),
    .pslverr_o    (apb_pslverr),
    .sd_clk_o     (sd_clk),
    .sd_cmd_io    (sd_cmd),
    .sd_dat_io    (sd_data),
    .sd_cd_i      (sd_card_detect),
    .sd_wp_i      (sd_write_protect),
    .sd_irq_o     (sd_interrupt)
);
```

### Initialization Sequence

1. Reset the controller
2. Configure clock settings
3. Enable the controller
4. Initialize SD card
5. Configure data transfer parameters

## Configuration

### Clock Configuration

- System clock: 100MHz maximum
- SD clock: 400kHz to 50MHz (set by `SD_CLK_DIV`, 0x030)
- Configurable clock dividers

### Power Management

- Dynamic voltage scaling
- Clock gating support
- Sleep mode configuration

### Security Settings

- Encryption key configuration
- Authentication setup
- Secure boot parameters

## Register Map

Offsets are taken from `rtl/sdcard_register_file.sv`. The base address is chosen
by the integrator; the IP decodes offsets `0x000`–`0x05C` only. The full bit-level
description is in `docs/api_reference.md`.

### Control and status

- `0x000`: `SD_CTRL` — control (bit 14 clock enable, bit 3 data start, bit 2 data valid)
- `0x004`: `SD_STATUS` — status, read-only
- `0x05C`: `SD_VERSION` — version, read-only, reads 0x0100_0000

### Command and response

- `0x008`: `SD_CMD` — command (bits 5:0 index, bit 31 start)
- `0x00C`: `SD_ARG` — command argument
- `0x010`: `SD_RESP0` — response word 0, read-only
- `0x014`: `SD_RESP1` — response word 1, read-only
- `0x018`: `SD_RESP2` — response word 2, read-only, always 0
- `0x01C`: `SD_RESP3` — response word 3, read-only, always 0

### Data transfer

- `0x020`: `SD_DATA` — data register
- `0x024`: `SD_BLK_CNT` — block count
- `0x028`: `SD_BLK_SIZE` — block size
- `0x02C`: `SD_TIMEOUT` — timeout value
- `0x03C`: `SD_DMA_CTRL` — DMA control

### Clocking and power

- `0x030`: `SD_CLK_DIV` — clock divider (bits 15:0)
- `0x040`: `SD_PWR_CTRL` — power control (bits 1:0 state, 11:8 voltage select)
- `0x058`: `SD_CAL_CTRL` — calibration control (bit 0 start)

### Interrupts

- `0x034`: `SD_INT_EN` — interrupt enable (stored, not yet wired up)
- `0x038`: `SD_INT_STAT` — interrupt status, read-only

There is no interrupt-clear register. Interrupt state is managed inside
`sdcard_interrupt_controller`, not cleared by an APB write.

### Security, debug, and test

- `0x044`: `SD_SEC_CTRL` — security control (stored, not yet wired up)
- `0x048`: `SD_DEBUG_CTRL` — debug control (bit 0 debug enable, bit 1 JTAG enable)
- `0x04C`: `SD_TEST_CTRL` — test control (stored, not yet wired up)
- `0x050`: `SD_ERROR_CTRL` — error control (stored, not yet wired up)
- `0x054`: `SD_PERF_CTRL` — performance control (stored, not yet wired up)

## Programming Interface

> No driver ships with this IP; the repository contains no C sources. The
> snippets below show the register sequence, not an API you can link against.

### APB Access

```c
void     sdcard_write_reg(uint32_t offset, uint32_t data);
uint32_t sdcard_read_reg(uint32_t offset);
```

### Command Interface

```c
// Argument first, then index with the start bit; poll SD_STATUS for completion.
int sdcard_send_command(uint8_t cmd, uint32_t arg) {
    sdcard_write_reg(0x00C, arg);                       // SD_ARG
    sdcard_write_reg(0x008, (1u << 31) | (cmd & 0x3F)); // SD_CMD start + index
    return wait_command_complete();                     // poll SD_STATUS bit 12
}

// Completion and error bits live in SD_STATUS (0x004):
//   bit 12 CMD_DONE, bit 11 CMD_TIMEOUT, bit 10 CMD_CRC_ERROR
// Response words are read from SD_RESP0 (0x010) and SD_RESP1 (0x014).
```

## Error Handling

### Error Types

- Command timeout
- Data transfer errors
- CRC errors
- Card detection issues

### Recovery Procedures

- Automatic retry mechanisms
- Error status reporting
- Recovery sequence execution

## Performance Optimization

### DMA Configuration

- Buffer alignment requirements
- Transfer size optimization
- Burst transfer settings

### Clock Optimization

- Dynamic frequency scaling
- Performance monitoring
- Power vs. performance trade-offs

## Debug and Testing

### Debug Interface

- Real-time monitoring
- Performance counters
- Error logging

### Test Modes

- Built-in self-test
- Manufacturing test
- Loopback testing

## Troubleshooting

### Common Issues

1. Card not detected
2. Command timeouts
3. Data transfer failures
4. Performance issues

### Solutions

- Check physical connections
- Verify clock configuration
- Review power supply
- Analyze debug output
