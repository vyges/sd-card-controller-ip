# SD Card Controller API Reference

Everything below is derived from `rtl/sdcard_register_file.sv`, which is the
authoritative source for offsets, access types, and bit positions.

## Register Map

**Base address**: assigned by the integrator. The IP decodes only the offsets
below; it has no opinion about where it sits in the system memory map.

The APB address decoder accepts offsets `0x000`–`0x05C` inclusive and reports
addresses above `0x05C` as invalid. All registers are 32 bits and word-aligned.

| Offset | Register | Access | Reset | Description |
| -------- | ---------- | -------- | ------- | ------------- |
| 0x000 | `SD_CTRL` | R/W | 0x0000_0000 | Control register |
| 0x004 | `SD_STATUS` | R | 0x0000_0000 | Status register |
| 0x008 | `SD_CMD` | R/W | 0x0000_0000 | Command register |
| 0x00C | `SD_ARG` | R/W | 0x0000_0000 | Command argument |
| 0x010 | `SD_RESP0` | R | 0x0000_0000 | Command response word 0 |
| 0x014 | `SD_RESP1` | R | 0x0000_0000 | Command response word 1 |
| 0x018 | `SD_RESP2` | R | 0x0000_0000 | Command response word 2 |
| 0x01C | `SD_RESP3` | R | 0x0000_0000 | Command response word 3 |
| 0x020 | `SD_DATA` | R/W | 0x0000_0000 | Data register |
| 0x024 | `SD_BLK_CNT` | R/W | 0x0000_0000 | Block count |
| 0x028 | `SD_BLK_SIZE` | R/W | 0x0000_0000 | Block size |
| 0x02C | `SD_TIMEOUT` | R/W | 0x0000_0000 | Timeout value |
| 0x030 | `SD_CLK_DIV` | R/W | 0x0000_0000 | Clock divider |
| 0x034 | `SD_INT_EN` | R/W | 0x0000_0000 | Interrupt enable |
| 0x038 | `SD_INT_STAT` | R | 0x0000_0000 | Interrupt status |
| 0x03C | `SD_DMA_CTRL` | R/W | 0x0000_0000 | DMA control |
| 0x040 | `SD_PWR_CTRL` | R/W | 0x0000_0000 | Power control |
| 0x044 | `SD_SEC_CTRL` | R/W | 0x0000_0000 | Security control |
| 0x048 | `SD_DEBUG_CTRL` | R/W | 0x0000_0000 | Debug control |
| 0x04C | `SD_TEST_CTRL` | R/W | 0x0000_0000 | Test control |
| 0x050 | `SD_ERROR_CTRL` | R/W | 0x0000_0000 | Error control |
| 0x054 | `SD_PERF_CTRL` | R/W | 0x0000_0000 | Performance control |
| 0x058 | `SD_CAL_CTRL` | R/W | 0x0000_0000 | Calibration control |
| 0x05C | `SD_VERSION` | R | 0x0100_0000 | Version, 1.0.0 |

Writes are accepted only when no security violation is asserted and the register
file is not write-protected; otherwise the write is dropped silently.

## Register Details

Only the bits listed are decoded by the RTL. Unlisted bits are writable and
read back on R/W registers but drive nothing.

### Control Register (`SD_CTRL`, 0x000)

| Bit | Name | Access | Description |
| ----- | ------ | -------- | ------------- |
| 14 | `CLK_EN` | R/W | Clock generator enable |
| 3 | `DATA_START` | R/W | Start a data transfer |
| 2 | `DATA_VALID` | R/W | Data valid; also drives the FIFO write strobe |
| others | — | R/W | Not decoded |

Bit 2 drives both `data_valid` and `fifo_write`; they are the same signal.
A FIFO read strobe on bit 1 exists in the source but is commented out and has
no effect.

### Status Register (`SD_STATUS`, 0x004, read-only)

Driven directly from internal status inputs every clock.

| Bit | Name | Description |
| ----- | ------ | ------------- |
| 31:16 | Reserved | Reads as 0 |
| 15 | `POWER_GOOD` | Power good |
| 14 | `POWER_FAULT` | Power fault |
| 13 | `CMD_BUSY` | Command busy |
| 12 | `CMD_DONE` | Command done |
| 11 | `CMD_TIMEOUT` | Command timeout |
| 10 | `CMD_CRC_ERROR` | Command CRC error |
| 9 | `DATA_BUSY` | Data busy |
| 8 | `DATA_DONE` | Data done |
| 7 | `DATA_CRC_ERROR` | Data CRC error |
| 6 | `DMA_BUSY` | DMA busy |
| 5 | `DMA_DONE` | DMA done |
| 4 | `DMA_ERROR` | DMA error |
| 3 | `FIFO_FULL` | FIFO full |
| 2 | `FIFO_EMPTY` | FIFO empty |
| 1 | `CLK_CALIBRATED` | Clock calibrated |
| 0 | `CAL_DONE` | Calibration done |

### Command Register (`SD_CMD`, 0x008)

| Bit | Name | Access | Description |
| ----- | ------ | -------- | ------------- |
| 31 | `CMD_START` | R/W | Start command transmission |
| 5:0 | `CMD_INDEX` | R/W | SD command index |
| others | — | R/W | Not decoded |

### Response Registers (`SD_RESP0`–`SD_RESP3`, 0x010–0x01C, read-only)

Loaded when a command completes:

- `SD_RESP0` = `{8'h00, cmd_response[39:16]}`
- `SD_RESP1` = `{cmd_response[15:0], 16'h0000}`
- `SD_RESP2`, `SD_RESP3` = 0

Only a 40-bit response is captured, so `SD_RESP2` and `SD_RESP3` are always
zero. Long (R2/136-bit) responses are not currently unpacked into these
registers.

### Clock Divider (`SD_CLK_DIV`, 0x030)

| Bit | Name | Access | Description |
| ----- | ------ | -------- | ------------- |
| 15:0 | `CLK_DIV` | R/W | Divider for the SD clock |
| 31:16 | — | R/W | Not decoded |

### DMA Control (`SD_DMA_CTRL`, 0x03C)

| Bit | Name | Access | Description |
| ----- | ------ | -------- | ------------- |
| 31:16 | `DMA_BASE` | R/W | Base address, used as `DMA_BASE << 16` |
| 15:0 | `DMA_LEN` | R/W | Transfer length |
| 0 | `DMA_EN` | R/W | DMA enable |

Bit 0 is decoded both as `DMA_EN` and as the least-significant bit of
`DMA_LEN`; the two overlap in the RTL. Setting an odd length therefore also
asserts the enable. Treat lengths as even until this is separated.

### Power Control (`SD_PWR_CTRL`, 0x040)

| Bit | Name | Access | Description |
| ----- | ------ | -------- | ------------- |
| 11:8 | `VOLTAGE_SEL` | R/W | Voltage select |
| 1:0 | `POWER_STATE` | R/W | Requested power state |
| others | — | R/W | Not decoded |

### Debug Control (`SD_DEBUG_CTRL`, 0x048)

| Bit | Name | Access | Description |
| ----- | ------ | -------- | ------------- |
| 1 | `JTAG_EN` | R/W | JTAG enable |
| 0 | `DEBUG_EN` | R/W | Debug enable |
| others | — | R/W | Not decoded |

### Calibration Control (`SD_CAL_CTRL`, 0x058)

| Bit | Name | Access | Description |
| ----- | ------ | -------- | ------------- |
| 0 | `CAL_START` | R/W | Start calibration |
| others | — | R/W | Not decoded |

### Interrupt Status (`SD_INT_STAT`, 0x038, read-only)

| Bit | Name | Description |
| ----- | ------ | ------------- |
| 31:4 | Reserved | Reads as 0 |
| 3:0 | `INT_STATUS` | Interrupt status from the interrupt controller |

There is no write-1-to-clear register. Interrupt state is managed inside
`sdcard_interrupt_controller` and cleared through its own acknowledge and clear
states, not by an APB write.

### Registers stored but not acted on

These are writable and read back, but their outputs are commented out in
`sdcard_register_file.sv`, so writing them changes no behaviour today:

| Register | Intended bits | Status |
| ---------- | --------------- | -------- |
| `SD_INT_EN` (0x034) | `[3:0]` interrupt enable | Connection commented out |
| `SD_SEC_CTRL` (0x044) | `[0]` security lock | Connection commented out |
| `SD_ERROR_CTRL` (0x050) | `[0]` error clear, `[1]` error interrupt | Connections commented out |
| `SD_TEST_CTRL` (0x04C) | — | Stored only, no decode |
| `SD_PERF_CTRL` (0x054) | — | Stored only, no decode |

`SD_ARG`, `SD_DATA`, `SD_BLK_CNT`, `SD_BLK_SIZE`, and `SD_TIMEOUT` are stored
and read back; they are consumed by the command and data engines rather than
decoded bit-wise here.

## Programming Interface

> **No driver ships with this IP.** The repository contains no C sources or
> headers. The sketch below is a proposed shape for a driver, not an API you can
> link against, and no part of it has been implemented or tested.

```c
// Proposed, not implemented.
int sdcard_init(void);
int sdcard_config_clock(uint32_t divider);          // writes SD_CLK_DIV
int sdcard_send_command(uint8_t cmd, uint32_t arg, uint32_t *resp);
int sdcard_read_block(uint32_t addr, uint8_t *data, uint32_t len);
int sdcard_write_block(uint32_t addr, uint8_t *data, uint32_t len);
int sdcard_config_dma(uint32_t base, uint16_t len); // writes SD_DMA_CTRL
int sdcard_get_status(uint32_t *status);            // reads SD_STATUS
```

A minimal command sequence against the registers as they exist:

1. Write the divider to `SD_CLK_DIV` (0x030) and set `SD_CTRL[14]` to enable the clock.
2. Poll `SD_STATUS[1]` (`CLK_CALIBRATED`) if calibration is in use.
3. Write the argument to `SD_ARG` (0x00C).
4. Write the index to `SD_CMD[5:0]` with `SD_CMD[31]` set to start.
5. Poll `SD_STATUS[12]` (`CMD_DONE`), checking `[11]` timeout and `[10]` CRC error.
6. Read the response from `SD_RESP0` and `SD_RESP1`.

## Timing

See `docs/architecture.md`. Those figures are design targets; no timing
characterisation has been run. The SD clock range implemented by
`sdcard_clock_generator` is 400kHz to 50MHz.
