# SD Card Controller API Reference

## Register Map

### Base Address: 0x4000_0000

| Offset | Name | Access | Reset | Description |
|--------|------|--------|-------|-------------|
| 0x000 | CTRL | R/W | 0x0000_0000 | Control Register |
| 0x004 | STAT | R | 0x0000_0000 | Status Register |
| 0x008 | CLK_CFG | R/W | 0x0000_0000 | Clock Configuration |
| 0x00C | PWR_CTRL | R/W | 0x0000_0000 | Power Control |
| 0x010 | CMD_REG | R/W | 0x0000_0000 | Command Register |
| 0x014 | CMD_ARG | R/W | 0x0000_0000 | Command Argument |
| 0x018 | CMD_RESP | R | 0x0000_0000 | Command Response |
| 0x01C | DATA_BUF | R/W | 0x0000_0000 | Data Buffer |
| 0x020 | INT_EN | R/W | 0x0000_0000 | Interrupt Enable |
| 0x024 | INT_STAT | R | 0x0000_0000 | Interrupt Status |
| 0x028 | INT_CLR | W | 0x0000_0000 | Interrupt Clear |
| 0x02C | DMA_CTRL | R/W | 0x0000_0000 | DMA Control |
| 0x030 | DMA_ADDR | R/W | 0x0000_0000 | DMA Address |
| 0x034 | DMA_LEN | R/W | 0x0000_0000 | DMA Length |
| 0x038 | SEC_CTRL | R/W | 0x0000_0000 | Security Control |
| 0x03C | SEC_KEY | R/W | 0x0000_0000 | Security Key |
| 0x040 | DEBUG_CTRL | R/W | 0x0000_0000 | Debug Control |
| 0x044 | DEBUG_DATA | R | 0x0000_0000 | Debug Data |
| 0x048 | PERF_CTRL | R/W | 0x0000_0000 | Performance Control |
| 0x04C | PERF_CNT | R | 0x0000_0000 | Performance Counter |
| 0x050 | ERR_CTRL | R/W | 0x0000_0000 | Error Control |
| 0x054 | ERR_STAT | R | 0x0000_0000 | Error Status |

## Register Details

### Control Register (CTRL)
| Bit | Name | Access | Description |
|-----|------|--------|-------------|
| 31:16 | Reserved | R | Reserved |
| 15 | EN_SEC | R/W | Enable Security |
| 14 | EN_DMA | R/W | Enable DMA |
| 13 | EN_INT | R/W | Enable Interrupts |
| 12 | EN_DEBUG | R/W | Enable Debug |
| 11 | EN_PERF | R/W | Enable Performance Monitoring |
| 10 | EN_ERR | R/W | Enable Error Reporting |
| 9 | EN_PWR | R/W | Enable Power Management |
| 8 | EN_CLK | R/W | Enable Clock Generator |
| 7:4 | CARD_TYPE | R/W | Card Type Selection |
| 3:0 | BUS_WIDTH | R/W | Bus Width (1/4/8 bit) |

### Status Register (STAT)
| Bit | Name | Access | Description |
|-----|------|--------|-------------|
| 31:16 | Reserved | R | Reserved |
| 15 | CARD_PRESENT | R | Card Present |
| 14 | CARD_WP | R | Card Write Protected |
| 13 | CMD_BUSY | R | Command Busy |
| 12 | DATA_BUSY | R | Data Transfer Busy |
| 11 | DMA_BUSY | R | DMA Busy |
| 10 | SEC_ACTIVE | R | Security Active |
| 9 | DEBUG_ACTIVE | R | Debug Active |
| 8 | PERF_ACTIVE | R | Performance Monitoring Active |
| 7:4 | CARD_STATE | R | Card State |
| 3:0 | ERROR_CODE | R | Error Code |

### Clock Configuration (CLK_CFG)
| Bit | Name | Access | Description |
|-----|------|--------|-------------|
| 31:16 | CLK_DIV | R/W | Clock Divider |
| 15:8 | CLK_FREQ | R/W | Clock Frequency |
| 7:4 | CLK_SRC | R/W | Clock Source |
| 3:0 | CLK_MODE | R/W | Clock Mode |

## Programming Interface

### C API Functions

```c
// Initialize SD Card Controller
int sdcard_init(void);

// Configure clock settings
int sdcard_config_clock(uint32_t freq, uint32_t div);

// Send SD command
int sdcard_send_command(uint8_t cmd, uint32_t arg, uint32_t *resp);

// Read data block
int sdcard_read_block(uint32_t addr, uint8_t *data, uint32_t len);

// Write data block
int sdcard_write_block(uint32_t addr, uint8_t *data, uint32_t len);

// Configure DMA
int sdcard_config_dma(uint32_t addr, uint32_t len);

// Enable interrupts
int sdcard_enable_interrupts(uint32_t mask);

// Get status
int sdcard_get_status(uint32_t *status);

// Configure security
int sdcard_config_security(uint32_t key, uint32_t mode);

// Enable debug
int sdcard_enable_debug(uint32_t mode);

// Get performance counters
int sdcard_get_performance(uint32_t *counters);
```

### Error Codes

| Code | Name | Description |
|------|------|-------------|
| 0 | SDCARD_OK | Success |
| -1 | SDCARD_ERR_TIMEOUT | Command timeout |
| -2 | SDCARD_ERR_CRC | CRC error |
| -3 | SDCARD_ERR_CARD | Card error |
| -4 | SDCARD_ERR_PARAM | Invalid parameter |
| -5 | SDCARD_ERR_BUSY | Device busy |
| -6 | SDCARD_ERR_SECURITY | Security error |
| -7 | SDCARD_ERR_DMA | DMA error |
| -8 | SDCARD_ERR_POWER | Power error |

### Interrupt Handling

```c
// Interrupt handler
void sdcard_interrupt_handler(void) {
    uint32_t status = sdcard_read_reg(INT_STAT);
    
    if (status & INT_CMD_DONE) {
        // Command completed
    }
    
    if (status & INT_DATA_DONE) {
        // Data transfer completed
    }
    
    if (status & INT_ERROR) {
        // Error occurred
    }
    
    // Clear interrupts
    sdcard_write_reg(INT_CLR, status);
}
```

## Timing Specifications

### APB Interface Timing
- Setup time: 2ns
- Hold time: 1ns
- Access time: 10ns

### SD Card Interface Timing
- Clock frequency: 400kHz to 208MHz
- Command setup: 5ns
- Data setup: 3ns
- Response time: 1μs typical

### DMA Transfer Timing
- Burst size: 1-16 words
- Transfer rate: Up to 104MB/s
- Latency: < 1μs 