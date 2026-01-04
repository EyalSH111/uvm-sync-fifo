# UVM Verification Project – Synchronous FIFO

## Overview
This project demonstrates an end-to-end, industry-style **UVM verification environment**
for a **synchronous FIFO** design.

The goal is to verify **functional correctness**, **robustness**, and **protocol compliance**
using standard UVM methodology.

The verification environment is:
- Fully **self-checking**
- Includes **directed and randomized sequences**
- Uses **functional coverage**
- Enforces protocol rules via **SystemVerilog Assertions (SVA)**

---

## DUT Specification

### FIFO Type
- **Synchronous FIFO**
- Single clock for read and write
- Parameterizable:
  - `DATA_W` – data width
  - `DEPTH` – FIFO depth

### Read Latency
- **Registered Read**
  - If `rd_en && !empty` at cycle *N*, the output data appears at cycle *N+1*

### Overflow / Underflow Policy
- Write when `full = 1` → blocked (no state change)
- Read when `empty = 1` → blocked (no state change)

---

## Verification Architecture (UVM)

### Interface (`fifo_if`)
- Encapsulates DUT signals
- Provides clocking blocks for race-free driver and monitor operation
- Hosts protocol-level assertions

### Transaction (`fifo_item`)
- Fields:
  - `do_write`
  - `do_read`
  - `wdata`

### Driver
- Converts transaction-level stimulus into pin-level activity
- Applies one-cycle write/read pulses
- Blocks illegal operations based on DUT flags (`full`, `empty`)

### Monitor
- Observes **accepted** write and read operations
- Correctly handles **registered read latency**
- Publishes transactions via analysis ports

### Scoreboard
- Golden reference model implemented as a queue
- Verifies:
  - FIFO ordering (in-order)
  - No data loss or duplication
- Detects overflow / underflow acceptance
- Supports **reset mid-traffic** via explicit model flush
- Produces final **PASS / FAIL** result

### Functional Coverage
- FIFO occupancy: `0`, `1`, `mid`, `DEPTH-1`, `DEPTH`
- Operation types: none, write, read, simultaneous
- Overflow and underflow attempts
- Cross coverage between occupancy and operations

### Assertions (SVA)
- Reset sanity (idle during reset)
- Block write on `full`
- Block read on `empty`
- External protocol invariants (black-box checking)

---

## Tests and Sequences

### Sequences
- **Directed sequence**
  - Single write followed by read (sanity check)
- **Random sequence**
  - Random read/write combinations
  - Random data patterns
- **Drain sequence**
  - Empties FIFO to ensure clean end state

### Tests
- **Base test**
  - Runs directed sanity sequence
- **Random test**
  - Runs random traffic followed by drain
- **Reset-mid-traffic test**
  - Asserts reset during active traffic
  - Flushes scoreboard model
  - Verifies clean recovery and continued operation

Each test creates a fresh environment instance and reuses the same driver,
monitor, scoreboard, and coverage components.

---
###Waveforms:
<img width="1536" height="864" alt="_IF_2_CASES_EXM" src="https://github.com/user-attachments/assets/39a0b6f5-2212-44e9-8127-0bb193e72033" />


## Reset Behavior
- Driver forces idle during reset
- DUT returns to a known empty state
- Scoreboard model is explicitly flushed after reset
- Verification resumes with a clean state

---

## Build Notes
A compilation glue file (e.g. `tb_includes.sv`) is provided for **EDA Playground**
compatibility.  
In a production environment, a filelist or Makefile would be used instead.

---

## How to Run

Example (Questa / qrun):

```bash
qrun -sv -uvm -mfcu design.sv tb_includes.sv +UVM_TESTNAME=fifo_base_test
qrun -sv -uvm -mfcu design.sv tb_includes.sv +UVM_TESTNAME=fifo_random_test
qrun -sv -uvm -mfcu design.sv tb_includes.sv +UVM_TESTNAME=fifo_reset_mid_test



