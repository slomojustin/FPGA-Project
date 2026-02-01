# FPGA‑Project — 3‑Stage RISC‑V CPU on PYNQ‑Z1

This project implements a 3‑stage pipelined 32‑bit RISC‑V (rv32ui + CSR) CPU in Verilog for the Digilent PYNQ‑Z1 FPGA, with UART‑based BIOS boot, branch prediction, and memory‑mapped IO.[file:2]

---

## Highlights

- 3‑stage pipeline: IF, combined ID/EX, and combined MEM/WB, with full forwarding for ALU↔ALU, ALU↔MEM, MEM↔ALU, and MEM↔MEM hazards.[file:2]  
- Dynamic branch predictor using a branch history table (BHT) and saturating counters, feeding the PC selection logic in fetch.[file:2]  
- UART‑driven BIOS that loads programs into instruction memory, then jumps from BIOS address space to IMem execution.[file:2]  
- Memory‑mapped address partitions for BIOS, IMem, DMem, UART, CSRs, and other IO devices.[file:2]  
- CSR support for `tohost`, test termination, and basic performance counters.[file:2]

---

## Architecture

- Decode/Execute is the critical stage, performing decode, register reads, immediate generation, ALU operations, and branch/jump target calculation in one cycle.[file:2]  
- Forwarding via ASel/BSel and a dedicated MEM‑forward mux resolves 1‑cycle data hazards without extra stalls; 2‑cycle‑apart hazards are naturally handled by the pipeline.[file:2]  
- Branch and jump (JAL/JALR) mispredictions flush younger instructions; typical JAL/JALR resolution requires flushing two stages.[file:2]

---

## Memory, BIOS, and UART

- BIOS ROM is selected when PC[30] is asserted and `address[31:28]` falls in the BIOS region (e.g., `4'b0100`).[file:2]  
- IMem is selected when `address[31:28] == 4'b0001` and is writable during the BIOS load phase via UART to install user programs.[file:2]  
- Loads/stores are routed to DMem or IO purely by address partitioning.[file:2]  
- UART interface example logic:  
  - `uart_tx_data_in_valid = data_to_transmit_ready && uart_tx_data_in_ready;`  
  - `uart_rx_data_out_ready = cpu_ready_to_receive;`[file:2]

---

## Repository Layout

- `src/z1top.v` — Top‑level wrapper for PYNQ‑Z1 (clocking, IO, CPU instance).  
- `src/z1top.xdc` — Board constraints (pins, timing).  
- `src/riscv_core/cpu.v` — 3‑stage core, hazard/forwarding logic, control.[file:2]  
- `src/memories/bios_mem.v` — BIOS ROM loading `software/bios/bios.hex`.[file:2]  
- `src/io_circuits/` — Synchronizer and debouncer modules.  
- `151_library/` — C headers for software; `software/` — BIOS and user programs.

---

## Build & Run

- **Simulation:** Use Verilator with a custom testbench that instantiates `z1top` or the core and monitors UART/CSR `tohost` for pass/fail.[file:2]  
- **FPGA:** In Vivado, target XC7Z020‑1CLG484, set `z1top` as top, add `z1top.xdc`, provide `software/bios/bios.hex`, generate bitstream, and program the PYNQ‑Z1.[file:2]
