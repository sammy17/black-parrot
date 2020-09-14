#define DRAM_BASE_ADDR    0x80000000
#define SD_CARD_BASE_ADDR 0x00500000
#define PROG_LOAD_FINISH  0xFFFFFF0000000000
#define MARKER            0xF0F0F0F0F0F0F0F0

#ifndef NUM_CORES
  #define NUM_CORES 1
#endif

#ifndef DOMAIN_MASK
  #define DOMAIN_MASK 1
#endif

#ifndef SAC_MASK
  #define SAC_MASK 0
#endif

#define CCE_PC_WIDTH 8
#define NUM_CCE_INSTR (1 << CCE_PC_WIDTH)

#define CFG_DOMAIN_MASK_ADDR    0x00200009
#define CFG_SAC_MASK_ADDR       0x0020000a
#define CFG_DCACHE_MODE_ADDR    0x00200043
#define CFG_ICACHE_MODE_ADDR    0x00200022
#define CFG_CCE_MODE_ADDR       0x00200081
#define CFG_CCE_UCODE_BASE_ADDR 0x00208000

.section .text.start
.globl _start
_start:
    li x0, 0
    li x1, 0
    li x2, 0
    li x3, 0
    li x4, 0
    li x5, 0
    li x6, 0
    li x7, 0
    li x8, 0
    li x9, 0
    li x10, 0
    li x11, 0
    li x12, 0
    li x13, 0
    li x14, 0
    li x15, 0
    li x16, 0
    li x17, 0
    li x18, 0
    li x19, 0
    li x20, 0
    li x21, 0
    li x22, 0
    li x23, 0
    li x24, 0
    li x25, 0
    li x26, 0
    li x27, 0
    li x28, 0
    li x29, 0
    li x30, 0
    li x31, 0

    # Enable FPU
    li x31, 0x2000
    csrs mstatus, x31
    
    /* Copy CCE uCode into CCE instruction RAM */
    li t0, SD_CARD_BASE_ADDR
    li t1, CFG_CCE_UCODE_BASE_ADDR
    li t2, DRAM_BASE_ADDR
    li t3, PROG_LOAD_FINISH
    li a0, MARKER
load_cce_inst:
    ld t4, 0(t0)
    /* Point to the next entry in "sd card" */
    addi t0, t0, 8
    /* Check for marker in "sd card" */
    beq t4, a0, load_cce_inst_done
    sd t4, 0(t1)
    addi t1, t1, 1
    j load_cce_inst
load_cce_inst_done:
    ld t5, 0(t0)
    li t2, DRAM_BASE_ADDR
    /* t5 has the starting address in "sd card" to load the data */
    /* DO NOT MODIFY UNTIL PROGRAM LOAD */
    add t2, t2, t5
    /* t0 is pointing to the first program instruction in "sd card" */
    /* DO NOT MODIFY UNTIL PROGRAM LOAD */
    addi t0, t0, 8
    
    /* Write D$ mode */
    li t4, 1
    li t1, CFG_DCACHE_MODE_ADDR
    sd t4, 0(t1)

    /* Write I$ mode */
    li t1, CFG_ICACHE_MODE_ADDR
    sd t4, 0(t1)

    /* Write CCE mode */
    li t1, CFG_CCE_MODE_ADDR 
    sd t4, 0(t1)
    
    /* Enable Domains */
    li t4, DOMAIN_MASK
    li t1, CFG_DOMAIN_MASK_ADDR
    sd t4, 0(t1)

    /* Enable SAC */
    li t4, SAC_MASK
    li t1, CFG_SAC_MASK_ADDR
    sd t4, 0(t1)

    j load_prog

switch_addr:
    ld t5, 0(t0)
    beq t5, t3, load_prog_done
    li t2, DRAM_BASE_ADDR
    add t2, t2, t5
    addi t0, t0, 8    
load_prog:
    ld t4, 0(t0)
    addi t0, t0, 8
    beq t4, a0, switch_addr
    sd t4, 0(t2)
    addi t2, t2, 8
    j load_prog
load_prog_done:
    
    /* Flush the D$ */
    fence.i
    li x31, DRAM_BASE_ADDR
    csrw dpc, x31
    csrwi dcsr, 0x3
    dret
halt:
    j halt
