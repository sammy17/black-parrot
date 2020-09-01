
RISCV_GCC = $(CROSS_COMPILE)gcc -fPIC -march=rv64im -mabi=lp64 -mcmodel=medany -static -nostdlib -nostartfiles

.DEFAULT: all

all: clean build

clean:
	rm -f bootrom.riscv *.bin *.out

build:
	$(RISCV_GCC) bootrom.S -DMULTICORE=$(MULTICORE) -DNUM_CORES=$(NCPUS) -DDOMAIN_MASK=$(DOMAIN_MASK) -DSAC_MASK=$(SAC_MASK) -o bootrom.riscv -Tlink.ld -static -Wl,--no-gc-sections
