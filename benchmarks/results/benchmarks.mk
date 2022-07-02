SHELL = /bin/bash -o pipefail

TIME_LIMIT ?= 36000 # seconds
STACK_LIMIT ?= 65536 # kB
MEM_LIMIT ?= 33554432 # kB

SRCDIR = ../../..
CLANG = clang
CC = gcc
OPT = # -O1
TOOLCLANGFLAGS = $(OPT)
OPTFLAGS = -mem2reg
CLANGFLAGS = -c -emit-llvm -g -Xclang -disable-O0-optnone $(TOOLCLANGFLAGS)
NIDHUGGC ?= ../../nidhuggc
NIDHUGGCOP ?= /home/sarbojit/nidhugg/src/nidhuggc
GENMC6 ?= ~kostis/genmc/src/genmc.v0.6.1
SOURCE    = $(NIDHUGGC) $(1) -- -c11 -sc -source
OPTIMAL   = $(NIDHUGGCOP) $(1) -- -sc -optimal -no-assume-await
OBSERVERS = $(NIDHUGGC) $(1) -- -c11 -sc -observers
RFSC      = $(NIDHUGGC) $(1) -- -c11 -sc -rf
EVENT     = $(NIDHUGGC) $(1) -- -sc -event
LAPORMO   = $(GENMC6) --lapor --mo -- $(1)
LAPOR     = $(GENMC6) --lapor -- $(1)
GENMC     = $(GENMC6) -- $(1)
GENMCMO   = $(GENMC6) --mo -- $(1)
TIME = env time -f 'real %e\nres %M'
TIMEOUT = timeout $(TIME_LIMIT)
ULIMIT = ulimit -Ss $(STACK_LIMIT) && ulimit -Sv $(MEM_LIMIT) &&
RUN = -$(ULIMIT) $(TIMEOUT) $(TIME)
TABULATE = ../../tabulate.sh

TOOLS = genmcmo lapormo optimal event

TABLES = $(TOOLS:%=%.txt) wide.txt
# Only for wide.txt (not including $(tool)_THREADS
ALL_RESULTS = $(foreach tool,$(TOOLS),$(foreach n,$(N),$(tool)_$(n).txt))
BITCODE_FILES = $(N:%=code_%.ll)
# Add the bitcode files as explicit targets, otherwise Make deletes them after
# benchmark, and thus reruns *all* benchmarks of a particular size if any of
# them need to be remade
all: $(TABLES) # $(BITCODE_FILES)

code_%.ll: $(SRCDIR)/$(FILE)
	$(CLANG) -DN=$* $(CLANGFLAGS) -o - $< | opt $(OPTFLAGS) -S -o $@

define tool_template =
 $(1)_$(2).txt: $(SRCDIR)/$(FILE)
	@date
	$$(RUN) $$(call $(shell echo $(1) | tr a-z A-Z), -DN=$(2)) $$< 2>&1 | tee $$@
 $(1).txt: $(1)_$(2).txt
endef

$(foreach tool,$(filter-out $(SPECIAL_TOOLS),$(TOOLS)),\
	$(foreach n,$(N),\
		$(eval $(call tool_template,$(tool),$(n)))))

# rfsc32_%_1.txt: rfsc_%_32.txt
# 	cp $< $@
# rfsc32.txt: $(foreach n,$(N),rfsc32_$(n)_1.txt)

define tool_tab_template =
$(1).txt: $$(TABULATE)
	$$(TABULATE) tool "$$(NAME)" $(1) "$$(N)" \
	  | column -t > $(1).txt
endef

$(foreach tool,$(TOOLS),\
	$(eval $(call tool_tab_template,$(tool))))

wide.txt: $(ALL_RESULTS) $(TABULATE)
	$(TABULATE) wide "$(NAME)" "$(TOOLS)" "$(N)" \
	  | column -t > $@


clean:
	rm -f *.ll *.bc *.elf $(TABLES)
mrproper: clean
	rm -f *.txt

.PHONY: clean all benchmark mrproper
.DELETE_ON_ERROR:
