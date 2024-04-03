SHELL = /bin/bash -o pipefail

#
# Set this to the proper value
#
HOME_DIR = /home/pop

NIDHUGGCPOP ?= ${HOME_DIR}/nidhugg-pop/src/nidhuggc
NIDHUGGC    ?= ${HOME_DIR}/nidhugg/src/nidhuggc
GENMC       ?= ${HOME_DIR}/genmc/genmc

TIME_LIMIT ?= 7200 # seconds
STACK_LIMIT ?= 65536 # kB
MEM_LIMIT ?= 33554432 # kB

SRCDIR = ../../..
CLANG = clang
CC = gcc
OPT = # -O1
TOOLCLANGFLAGS = $(OPT)
OPTFLAGS = -mem2reg
CLANGFLAGS = -c -emit-llvm -g -Xclang -disable-O0-optnone $(TOOLCLANGFLAGS)

SOURCE    = $(NIDHUGGC) $(1) -- -c11 -sc -source
OPTIMAL   = $(NIDHUGGC) $(1) -- -sc -optimal --extfun-no-race=pow #-no-assume-await
POP       = $(NIDHUGGCPOP) $(1) -- -sc -pop   --extfun-no-race=pow
OBSERVERS = $(NIDHUGGC) $(1) -- -c11 -sc -observers
RFSC      = $(NIDHUGGC) $(1) -- -c11 -sc -rf
GENMCSC   = $(GENMC) -sc --disable-instruction-caching --disable-sr --disable-ipr --disable-estimation -- $(1)
TIME = env time -f 'real %e\nres %M'
TIMEOUT = timeout $(TIME_LIMIT)
ULIMIT = ulimit -Ss $(STACK_LIMIT) && ulimit -Sv $(MEM_LIMIT) &&
RUN = -$(ULIMIT) $(TIMEOUT) $(TIME)
TABULATE = ../../tabulate.sh

TOOLS = genmcsc optimal pop

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
