SUBDIRS =				\
        from_CONCUERROR/lastzero        \
	from_DPU/dispatcher	        \
	from_DPU/multiprodcon	        \
	from_DPU/poke		        \
	from_OBSERVERS/fib_bench        \
	from_OBSERVERS/lastwrite	\
	from_RCMC/readers               \
	from_SATCHECK/linuxrwlocks	\
	from_SCTBench/reorder	 	\
	from_TRACER/exponential_bug     \
	from_TRACER/redundant_co        \
	from_TRUST/exp-mem3             \
	SV-COMP/szymanski               \
	synthetic/thread_parametric     \
	from_DCDPOR/opt_lock		\
	from_DCDPOR/parker              \
	from_OBSERVERS/floating_read 	\
	from_OBSERVERS/lamport          \
	from_SATCHECK/linuxlocks	\
	other/approxds_append		\

#	from_SCTBench/circular_buffer 	\
	from_TRACER/control_flow 	\
	from_TRACER/filesystem		\
	from_TRUST/exp-mem              \
	SV-COMP/fibonacci               \
	SV-COMP/indexer                 \
	SV-COMP/sigma                   \
	synthetic/length_parametric     \
	synthetic/race_parametric       \
# T ?= all

all: $(SUBDIRS)

$(SUBDIRS):
	$(MAKE) -C $@ $(T)

mrproper:
	for d in $(SUBDIRS); do \
		$(MAKE) -C$$d mrproper; \
	done

.PHONY: $(SUBDIRS) all mrproper
