SUBDIRS =				\
	from_DPU/dispatcher	        \
	from_DPU/poke		        \
	from_OBSERVERS/lastwrite	\
	from_SCTBench/reorder	 	\
	from_TRACER/redundant_co        \
	from_TRUST/exp-mem3             \
	synthetic/thread_parametric     \
	SV-COMP/indexer                 \

#	from_OBSERVERS/floating_read 	\
	from_OBSERVERS/lamport          \
	from_SATCHECK/linuxlocks	\
	other/approxds_append		\
	from_SCTBench/circular_buffer 	\
	from_DCDPOR/parker              \
	from_DCDPOR/opt_lock		\
	SV-COMP/szymanski               \
	from_TRACER/exponential_bug     \
	from_SATCHECK/linuxrwlocks	\
	from_RCMC/readers               \
	from_OBSERVERS/fib_bench        \
	from_DPU/multiprodcon	        \
	from_TRACER/control_flow 	\
        from_CONCUERROR/lastzero        \
	from_TRACER/filesystem		\
	from_TRUST/exp-mem              \
	SV-COMP/fibonacci               \
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
