SUBDIRS =				\
        from_CONCUERROR/lastzero        \
        from_TRUST/exp-mem                \
        from_OBSERVERS/fib_bench        \
	from_OBSERVERS/lamport          \
	from_TRACER/filesystem		\
#	SV-COMP/sigma			\
#        synthetic/race_parametric       \
#        other/approxds_append		\
#	from_DCDPOR/parker              \
#	from_SCTBench/circular_buffer 	\
#	from_RCMC/readers
#	from_DCDPOR/opt_lock		\
#	from_TRACER/control_flow 	\
#	from_TRACER/exponential_bug     \
#	from_OBSERVERS/floating_read 	\
#	from_OBSERVERS/lastwrite 	\

# T ?= all

all: $(SUBDIRS)

$(SUBDIRS):
	$(MAKE) -C $@ $(T)

mrproper:
	for d in $(SUBDIRS); do \
		$(MAKE) -C$$d mrproper; \
	done

.PHONY: $(SUBDIRS) all mrproper
