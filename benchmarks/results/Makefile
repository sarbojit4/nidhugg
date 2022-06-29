SUBDIRS =			\
	event_driven/nW 	\
	event_driven/2nW 	\
	event_driven/n2W 	\
	event_driven/multilevel_race 	\
	event_driven/2_phase_commit \
	event_driven/nR+nR 	\
	event_driven/n-1R+nW 	\
	event_driven/mat_mult 	\
	event_driven/n_buyers 	    \
	event_driven/ping_pong 	    \
	event_driven/consensus 	\

# T ?= all

all: $(SUBDIRS)

$(SUBDIRS):
	$(MAKE) -C $@ $(T)

merge:
	bash merge_table.sh $(SUBDIRS)

mrproper:
	for d in $(SUBDIRS); do \
		$(MAKE) -C$$d mrproper; \
	done

.PHONY: $(SUBDIRS) all mrproper
