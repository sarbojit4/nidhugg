SUBDIRS =			\
	event_driven/nR+nR 	\
	event_driven/n-1R+nW 	\
	event_driven/multilevel_race 	\
	event_driven/fig_3 	\
	event_driven/fig_5 	\
	event_driven/fig_7 	\
	event_driven/inc_msgs3 	\
	event_driven/ordered_posts2 \
	event_driven/ordered_posts3 \
	event_driven/three_handlers \
	event_driven/mat_mult 	\
	event_driven/consensus 	\
	event_driven/n_buyers 	    \
	event_driven/2_phase_commit \
	event_driven/nW 	\
	event_driven/2nW 	\
	event_driven/n2W 	\
	#event_driven/ping_pong 	    \

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
