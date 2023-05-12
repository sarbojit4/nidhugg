SUBDIRS =			\
	event_driven/prolific 	\
	event_driven/writers 	\
	event_driven/posters 	\
	event_driven/buyers 	    \
	event_driven/ping-pong 	    \
	event_driven/2PC \
	event_driven/consensus \
	event_driven/db-cache \
	event_driven/mat-mult \
	event_driven/sparse-mat \
	event_driven/plb

# T ?= all

TABULATE = ./tabulate.sh

all: $(SUBDIRS)

$(SUBDIRS):
	$(MAKE) -C $@ $(T)

all_merged.txt: all
	$(TABULATE) all_merge $(SUBDIRS)

mrproper:
	for d in $(SUBDIRS); do \
		$(MAKE) -C$$d mrproper; \
	done
	rm -f all_merged.txt

.PHONY: $(SUBDIRS) all mrproper
