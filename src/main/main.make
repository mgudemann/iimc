main_Main_sources = \
  src/main/options.cpp \
  src/main/main.cpp \
  src/main/Dispatch.cpp \
  src/main/Engine.cpp \
  src/main/options.h \
  src/main/Dispatch.h \
  src/main/Engine.h \
  src/main/Verbosity.h

iimc_SOURCES += $(main_Main_sources)

AM_CPPFLAGS += -I$(srcdir)/src/main

check_SCRIPTS += test_iimc.sh

EXTRA_DIST += src/main/test_iimc.sh.in

test_iimc.sh: src/main/test_iimc.sh.in Makefile
	$(do_subst) $< > $@
	chmod +x $@
