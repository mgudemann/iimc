sim_Sim_sources = \
  src/sim/Sim.cpp \
  src/sim/Sim.h \
  src/sim/SimUtil.cpp \
  src/sim/SimUtil.h

iimc_SOURCES += \
  $(sim_Sim_sources)

AM_CPPFLAGS += -I$(srcdir)/src/sim

