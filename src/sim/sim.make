sim_Sim_sources = \
  src/sim/Sim.cpp \
  src/sim/Sim.h \
  src/sim/ThreeValuedSimulation.cpp \
  src/sim/ThreeValuedSimulation.h

iimc_SOURCES += \
  $(sim_Sim_sources)

AM_CPPFLAGS += -I$(srcdir)/src/sim

