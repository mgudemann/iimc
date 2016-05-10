copt_Copt_sources = \
  src/copt/SATSweep.cpp \
  src/copt/SATSweep.h \
  src/copt/CombAttachment.cpp \
  src/copt/CombAttachment.h \
  $(copt_AIG_sources) \
  $(copt_CutSweep_sources)

copt_AIG_sources = \
  src/copt/AIGUtil.cpp \
  src/copt/AIGUtil.h \
  src/copt/AIG.cpp \
  src/copt/AIG.h \
  src/copt/AIGAttachment.cpp \
  src/copt/AIGAttachment.h \
  src/copt/UniqueIntegralType.h

copt_CutSweep_sources = \
  src/copt/CutSweep.cpp \
  src/copt/CutSweep.h

iimc_SOURCES += $(copt_Copt_sources)

AM_CPPFLAGS += -I$(srcdir)/src/copt
