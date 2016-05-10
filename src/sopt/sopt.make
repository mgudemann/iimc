sopt_SOPT_sources = \
  src/sopt/SeqAttachment.h \
  src/sopt/SeqAttachment.cpp \
  src/sopt/SequentialEquivalence.h \
  src/sopt/SequentialEquivalence.cpp \
  src/sopt/StuckAt.h \
  src/sopt/StuckAt.cpp \
  src/sopt/ThreeValuedSimulation.h

iimc_SOURCES += $(sopt_SOPT_sources)

AM_CPPFLAGS += -I$(srcdir)/src/sopt
