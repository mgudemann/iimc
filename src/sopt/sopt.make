sopt_SOPT_sources = \
  src/sopt/SeqAttachment.h \
  src/sopt/SeqAttachment.cpp \
  src/sopt/SequentialEquivalence.h \
  src/sopt/SequentialEquivalence.cpp \
  src/sopt/StuckAt.h \
  src/sopt/StuckAt.cpp \
  src/sopt/Simplifier.h \
  src/sopt/Simplifier.cpp \
  src/sopt/PhaseAbstraction.h \
  src/sopt/PhaseAbstraction.cpp \
  src/sopt/AbsInt.h \
  src/sopt/AbsInt.cpp \
  src/sopt/Slice.h \
  src/sopt/Slice.cpp \
  src/sopt/Decode.h \
  src/sopt/Decode.cpp

iimc_SOURCES += $(sopt_SOPT_sources)

AM_CPPFLAGS += -I$(srcdir)/src/sopt
