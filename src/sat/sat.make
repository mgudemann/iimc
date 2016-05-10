sat_SAT_sources = \
  src/sat/SAT.cpp \
  src/sat/SAT.h

iimc_SOURCES += \
  $(sat_SAT_sources)

AM_CPPFLAGS += -Isrc/sat -I$(srcdir)/src/sat
LDADD += src/sat/minisat/libminisat.a
if ZCHAFF
LDADD += src/sat/zchaff/libsat.a
else
LDADD += src/sat/minisat22/libminisat22.a 
endif

check_PROGRAMS += test_SAT
TESTS += test_SAT

test_SAT_SOURCES = \
  src/sat/test_SAT.cpp \
  $(sat_SAT_sources) \
  $(expressions_Expr_sources) \
  $(model_Model_sources) \
  $(util_Util_sources)
