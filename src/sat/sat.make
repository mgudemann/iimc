sat_SAT_sources = \
  src/sat/SAT.cpp \
  src/sat/SAT_minisat.cpp \
  src/sat/SAT_minisat.h \
  src/sat/SAT.h

if ZCHAFF
  sat_SAT_sources += \
    src/sat/SAT_zchaff.cpp \
    src/sat/SAT_zchaff.h
endif

iimc_SOURCES += \
  $(sat_SAT_sources)

AM_CPPFLAGS += -Isrc/sat -I$(srcdir)/src/sat
LDADD += src/sat/minisat20/libminisat20.a src/sat/minisat/libminisat.a 
if ZCHAFF
LDADD += src/sat/zchaff/libsat.a
endif

check_PROGRAMS += test_SAT
TESTS += test_SAT

test_SAT_LDADD = $(LDADD) src/parser/aiger19.o

test_SAT_SOURCES = \
  src/sat/test_SAT.cpp \
  $(sat_SAT_sources) \
  $(expressions_Expr_sources) \
  $(model_Model_sources) \
  $(util_Util_sources)
