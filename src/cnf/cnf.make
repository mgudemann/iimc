
cnf_CNF_sources = \
  src/cnf/ISOP.h \
  src/cnf/Cover.h \
  src/cnf/TechMapCNF.h \
  src/cnf/TechMapCNF.cpp \
  src/cnf/CNFTestAction.h \
  src/cnf/CNFDummyAction.h \
  src/cnf/CNFAttachment.h \
  src/cnf/CNFAttachment.cpp \
  src/cnf/DIMACSAction.h \
  src/cnf/DIMACSAction.cpp \
  src/cnf/NiceDAG.h \
  src/cnf/NiceDAG.cpp \
  src/cnf/Cut.h \
  src/cnf/CutAlgorithm.h \
  src/cnf/Cover.cpp \
  src/cnf/SimplifyCNF.h \
  src/cnf/SimplifyCNF.cpp \
  src/cnf/StringTR.h \
  src/cnf/StringTR.cpp

iimc_SOURCES += $(cnf_CNF_sources)

AM_CPPFLAGS += -I$(srcdir)/src/cnf

check_PROGRAMS += test_ISOP
TESTS += test_ISOP

test_ISOP_SOURCES = \
  src/truthtable/TreeTruthTable.h \
  src/truthtable/TreeTruthTable.cpp \
  src/truthtable/BitTruthTable.h \
  src/truthtable/BitTruthTable.cpp \
  src/cnf/ISOP.h \
  src/cnf/Cover.h \
  src/cnf/Cover.cpp \
  src/cnf/test_ISOP.cpp
