truthtable_TruthTable_sources = \
  src/truthtable/TreeTruthTable.h \
  src/truthtable/TreeTruthTable.cpp \
  src/truthtable/TurboTruthTable.h \
  src/truthtable/BitTruthTable.h \
  src/truthtable/BitTruthTable.cpp

iimc_SOURCES += $(truthtable_TruthTable_sources)

AM_CPPFLAGS += -I$(srcdir)/src/truthtable

check_PROGRAMS += test_TruthTables
TESTS += test_TruthTables

test_TruthTables_SOURCES = \
  src/truthtable/test_TruthTables.cpp \
  src/truthtable/TreeTruthTable.h \
  src/truthtable/TreeTruthTable.cpp \
  src/truthtable/BitTruthTable.h \
  src/truthtable/BitTruthTable.cpp
