model_Model_sources = \
  src/model/Key.h \
  src/model/Model.cpp \
  src/model/Model.h

iimc_SOURCES += \
  $(model_Model_sources)

AM_CPPFLAGS += -I$(srcdir)/src/model

check_PROGRAMS += \
  test_Model
TESTS += test_Model

test_Model_SOURCES = src/model/test_Model.cpp \
  $(model_Model_sources) \
  $(util_Util_sources) \
  $(expressions_Expr_sources) \
  $(expressions_Attachment_sources) \
  $(opt_BDD_sources) \
  $(copt_Copt_sources) \
  $(truthtable_TruthTable_sources) \
  $(sim_Sim_sources) \
  $(sat_SAT_sources) \
  src/mc/COI.h \
  src/mc/COI.cpp \
  src/mc/BddReach.h \
  src/mc/BddReach.cpp \
  src/mc/ProofAttachment.h \
  src/mc/ProofAttachment.cpp \
  src/mc/RchAttachment.h \
  src/mc/RchAttachment.cpp \
  src/parser/AIGER.cpp \
  src/parser/AIGER.h \
  src/parser/DIMACS.cpp \
  src/parser/DIMACS.h \
  src/parser/aiger19.h \
  src/parser/aiger19.c \
  src/cnf/StringTR.cpp \
  $(properties_Prop_sources)
