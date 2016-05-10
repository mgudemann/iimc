parser_Parser_sources = \
  src/parser/AIGER.cpp \
  src/parser/AIGER.h \
  src/parser/DIMACS.cpp \
  src/parser/DIMACS.h \
  src/parser/aiger19.h \
  src/parser/aiger19.c

iimc_SOURCES += $(parser_Parser_sources)

AM_CPPFLAGS += -I$(srcdir)/src/parser

check_PROGRAMS += test_Parser
TESTS += test_Parser

test_Parser_SOURCES = \
  src/parser/test_Parser.cpp \
  $(parser_Parser_sources) \
  src/expressions/Expr.cpp \
  src/expressions/ExprUtil.cpp \
  src/model/Model.cpp \
  $(expressions_Attachment_sources) \
  $(copt_AIG_sources) \
  $(sat_SAT_sources) \
  src/expressions/ExprVerilog.cpp \
  src/expressions/ExprVerilog.h \
  src/util/UtilSystem.cpp
