expressions_Expr_sources = \
  src/expressions/Expr.cpp \
  src/expressions/ExprUtil.cpp \
  src/expressions/Expr.h \
  src/expressions/ExprUtil.h \
  src/expressions/Expr_ignore.h \
  src/expressions/ExprBdd.cpp \
  src/expressions/ExprBdd.h \
  src/expressions/ExprVerilog.cpp \
  src/expressions/ExprVerilog.h \
  src/expressions/HashedStructure.h

expressions_Attachment_sources = \
  src/expressions/ExprAttachment.h \
  src/expressions/ExprAttachment.cpp

iimc_SOURCES += \
  $(expressions_Expr_sources) \
  $(expressions_Attachment_sources)

AM_CPPFLAGS += -I$(srcdir)/src/expressions

if HAS_THREADS
check_PROGRAMS += test_Threads
TESTS += test_Threads
test_Threads_LDADD = $(LDADD) src/parser/aiger19.o
test_Threads_SOURCES = \
  src/expressions/test_Threads.cpp \
  $(expressions_Expr_sources) \
  $(model_Model_sources)
endif
