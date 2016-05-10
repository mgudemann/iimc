expressions_Expr_sources = \
  src/expressions/Expr.cpp \
  src/expressions/ExprUtil.cpp \
  src/expressions/Expr.h \
  src/expressions/ExprUtil.h \
  src/expressions/ExprNode.h \
  src/expressions/ExprTypes.h \
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
