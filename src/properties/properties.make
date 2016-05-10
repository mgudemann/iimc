properties_Prop_sources = \
  src/properties/PropCtlWrapper.h \
  src/properties/PropCtlScanner.ll \
  src/properties/PropCtlParser.yy \
  src/properties/PropCtlDriver.h \
  src/properties/PropCtlDriver.cpp

iimc_SOURCES += $(properties_Prop_sources)

src/properties/PropCtlParser.$(OBJEXT): src/properties/PropCtlParser.cc src/properties/PropCtlParser.hh

AM_LFLAGS = -o$(LEX_OUTPUT_ROOT).c

AM_CPPFLAGS += -I$(srcdir)/src/properties -Isrc/properties

check_PROGRAMS += test_Prop
check_SCRIPTS += test_prop.sh

dist_check_DATA += \
  src/properties/tests/egefo0.ctl \
  src/properties/tests/reset.ctl \
  src/properties/tests/until.ctl \
  src/properties/tests/response.ctl \
  src/properties/tests/syntaxError.ctl \
  src/properties/tests/reduction.ctl \
  src/properties/tests/mult.ctl

EXTRA_DIST += \
  src/properties/test_prop.sh.in

test_Prop_SOURCES = \
  src/properties/test_Prop.cpp \
  $(properties_Prop_sources) \
  $(expressions_Expr_sources) \
  $(model_Model_sources) \
  $(expressions_Attachment_sources) \
  $(copt_AIG_sources) \
  $(parser_Parser_sources) \
  $(util_Util_sources)

src/properties/PropCtlParser.hh src/properties/PropCtlParser.cc: src/properties/PropCtlParser.yy
	$(YACC) -o src/properties/PropCtlParser.cc $(top_srcdir)/src/properties/PropCtlParser.yy

src/properties/PropCtlScanner.cc: $(top_srcdir)/src/properties/PropCtlScanner.ll src/properties/PropCtlParser.hh

test_prop.sh: src/properties/test_prop.sh.in
	$(do_subst) $< > $@
	chmod +x $@

CLEANFILES += \
  src/properties/PropCtlParser.hh \
  src/properties/PropCtlParser.cc \
  src/properties/PropCtlScanner.cc \
  src/properties/location.hh \
  src/properties/stack.hh \
  src/properties/position.hh
