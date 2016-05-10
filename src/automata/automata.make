automata_Auto_sources = \
  src/automata/Automaton.h \
  src/automata/AutoWrapper.h \
  src/automata/AutoScanner.ll \
  src/automata/AutoParser.yy \
  src/automata/AutoDriver.h \
  src/automata/AutoDriver.cpp

iimc_SOURCES += $(automata_Auto_sources)

src/automata/AutoParser.$(OBJEXT): src/automata/AutoParser.cc src/automata/AutoParser.hh

AM_LFLAGS += -o$(LEX_OUTPUT_ROOT).c

AM_CPPFLAGS += -I$(srcdir)/src/automata -Isrc/automata

check_PROGRAMS += test_Auto
check_SCRIPTS += test_auto.sh

dist_check_DATA += \
    src/automata/tests/gg.auto \
    src/automata/tests/gx.auto \
    src/automata/tests/multAuto.auto \
    src/automata/tests/multBad.auto \
    src/automata/tests/multInit.auto \
    src/automata/tests/syntaxError.auto

EXTRA_DIST += \
  src/automata/test_auto.sh.in

test_Auto_SOURCES = \
  src/automata/test_Auto.cpp \
  $(automata_Auto_sources) \
  $(expressions_Expr_sources) \
  $(model_Model_sources) \
  $(expressions_Attachment_sources) \
  $(copt_AIG_sources) \
  $(parser_Parser_sources) \
  $(util_Util_sources)

src/automata/AutoParser.hh src/automata/AutoParser.cc: src/automata/AutoParser.yy
	$(YACC) --name-prefix=autoparser -o src/automata/AutoParser.cc $(top_srcdir)/src/automata/AutoParser.yy

src/automata/AutoScanner.cc: $(top_srcdir)/src/automata/AutoScanner.ll src/automata/AutoParser.hh

test_auto.sh: src/automata/test_auto.sh.in
	$(do_subst) $< > $@
	chmod +x $@

CLEANFILES += \
  src/automata/AutoParser.hh \
  src/automata/AutoParser.cc \
  src/automata/AutoScanner.cc \
  src/automata/location.hh \
  src/automata/stack.hh \
  src/automata/position.hh
