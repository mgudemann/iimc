SUBDIRS = src/cudd src/sat/minisat
if ZCHAFF
SUBDIRS += src/sat/zchaff
else
SUBDIRS += src/sat/minisat22 
endif
ACLOCAL_AMFLAGS = -I m4

bin_PROGRAMS = iimc

## Each included file adds to these variables as it sees fit. 
iimc_SOURCES =
AM_CPPFLAGS = @AM_CPPFLAGS@
check_PROGRAMS =
check_SCRIPTS =
EXTRA_DIST = LICENSE LICENSE.zchaff examples/aig19 examples/dimacs examples/ctl
dist_check_DATA =
TESTS =
CLEANFILES =

dist-hook:
	$(foreach i,$(DIST_SOURCES),sed -i -e '/^LICENSE/r $(top_srcdir)/LICENSE' -e '/^LICENSE/d' $(distdir)/$(i);)
	rm -rf `find $(distdir)/examples -name .svn`

LDADD = $(BOOST_LDFLAGS) $(BOOST_PROGRAM_OPTIONS_LIB) \
  src/cudd/libobj.a src/cudd/libcudd.a src/cudd/libepd.a \
  src/cudd/libmtr.a src/cudd/libst.a src/cudd/libutil.a

do_subst = sed \
  -e 's,[@]EXEEXT[@],$(EXEEXT),g' \
  -e 's,[@]srcdir[@],$(srcdir),g'

include $(top_srcdir)/src/util/util.make
include $(top_srcdir)/src/expressions/expressions.make
include $(top_srcdir)/src/model/model.make
include $(top_srcdir)/src/sim/sim.make
include $(top_srcdir)/src/parser/parser.make
include $(top_srcdir)/src/sat/sat.make
include $(top_srcdir)/src/opt/opt.make
include $(top_srcdir)/src/copt/copt.make
include $(top_srcdir)/src/sopt/sopt.make
include $(top_srcdir)/src/truthtable/truthtable.make
include $(top_srcdir)/src/cnf/cnf.make
include $(top_srcdir)/src/properties/properties.make
include $(top_srcdir)/src/mc/mc.make
include $(top_srcdir)/src/main/main.make

AM_CPPFLAGS += $(BOOST_CPPFLAGS) -I$(top_srcdir)/src/cudd -D __STDC_LIMIT_MACROS -D __STDC_FORMAT_MACROS

TESTS += $(check_SCRIPTS)
CLEANFILES += $(check_SCRIPTS)

## Doxygen stuff.
include $(top_srcdir)/aminclude.am
