AM_CFLAGS =
AM_CXXFLAGS = $(AM_CFLAGS)

noinst_LIBRARIES = libutil.a libst.a libmtr.a libepd.a libcudd.a libobj.a

libutil_a_SOURCES = cpu_stats.c cpu_time.c datalimit.c \
  prtime.c safe_mem.c qsort.c util.h

libst_a_SOURCES = st.h st.c

libmtr_a_SOURCES = mtrBasic.c mtrGroup.c mtr.h mtrInt.h

libepd_a_SOURCES = epd.c epd.h

libcudd_a_SOURCES = cudd.h cuddInt.h \
  cuddAPI.c cuddAddAbs.c cuddAddApply.c cuddAddFind.c cuddAddIte.c \
  cuddAddInv.c cuddAddNeg.c cuddAddWalsh.c cuddAndAbs.c \
  cuddAnneal.c cuddApa.c cuddApprox.c cuddBddAbs.c cuddBddCorr.c \
  cuddBddIte.c cuddBridge.c cuddCache.c cuddCheck.c cuddClip.c \
  cuddCof.c cuddCompose.c cuddDecomp.c cuddEssent.c \
  cuddExact.c cuddExport.c cuddGenCof.c cuddGenetic.c \
  cuddGroup.c cuddHarwell.c cuddInit.c cuddInteract.c \
  cuddLCache.c cuddLevelQ.c \
  cuddLinear.c cuddLiteral.c cuddMatMult.c cuddPriority.c \
  cuddRead.c cuddRef.c cuddReorder.c cuddSat.c cuddSign.c \
  cuddSolve.c cuddSplit.c cuddSubsetHB.c cuddSubsetSP.c cuddSymmetry.c \
  cuddTable.c cuddUtil.c cuddWindow.c cuddZddCount.c cuddZddFuncs.c \
  cuddZddGroup.c cuddZddIsop.c cuddZddLin.c cuddZddMisc.c \
  cuddZddPort.c cuddZddReord.c cuddZddSetop.c cuddZddSymm.c \
  cuddZddUtil.c

libobj_a_SOURCES = cuddObj.cc cuddObj.hh

check_PROGRAMS = testmtr testcudd testobj
check_SCRIPTS = test_mtr.sh test_cudd.sh

testmtr_SOURCES = testmtr.c
testmtr_LDADD = libmtr.a libutil.a

testcudd_SOURCES = testcudd.c
testcudd_LDADD = libcudd.a libst.a libepd.a $(testmtr_LDADD)

testobj_SOURCES = testobj.cc
testobj_LDADD = libobj.a $(testcudd_LDADD)

dist_check_DATA = test.groups r7x8.1.mat
EXTRA_DIST = test_mtr.sh.in test_cudd.sh.in
CLEANFILES = $(check_SCRIPTS)

do_subst = sed \
  -e 's,[@]EXEEXT[@],$(EXEEXT),g' \
  -e 's,[@]srcdir[@],$(srcdir),g'

test_mtr.sh: test_mtr.sh.in Makefile
	$(do_subst) $< > $@
	chmod +x $@

test_cudd.sh: test_cudd.sh.in Makefile
	$(do_subst) $< > $@
	chmod +x $@

TESTS = $(check_SCRIPTS) testobj
