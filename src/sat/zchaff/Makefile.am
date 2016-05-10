AM_CXXFLAGS = -DWLEFT -DNDEBUG

noinst_LIBRARIES = libsat.a

libsat_a_SOURCES = \
  zchaff_utils.cpp \
  zchaff_solver.cpp\
  zchaff_base.cpp \
  zchaff_dbase.cpp \
  zchaff_cpp_wrapper.cpp \
  zchaff_base.h \
  zchaff_clsgen.h \
  zchaff_header.h \
  zchaff_version.h \
  zchaff_dbase.h \
  zchaff_solver.h \
  SAT.h

EXTRA_DIST = zchaff_wrapper.wrp

BUILT_SOURCES = SAT_C.h zchaff_cpp_wrapper.cpp
CLEANFILES = $(BUILT_SOURCES)

zchaff_cpp_wrapper.cpp: zchaff_wrapper.wrp Makefile
	sed 's/EXTERN//' $< > $@

SAT_C.h: SAT.h Makefile
	sed 's/gid = 0/gid/' $< > $@
