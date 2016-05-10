#                                               -*- Autoconf -*-
# Process this file with autoconf to produce a configure script.

AC_PREREQ([2.65])
AC_INIT([iimc], [1.3.2])
AC_CONFIG_AUX_DIR([build-aux])
AC_CANONICAL_HOST
AM_INIT_AUTOMAKE(
  [1.11 -Wall -Werror -Wno-portability foreign subdir-objects color-tests silent-rules]
)
AC_CONFIG_SRCDIR([src/expressions/Expr.cpp])
: ${DOXYGEN_PAPER_SIZE=letter}
DX_INIT_DOXYGEN($PACKAGE_NAME)

# Checks for programs.
# Set our own default (instead of "-g -O2") unless CXXFLAGS is already defined.
: ${CXXFLAGS="-g -O3"}
# Do the same for CFLAGS.
: ${CFLAGS="-g -O3"}
AC_PROG_CXX
AC_PROG_CC
m4_ifdef([AM_PROG_AR],[AM_PROG_AR])
AC_PROG_LEX
AC_PROG_YACC
AM_PROG_CC_C_O

# Use the C++ compiler for the following checks.
AC_LANG([C++])
: ${AM_CXXFLAGS="-Wall"}
# If -std=c++0x is added to CXXFLAGS instead of CPPFLAGS, the tests that
# run the preprocessor do not use this flag.  However, the linker does not
# use CPPFLAGS.  Hence, we add -std=c++0x to LDFLAGS as well.
# We want the tests to use AM_CPPFLAGS and AM_LDFLAGS in addition to
# CPPFLAGS and LDFLAGS.  Hence, we save and restore CPPFLAGS and LDFLAGS.
save_CPPFLAGS=$CPPFLAGS
CPPFLAGS="-std=c++0x $AM_CPPFLAGS $CPPFLAGS"
save_LDFLAGS=$LDFLAGS
LDFLAGS="-std=c++0x $AM_LDFLAGS $LDFLAGS"

# Checks for libraries.

AX_BOOST_BASE(
  [1.40.0],,[AC_MSG_FAILURE([boost could not be located.])]
)
AX_BOOST_PROGRAM_OPTIONS
AX_BOOST_REGEX

# Add an option for disabling zchaff and using MiniSat instead
AC_ARG_ENABLE([zchaff],
              [AC_HELP_STRING([--disable-zchaff],
              [build iimc with MiniSat as the backend SAT solver (default is zchaff)])],
              [case "${enableval}" in
               yes) zchaff=true ;;
               no)  zchaff=false
                    AC_DEFINE([DISABLE_ZCHAFF], [1], Define to 1 to disable zchaff and use MiniSat as the backend SAT solver) ;;
               *) AC_MSG_ERROR(bad value ${enableval} for --enable-zchaff) ;;
               esac],
              [zchaff=true])

AM_CONDITIONAL([ZCHAFF], test x$zchaff = xtrue)

# If the user asks for mutithreading, check for Intel's TBB library.
AC_ARG_WITH([threads],
  [AS_HELP_STRING([--with-threads],
    [build multi-threaded iimc @<:@default=no@:>@])],
    [if test "x$withval" != x; then
      LIBRARY_PATH="$withval/lib:$LIBRARY_PATH"; export LIBRARY_PATH
      DYLD_LIBRARY_PATH="$withval/lib:$DYLD_LIBRARY_PATH"; export DYLD_LIBRARY_PATH
      CPATH="$withval/include:$CPATH"; export CPATH
    fi],
    [with_threads=no])

AS_IF([test "x$with_threads" != xno],
  [AC_MSG_CHECKING([for libtbb])
  [save_libs=$LIBS]
  [LIBS="$LIBS -ltbb -ltbbmalloc -ltbbmalloc_proxy"]
  AC_LINK_IFELSE(
    [AC_LANG_PROGRAM([#include <tbb/tbb.h>],
      [tbb::spin_mutex m; tbb::spin_mutex::scoped_lock lock(m)])],
    [AC_MSG_RESULT([yes])]
    [AC_DEFINE([MTHREADS], [1], 
      [Define to 1 if libtbb is requested and available.])]
    [multithreaded=yes],
    [AC_MSG_RESULT([no])]
    [LIBS=$save_libs]
    [AC_MSG_FAILURE([--with-threads was given, but test for libtbb failed.])])],
)
# Define an Automake conditional so that the test programs that
# require multithreading support may be selectively included.
AM_CONDITIONAL([HAS_THREADS], [test x$multithreaded = xyes])

# Checks for header files.
AC_HEADER_STDBOOL
AC_CHECK_HEADERS(
  [ctime cstdlib cinttypes sys/resource.h sys/time.h sys/utsname.h assert.h]
)

# Checks for typedefs, structures, and compiler characteristics.
AC_TYPE_SIZE_T
AC_TYPE_INT64_T
AC_TYPE_UINT64_T
AC_TYPE_UINTPTR_T
AC_CHECK_SIZEOF([long])
AC_CHECK_SIZEOF([int])
AC_CHECK_SIZEOF([void *])
AC_CHECK_DECLS([_SC_PHYS_PAGES, _SC_AVPHYS_PAGES, _SC_PAGESIZE])

# Checks for library functions.
AC_CHECK_FUNCS([getenv],[],
  AC_MSG_FAILURE([Cannot build without this function.]))
AC_CHECK_FUNCS([sysconf getrusage getrlimit clock uname gethostname])

# We are done with the tests.  Restore CPPFLAGS and LDFLAGS.  Since we are not
# using the stand-alone preprocessor, and we want to pass the -std flag only
# to g++, we now add -std=c++0x to AM_CXXFLAGS.
AM_CXXFLAGS="-std=c++0x ${AM_CXXFLAGS}"
CPPFLAGS=$save_CPPFLAGS
LDFLAGS=$save_LDFLAGS
# On some Red Hat systems the boost libraries are in /usr/local/lib,
# but the loader does not look for dynamic libraries in that directory
# by default.  We add a -R option to change that behavior.
# On Cygwin we want a larger limit for the stack.
# On OS/X we don't want to change the linker options.
AS_CASE([$host],
  [*86*-*-cygwin], [AM_LDFLAGS="$AM_LDFLAGS -Wl,--stack,16777216"],
  [*86*-apple-darwin*], [],
  [AS_CASE([$BOOST_LDFLAGS],
    [*/usr/local/lib], [AM_LDFLAGS="$AM_LDFLAGS -Wl,-R /usr/local/lib"],
    [*/usr/lib64], [AM_LDFLAGS="$AM_LDFLAGS -Wl,-R /usr/lib64"]
  )]
)
# On OS X, getrusage returns the number of bytes instead of the usual
# number of kilobytes.  Yet another case of misplaced creativity.
AS_CASE([$host],
  [*86*-apple-darwin*], [AC_DEFINE([RU_MAXRSS_SCALE], [1],
                         [Scaling factor for the value of ru_maxrss])],
                        [AC_DEFINE([RU_MAXRSS_SCALE], [1024],
                         [Scaling factor for the value of ru_maxrss])]
)

# Distribute additional compiler flags to Makefiles.
AC_SUBST([AM_CPPFLAGS])
AC_SUBST([AM_CXXFLAGS])
AC_SUBST([AM_LDFLAGS])

AC_CONFIG_HEADERS([config.h])
AC_CONFIG_FILES([Makefile Doxyfile])
AC_CONFIG_SUBDIRS([src/cudd src/sat/minisat20 src/sat/zchaff src/sat/minisat])
AC_OUTPUT

echo \
"--------------------------------------------------
Configuration summary for ${PACKAGE_NAME} ${PACKAGE_VERSION}

Build system  : ${build}
Host system   : ${host}
Size of long  : ${ac_cv_sizeof_long:-?} bytes
Prefix        : '${prefix}'
Compiler      : '${CXX} ${AM_CPPFLAGS} ${CPPFLAGS} ${AM_CXXFLAGS} ${CXXFLAGS}'
Multithreaded : ${multithreaded:-no}
--------------------------------------------------"
