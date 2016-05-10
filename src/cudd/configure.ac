#                                               -*- Autoconf -*-
# Process this file with autoconf to produce a configure script.

AC_PREREQ([2.65])
AC_INIT([cudd], [2.5.1], [Fabio@Colorado.EDU])
AC_CONFIG_AUX_DIR([build-aux])
AC_CANONICAL_HOST
AM_INIT_AUTOMAKE(
  [1.11 -Wall -Werror foreign subdir-objects color-tests silent-rules]
)
AC_CONFIG_SRCDIR([epd.h])
#AC_CONFIG_HEADERS([config.h])

# Checks for programs.
# Set our own default (instead of "-g -O2") unless CXXFLAGS is already defined.
: ${CXXFLAGS="-g -O3"}
# Do the same for CFLAGS.
: ${CFLAGS="-g -O3"}
AC_PROG_CXX
AC_PROG_CC
m4_ifdef([AM_PROG_AR],[AM_PROG_AR])
AC_PROG_RANLIB

# Checks for libraries.

# Checks for header files.
AC_CHECK_HEADERS([float.h math.h assert.h sys/times.h sys/time.h sys/resource.h errno.h])

# Checks for typedefs, structures, and compiler characteristics.
AC_C_INLINE
AC_CHECK_SIZEOF([int])
AC_CHECK_SIZEOF([void *])

# Checks for library functions.
AC_CHECK_LIB([m],[pow])
AC_FUNC_MALLOC
AC_FUNC_REALLOC
AC_CHECK_FUNCS(
  [sysconf memset pow sqrt ceil strchr strstr getrusage getrlimit]
)

# Check for a working implementation of IEEE 754 floating point
# Specifically, check for correct treatment of +Infinity
AC_MSG_CHECKING([for +Infinity (IEEE 754 floating point)])
AC_CACHE_VAL(ac_cv_have_ieee_754,
[ AC_TRY_RUN([
#include <math.h>
main()
{
  if (HUGE_VAL != HUGE_VAL * 3 || HUGE_VAL != HUGE_VAL / 3) return 1;
  return 0;
}
],ac_cv_have_ieee_754=yes,ac_cv_have_ieee_754=no,ac_cv_have_ieee_754=no)])
if test $ac_cv_have_ieee_754 = yes ; then
  AC_MSG_RESULT(working)
  AC_DEFINE(HAVE_IEEE_754)
else
  AC_MSG_RESULT(broken)
fi

AM_CXXFLAGS="-std=c++11 ${AM_CXXFLAGS}"

AC_CONFIG_FILES([Makefile])
AC_OUTPUT
