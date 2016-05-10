#                                               -*- Autoconf -*-
# Process this file with autoconf to produce a configure script.

AC_PREREQ([2.65])
AC_INIT([zchaff], [1.0])
AC_CONFIG_AUX_DIR([build-aux])
AM_INIT_AUTOMAKE(
  [1.11 -Wall -Werror foreign subdir-objects color-tests silent-rules]
)
# Set our own default (instead of "-g -O2") unless CXXFLAGS is already defined.
: ${CXXFLAGS="-g -O3"}
AC_PROG_CXX
AC_LANG([C++])
# If -std=c++11 is added to CXXFLAGS instead of CPPFLAGS, the tests that
# run the preprocessor do not use this flag.  However, the linker does not
# use CPPFLAGS.  Hence, we add -std=c++11 to LDFLAGS as well.
: ${AM_CPPFLAGS="-std=c++11"}
: ${AM_LDFLAGS="-std=c++11"}

# Distribute additional compiler flags to Makefiles.
AC_SUBST([AM_CPPFLAGS])
AC_SUBST([AM_CXXFLAGS])
AC_SUBST([AM_LDFLAGS])

AC_PROG_SED
m4_ifdef([AM_PROG_AR],[AM_PROG_AR])
AC_PROG_RANLIB
AC_CONFIG_FILES([Makefile])
AC_OUTPUT

