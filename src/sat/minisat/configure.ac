AC_INIT([minisat], [2.2.0])
AC_CONFIG_AUX_DIR([build-aux])
AM_INIT_AUTOMAKE(
  [1.11 -Wall -Werror foreign subdir-objects color-tests silent-rules]
)
# Set our own default (instead of "-g -O2") unless CXXFLAGS is already defined.
: ${CXXFLAGS="-g -O3"}
AC_PROG_CXX
AC_LANG([C++])
m4_ifdef([AM_PROG_AR],[AM_PROG_AR])
AC_PROG_RANLIB
AC_CONFIG_FILES([Makefile])
AC_OUTPUT
