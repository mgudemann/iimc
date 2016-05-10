AC_INIT([minisat], [1.0])
AC_CONFIG_AUX_DIR([build-aux])
AM_INIT_AUTOMAKE(
  [-Wall -Werror foreign subdir-objects color-tests silent-rules]
)
# Set our own default (instead of "-g -O2") unless CXXFLAGS is already defined.
: ${CXXFLAGS="-g -O3"}
AC_PROG_CXX
AC_LANG([C++])
AC_PROG_RANLIB
AC_CONFIG_FILES([Makefile])
AC_OUTPUT
