util_Util_sources = \
  src/util/UtilSystem.cpp \
  src/util/Util.h \
  src/util/Error.h \
  src/util/BitTricks.h

iimc_SOURCES += $(util_Util_sources)
AM_CPPFLAGS += -I$(srcdir)/src/util

check_PROGRAMS += test_Util
TESTS += test_Util

test_Util_SOURCES = \
  src/util/test_Util.cpp \
  $(util_Util_sources)
