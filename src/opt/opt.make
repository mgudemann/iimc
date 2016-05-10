opt_BDD_sources = \
  src/opt/BddAttachment.h \
  src/opt/BddAttachment.cpp \
  src/opt/BddTrAttachment.h \
  src/opt/BddTrAttachment.cpp

iimc_SOURCES += $(opt_BDD_sources)

AM_CPPFLAGS += -I$(srcdir)/src/opt
