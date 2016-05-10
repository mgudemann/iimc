mc_MC_sources = \
  src/mc/MC.h \
  src/mc/BMC.cpp \
  src/mc/BMC.h \
  src/mc/COI.h \
  src/mc/COI.cpp \
  src/mc/IC3.h \
  src/mc/IC3.cpp \
  src/mc/FSIS.h \
  src/mc/BddReach.h \
  src/mc/BddReach.cpp \
  src/mc/TacticMisc.h \
  src/mc/TacticMisc.cpp \
  src/mc/ProofAttachment.h \
  src/mc/ProofAttachment.cpp \
  src/mc/RchAttachment.h \
  src/mc/RchAttachment.cpp \
  src/mc/Fair.h \
  src/mc/Fair.cpp \
  src/mc/IICTL.h \
  src/mc/IICTL.cpp \
  src/mc/FCBMC.h \
  src/mc/FCBMC.cpp \
  src/mc/IIC.h \
  src/mc/IIC.cpp \
  src/mc/BddGSH.h \
  src/mc/BddGSH.cpp \
  src/mc/Persist.h \
  src/mc/Persist.cpp \
  src/mc/KLive.h \
  src/mc/KLive.cpp

iimc_SOURCES += $(mc_MC_sources)

AM_CPPFLAGS += -I$(srcdir)/src/mc
