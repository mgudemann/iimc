AM_CXXFLAGS = -ffloat-store

AM_CPPFLAGS = -I$(srcdir)/.. -I$(srcdir)/simp -I$(srcdir)/mcore -I$(srcdir)/mtl

noinst_LIBRARIES = libminisat.a

libminisat_a_SOURCES = \
  simp/SimpSolver.C \
  simp/SimpSolver.h \
  mcore/Solver.C \
  mcore/Solver.h \
  mcore/SolverTypes.h \
  mtl/Alg.h \
  mtl/BasicHeap.h \
  mtl/BoxedVec.h \
  mtl/Heap.h \
  mtl/Map.h \
  mtl/Queue.h \
  mtl/Sort.h \
  mtl/Vec.h

EXTRA_DIST = simp/Main.C
