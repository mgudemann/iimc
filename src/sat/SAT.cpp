/********************************************************************
Copyright (c) 2010-2015, Regents of the University of Colorado

All rights reserved.

Redistribution and use in source and binary forms, with or without
modification, are permitted provided that the following conditions
are met:

Redistributions of source code must retain the above copyright
notice, this list of conditions and the following disclaimer.

Redistributions in binary form must reproduce the above copyright
notice, this list of conditions and the following disclaimer in the
documentation and/or other materials provided with the distribution.

Neither the name of the University of Colorado nor the names of its
contributors may be used to endorse or promote products derived from
this software without specific prior written permission.

THIS SOFTWARE IS PROVIDED BY THE COPYRIGHT HOLDERS AND CONTRIBUTORS
"AS IS" AND ANY EXPRESS OR IMPLIED WARRANTIES, INCLUDING, BUT NOT
LIMITED TO, THE IMPLIED WARRANTIES OF MERCHANTABILITY AND FITNESS
FOR A PARTICULAR PURPOSE ARE DISCLAIMED. IN NO EVENT SHALL THE
COPYRIGHT OWNER OR CONTRIBUTORS BE LIABLE FOR ANY DIRECT, INDIRECT,
INCIDENTAL, SPECIAL, EXEMPLARY, OR CONSEQUENTIAL DAMAGES (INCLUDING,
BUT NOT LIMITED TO, PROCUREMENT OF SUBSTITUTE GOODS OR SERVICES;
LOSS OF USE, DATA, OR PROFITS; OR BUSINESS INTERRUPTION) HOWEVER
CAUSED AND ON ANY THEORY OF LIABILITY, WHETHER IN CONTRACT, STRICT
LIABILITY, OR TORT (INCLUDING NEGLIGENCE OR OTHERWISE) ARISING IN
ANY WAY OUT OF THE USE OF THIS SOFTWARE, EVEN IF ADVISED OF THE
POSSIBILITY OF SUCH DAMAGE.
********************************************************************/

#include "Error.h"
#include "SAT.h"
#include "Util.h"

#include "SAT_minisat.h"
#ifndef DISABLE_ZCHAFF
#include "SAT_zchaff.h"
#endif

#include <algorithm>
#include <assert.h>

using namespace std;

namespace SAT {

  uint64_t Manager::sat_time = 0;
  unsigned int Manager::sat_count = 0;

  bool isValidBackend(const std::string & backend) {
    return (
#ifndef DISABLE_ZCHAFF
      backend == "zchaff" ||
#endif
      backend == "minisat");
  }

  Solver toSolver(const std::string & backend) {
    assert(isValidBackend(backend));
    if (backend == "minisat")
      return MINISAT;
#ifndef DISABLE_ZCHAFF
    if (backend == "zchaff")
      return ZCHAFF;
#endif
    assert(false);
  }


  Manager::Manager(Expr::Manager & _man, bool track_time) : 
    exprMan(_man), tt(track_time) {}
  Manager::~Manager() {
    assert (views.size() == 0);
  }

  bool Manager::add(Clause & clause) throw(Trivial) {
#ifdef MTHREADS
    MMuxType::scoped_lock lock(mux);
#endif
    bool trivial = false;
    try {
      for (vector<View *>::iterator it = views.begin(); it != views.end(); it++)
        (*it)->add(clause);
    }
    catch (Trivial tv) {
      if (!tv.value())
        throw tv;
      trivial = true;
    }
    if (!trivial) clauses.push_back(clause);
    return true;
  }

  bool Manager::add(Clauses & clauses) throw(Trivial) {
    for (Clauses::iterator it = clauses.begin(); it != clauses.end(); it++)
      add(*it);
    return true;
  }

  Manager::View * Manager::newView(Expr::Manager::View & exprView, Solver solver) {
#ifdef MTHREADS
    MMuxType::scoped_lock lock(mux);
#endif

#ifdef DISABLE_ZCHAFF
    View * v = new MinisatView(*this, exprView);
#else
    View * v;
    if (solver == ZCHAFF)
      v = new ZchaffView(*this, exprView);
    else
      v = new MinisatView(*this, exprView);
#endif
    views.push_back(v);
    v->add(clauses);
    return v;
  }

  Manager::View * Manager::newView(Expr::Manager::View & exprView, string solver) {
    return newView(exprView, toSolver(solver));
  }


  Manager::View::~View() {
#ifdef MTHREADS
    MMuxType::scoped_lock lock(man.mux);
#endif
    for (vector<Manager::View *>::iterator it = man.views.begin();
         it != man.views.end();
         it++)
      if (*it == this) {
        man.views.erase(it);
        break;
    }
  }

  bool Manager::View::add(Clauses & clauses, GID gid) throw(Trivial) {
    for (Clauses::iterator it = clauses.begin(); it != clauses.end(); it++)
      try {
        add(*it, gid);
      }
      catch (Trivial tv) {
        if (!tv.value())
          throw tv;
      }
    return true;
  }

  void Manager::View::cleanClause(Clause & clause) {
    exprView.sort(clause.begin(), clause.end());
    for (Clause::iterator it = clause.begin(); it != clause.end(); ) {
      if (*it == exprView.btrue())
        // [true lit]
        throw Trivial(true);
      else if (*it == exprView.bfalse())
        // [false lit]
        clause.erase(it);
      else if (it+1 != clause.end()) {
        if (*it == *(it+1)) {
          // [repetition of lit]
          clause.erase(it);
        }
        else if (*it == exprView.apply(Expr::Not, *(it+1)))
          // [var with both phases]
          // Relies on how Expr handles negation, so possibly a hack.
          // However, I meant for this property to be usable, so it
          // will be maintained.
          throw Trivial(true);
        else
          it++;
      }
      else
        it++;
    }
    if (clause.size() == 0)
      // empty clause
      throw Trivial(false);
  }
}
