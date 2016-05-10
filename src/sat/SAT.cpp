/********************************************************************
Copyright (c) 2010-2012, Regents of the University of Colorado

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

#ifndef USE_MINISAT
#include "zchaff/SAT_C.h"
#endif

#include <algorithm>
#include <assert.h>

using namespace std;

namespace SAT {

#ifdef USE_MINISAT
  enum {TIMEOUT, UNSATISFIABLE, SATISFIABLE};
#endif

  uint64_t Manager::sat_time = 0;
  unsigned int Manager::sat_count = 0;

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

  Manager::View * Manager::newView(Expr::Manager::View & exprView) {
#ifdef MTHREADS
    MMuxType::scoped_lock lock(mux);
#endif
    View * v = new View(*this, exprView);
    views.push_back(v);
    v->add(clauses);
    return v;
  }

  Manager::View::View(Manager & _man, Expr::Manager::View & _eview) :
    man(_man), exprView(_eview)
  {
#ifndef USE_MINISAT
    satMan = SAT_InitManager();
    SAT_SetRandomness(satMan, 2);
#endif
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
#ifndef USE_MINISAT
    SAT_ReleaseManager(satMan);
#endif
  }

  bool Manager::View::add(Clause & clause, GID gid) throw(Trivial) {
    assert (clause.size() < MAX_LITS);

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

#ifdef MTHREADS
    { VMuxType::scoped_lock lock(mux);
#endif
#ifdef USE_MINISAT
      Minisat::vec<Minisat::Lit> lits(clause.size());
#endif
      int i = 0;
      for (Clause::iterator it = clause.begin(); it != clause.end(); ++i, it++) {
        ID v = *it;
        bool pos = true;
        if (exprView.op(v) != Expr::Var) {
          int _n;
          const ID * const _args = exprView.arguments(v, &_n);
          v = _args[0];
          pos = false;
        }
        VMap::iterator mapIt = vmap.find(v);
        if (mapIt == vmap.end()) {
#ifdef USE_MINISAT
          Minisat::Var vi = satMan.newVar();
#else
          int vi = SAT_AddVariable(satMan);
#endif
          pair<VMap::iterator, bool> rv = vmap.insert(VMap::value_type(v, vi));
          mapIt = rv.first;
          ivmap.insert(IVMap::value_type(vi, v));
        }
#ifdef USE_MINISAT
        Minisat::Var sv = mapIt->second;
        lits[i] = Minisat::mkLit(sv, !pos);
#else
        int sv = mapIt->second;
        _lits[i] = 2*sv + (pos ? 0 : 1);
#endif
      }
#ifdef USE_MINISAT
      if(gid != NULL_GID)
        lits.push(~gid);
      satMan.addClause(lits);
#else
      SAT_AddClause(satMan, _lits, clause.size(), gid);
#endif
      return true;
#ifdef MTHREADS
    }
#endif
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

  GID Manager::View::newGID() {
#ifdef USE_MINISAT
    Minisat::Var v =  satMan.newVar();
    Minisat::Lit act = Minisat::mkLit(v, false);
    //Add the variable to the list of assumptions
    _assumps.insert(act);
    return act;
#else
    return SAT_AllocClauseGroupID(satMan);
#endif
  }

  void Manager::View::remove(GID gid) {
#ifdef USE_MINISAT
    //Remove the activation literal from the assumptions
    _assumps.erase(gid);
    //Add a unit clause permanently
    satMan.addClause(~gid);
#else
    SAT_DeleteClauseGroup(satMan, gid);
#endif
  }

  bool Manager::View::sat(Expr::IDVector * assump, Assignment * asgn, 
                          Expr::IDVector * crits, GID gid, bool full_init, 
                          Assignment * lift)
  {
#ifdef USE_MINISAT
    Minisat::vec<Minisat::Lit> assumps;
    for(set<Minisat::Lit>::const_iterator it = _assumps.begin();
        it != _assumps.end(); ++it) {
      assumps.push(*it);
    }
    if (assump != NULL) {
      //Add the user provided assumptions to the list of assumptions
      for(vector<ID>::const_iterator it = assump->begin(); it != assump->end();
          ++it) {
        ID v = *it;
        bool pos = true;
        if (exprView.op(v) != Expr::Var) {
          int _n;
          const ID * const _args = exprView.arguments(v, &_n);
          v = _args[0];
          pos = false;
        }
        VMap::iterator vit = vmap.find(v);
        if(vit != vmap.end()) {
          Minisat::Var mv = vit->second;
          assumps.push(Minisat::mkLit(mv, !pos));
        }
      }
    }
#else
    SAT_Reset(satMan);

    int agid = -1;
    if (assump != NULL) {
      agid = gid > 0 ? gid : SAT_AllocClauseGroupID(satMan);
      Clause cl(1);
      for (Expr::IDVector::iterator it = assump->begin(); it != assump->end(); it++) {
        cl[0] = *it;
        add(cl, agid);
      }
    }
#endif

    bool result = false;
    int64_t stime = man.tt ? Util::get_user_cpu_time() : 0;
#ifdef USE_MINISAT
    Minisat::lbool ret = satMan.solveLimited(assumps);
    int status;
    if(ret == l_True)
      status = SATISFIABLE;
    else if(ret == l_False)
      status = UNSATISFIABLE;
    else
      status = TIMEOUT;
#else
    int status = SAT_Solve(satMan, full_init);
#endif
    int64_t etime = man.tt ? Util::get_user_cpu_time() : 0;
    man.sat_time += (etime - stime);
    man.sat_count++;
    if (status == UNSATISFIABLE) {
      if (crits != NULL) {
        Expr::IDVector ua;
#ifdef USE_MINISAT
        const Minisat::vec<Minisat::Lit> & conf = satMan.conflict;
        for (int i = 0; i < conf.size(); ++i) {
          Minisat::Var var = Minisat::var(conf[i]);
          bool neg = Minisat::sign(conf[i]);
          IVMap::iterator it = ivmap.find(var);
          //it is possible that the variable has no corresponding ID which is
          //the case when it is an activation literal
          if(it != ivmap.end()) {
            ID exprVar = it->second;
            //Flip the polarity of the literal since it is coming from the
            //conflict clause
            ua.push_back(neg ? exprVar : exprView.apply(Expr::Not, exprVar));
          }
        }
#else
        int n = SAT_UA(satMan, _lits);
        for (int i = 0; i < n; ++i) {
          bool pos = _lits[i] % 2 == 0;
          int vi = _lits[i] / 2;
          ID v = ivmap.find(vi)->second;
          ua.push_back(pos ? v : exprView.apply(Expr::Not, v));
        }
#endif
        sort(crits->begin(), crits->end());
        sort(ua.begin(), ua.end());
        Expr::IDVector::iterator cit = crits->begin(), uit = ua.begin();
        while (cit != crits->end() && uit != ua.end())
          if (*cit < *uit)
            crits->erase(cit);
          else if (*cit == *uit) {
            cit++; uit++;
          }
          else
            uit++;
        if (cit != crits->end()) 
          crits->erase(cit, crits->end());
      }
    }
    else if (status == SATISFIABLE) {
      result = true;
      if (asgn != NULL) {
        for (Assignment::iterator it = asgn->begin(); it != asgn->end(); it++) {
          VMap::const_iterator vit = vmap.find(it->first);
          if (vit != vmap.end()) {
#ifdef USE_MINISAT
            Minisat::lbool va = satMan.modelValue(vit->second);
            if (va == l_False)
              it->second = False;
            else if (va == l_True)
              it->second = True;
            else
              it->second = Unknown;
#else
            int va = SAT_GetVarAsgnment(satMan, vit->second);
            if (va == 0)
              it->second = False;
            else if (va == 1)
              it->second = True;
            else
              it->second = Unknown;
#endif
          }
          else
            it->second = Unknown;
        }
      }
      if (lift != NULL) {
#ifdef USE_MINISAT
        *lift = *asgn;
#else
        int i = 0;
        for (Assignment::const_iterator it = lift->begin(); it != lift->end(); it++) {
          VMap::const_iterator vit = vmap.find(it->first);
          if (vit != vmap.end()) {
            assert (i < MAX_LITS);
            _lits[i++] = vit->second;
          }
        }
        SAT_Lift(satMan, _lits, i);
        for (Assignment::iterator it = lift->begin(); it != lift->end(); it++) {
          VMap::const_iterator vit = vmap.find(it->first);
          if (vit != vmap.end()) {
            int va = SAT_GetVarAsgnment(satMan, vit->second);
            if (va == 0)
              it->second = False;
            else if (va == 1)
              it->second = True;
            else
              it->second = Unknown;
          }
          else
            it->second = Unknown;
        }
#endif
      }
    }
    else {
      throw Timeout("SAT timed out");
    }

#ifndef USE_MINISAT
    if (assump != NULL && gid == 0)
      SAT_DeleteClauseGroup(satMan, agid);
#endif

    return result;
  }

  void Manager::View::timeout(double to) {
#ifdef USE_MINISAT
    if(to < 0)
      return;
    satMan.setConfBudget(to * 10000);
#else
    SAT_SetTimeLimit(satMan, to);
#endif
  }
}
