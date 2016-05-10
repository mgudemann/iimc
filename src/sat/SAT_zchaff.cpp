/********************************************************************
Copyright (c) 2010-2013, Regents of the University of Colorado

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
#include "SAT_zchaff.h"
#include "Util.h"
#include "zchaff/SAT_C.h"

#include <algorithm>
#include <assert.h>

using namespace std;

namespace SAT {

  ZchaffView::ZchaffView(Manager & _man, Expr::Manager::View & _eview) : 
    View(_man, _eview)
  {
    satMan = SAT_InitManager();
    SAT_SetRandomness(satMan, 2);
  }

  ZchaffView::~ZchaffView() {
    SAT_ReleaseManager(satMan);
  }

  bool ZchaffView::add(Clause & clause, GID gid) throw(Trivial) {
    View::cleanClause(clause);

#ifdef MTHREADS
    { VMuxType::scoped_lock lock(mux);
#endif
      int i = 0;
      vector<int> lits(clause.size());
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
          int vi = SAT_AddVariable(satMan);
          pair<VMap::iterator, bool> rv = vmap.insert(VMap::value_type(v, vi));
          mapIt = rv.first;
          ivmap.insert(IVMap::value_type(vi, v));
        }
        int sv = mapIt->second;
        lits[i] = 2*sv + (pos ? 0 : 1);
      }
      SAT_AddClause(satMan, &lits[0], clause.size(), gid ? *(int *) gid : 0);
      return true;
#ifdef MTHREADS
    }
#endif
  }

  GID ZchaffView::newGID() {
    int gid = SAT_AllocClauseGroupID(satMan);
    pair<set<int>::iterator, bool> ret = gids.insert(gid);
    assert(ret.second);
    return &(*(ret.first));
  }

  void ZchaffView::remove(GID gid) {
    int theGid = *(int *) gid;
    SAT_DeleteClauseGroup(satMan, theGid);
    gids.erase(theGid);
  }

  bool ZchaffView::sat(Expr::IDVector * assump, Assignment * asgn, 
                          Expr::IDVector * crits, GID gid, bool full_init, 
                          Assignment * lift)
  {
    SAT_Reset(satMan);

    int agid = -1;
    if (assump != NULL) {
      agid = gid != 0 ? *(int *) gid : SAT_AllocClauseGroupID(satMan);
      Clause cl(1);
      for (Expr::IDVector::iterator it = assump->begin(); it != assump->end(); it++) {
        cl[0] = *it;
        add(cl, &agid);
      }
    }

    bool result = false;
    int64_t stime = View::tt() ? Util::get_user_cpu_time() : 0;
    int status = SAT_Solve(satMan, full_init);
    int64_t etime = View::tt() ? Util::get_user_cpu_time() : 0;
    View::satTime() += (etime - stime);
    View::satCount()++;
    if (status == UNSATISFIABLE) {
      if (crits != NULL) {
        Expr::IDVector ua;
        vector<int> lits;
        SAT_UA(satMan, lits);
        for (unsigned i = 0; i < lits.size(); ++i) {
          bool pos = lits[i] % 2 == 0;
          int vi = lits[i] / 2;
          ID v = ivmap.find(vi)->second;
          ua.push_back(pos ? v : exprView.apply(Expr::Not, v));
        }
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
      }
      if (lift != NULL) {
        vector<int> lits;
        for (Assignment::const_iterator it = lift->begin(); it != lift->end(); it++) {
          VMap::const_iterator vit = vmap.find(it->first);
          if (vit != vmap.end())
            lits.push_back(vit->second);
        }
        SAT_Lift(satMan, &lits[0], lits.size());
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
      }
    }
    else {
      throw Timeout("SAT timed out");
    }

    if (assump != NULL && gid == 0)
      SAT_DeleteClauseGroup(satMan, agid);

    return result;
  }

  void ZchaffView::timeout(double to) {
    SAT_SetTimeLimit(satMan, to);
  }
}
