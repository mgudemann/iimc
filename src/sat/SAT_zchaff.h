/* -*- C++ -*- */

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

#ifndef _SAT_ZCHAFF_
#define _SAT_ZCHAFF_

/** @file SAT_zchaff.h */

#include "Expr.h"
#include "ExprUtil.h"
#include "SAT.h"
#include "zchaff/SAT_C.h"

#include <unordered_map>
#include <vector>

/** Namespace of SAT. */
namespace SAT {

class ZchaffView : public Manager::View {
  friend class Manager;
public:
  /**
   * Deletes the view.
   */
  ~ZchaffView();

  /**
   * Adds a clause to the thread-local clause database with the
   * given Group ID.  Returns false if the clause is equivalent to
   * false.
   */
  bool add(Clause & clause, GID gid = NULL_GID) throw(Trivial);

  /**
   * Allocates a new Group ID.
   */
  GID newGID();
  /**
   * Removes all clauses with the given Group ID.
   */
  void remove(GID gid);

  /**
   * Solves the current SAT problem using the global database, the
   * thread-local database, and the list of given literal
   * assumptions.  If the instance is satisifable, it returns
   * true; and if asgn != NULL, the assignment is stored in the
   * given map.  If the instance is unsatisfiable, it returns
   * false; and if criticalUnits != NULL, the literals in
   * criticalUnits that are used in the proof of unsatisfiability
   * are kept, while all others are removed.  If the same IDVector
   * is used as both assumptions and criticalUnits and the
   * instance is unsatisfiable, the vector contains only the
   * "necessary" literals after the method returns.  [The GID, if
   * provided, is used for handling assumptions in the ZChaff
   * implementation; it can only be used when there is when sat()
   * call involving the clause group.
   */
  bool sat(Expr::IDVector * assumptions = NULL, 
           Assignment * asgn = NULL, 
           Expr::IDVector * criticalUnits = NULL, 
           GID gid = NULL_GID,
           bool full_init = false,
           Assignment * lift = NULL);

  /**
   * Set this view's maximum allotted solving time.
   */
  void timeout(double to = -1.0);

private:
  ZchaffView(Manager & _man, Expr::Manager::View & _ev);
  typedef std::unordered_map<ID, int> VMap;
  typedef std::unordered_map<int, ID> IVMap;
  VMap vmap;
  IVMap ivmap;

  SAT_Manager satMan;

  std::set<int> gids;
};

}

#endif
