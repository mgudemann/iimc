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

#ifndef _SAT_
#define _SAT_

/** @file SAT.h */

#include "Expr.h"
#include "ExprUtil.h"

#include <unordered_map>
#include <vector>

#ifdef MTHREADS
#include "tbb/mutex.h"
#include "tbb/spin_mutex.h"
#endif

/** Namespace of SAT. */
namespace SAT {

  enum Solver {
#ifndef DISABLE_ZCHAFF
    ZCHAFF,
#endif
    MINISAT};

  bool isValidBackend(const std::string & backend);

  Solver toSolver(const std::string & backend);

  typedef Expr::IDVector Clause;
  typedef std::vector<Expr::IDVector> Clauses;
  typedef const void * GID;
  const GID NULL_GID = 0;

  class Trivial {
  public:
    Trivial(bool va) : v(va) {}
    bool value() { return v; }
  private:
    bool v;
  };

  /**
   * Defines an assigment, a mapping from variables to AssignVals.
   */
  enum AssignVal {False, True, Unknown};
  typedef std::unordered_map<ID, AssignVal> Assignment;

  /**
   * A thread-safe SAT manager.
   */
  class Manager {
  public:
    /**
     * Creates a Manager over the given Expr::Manager.
     */
    Manager(Expr::Manager & exprMan, bool track_time = false);
    /**
     * Destroys the manager.
     */
    ~Manager();

    /**
     * Adds a clause (permanently) to the global clause database.
     * Returns false if the clause is equivalent to false.
     */
    bool add(Clause & clause) throw(Trivial);

    /**
     * Adds a list of clauses (permanently) to the global clause
     * database.  Returns false if any clause is equivalent to false.
     */
    bool add(Clauses & clauses) throw(Trivial);

    class View;
    /**
     * Creates a thread-local view of the SAT solver over the given
     * Expr::Manager::View.
     */
#ifdef DISABLE_ZCHAFF
    View * newView(Expr::Manager::View & exprView, Solver solver = MINISAT);
#else
    View * newView(Expr::Manager::View & exprView, Solver solver = ZCHAFF);
#endif
    View * newView(Expr::Manager::View & exprView, std::string solver);

    static uint64_t satTime() { return sat_time; }
    static unsigned int satCount() { return sat_count; }

    /**
     * A thread-local view of the SAT solver.
     */
    class View {
      friend class Manager;
    public:
      /**
       * Deletes the view.
       */
      virtual ~View();

      /**
       * Adds a clause to the thread-local clause database with the
       * given Group ID.  Returns false if the clause is equivalent to
       * false.
       */
      virtual bool add(Clause & clause, GID gid = NULL_GID) throw(Trivial) = 0;
      /**
       * Adds a list of clauses to the thread-local clause database
       * with the given Group ID.  Returns false if any clause is
       * equivalent to false.
       */
      bool add(Clauses & clauses, GID gid = NULL_GID) throw(Trivial);

      /**
       * Allocates a new Group ID.
       */
      virtual GID newGID() = 0;
      /**
       * Removes all clauses with the given Group ID.
       */
      virtual void remove(GID gid) = 0;

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
      virtual bool sat(Expr::IDVector * assumptions = NULL, 
               Assignment * asgn = NULL, 
               Expr::IDVector * criticalUnits = NULL, 
               GID gid = NULL_GID,
               bool full_init = false,
               Assignment * lift = NULL) = 0;

      /**
       * Returns this view's manager.
       */
      Manager & manager() { return man; }

      /**
       * Set this view's maximum allotted solving time.
       */
      virtual void timeout(double to = -1.0) = 0;

    protected:
      View(Manager & _man, Expr::Manager::View & _ev) : man(_man), exprView(_ev) { }

      void cleanClause(Clause & clause);

      bool tt() { return man.tt; }
      uint64_t & satTime() { return man.sat_time; }
      unsigned int & satCount() { return man.sat_count; }

      Manager & man;
      Expr::Manager::View & exprView;

#ifdef MTHREADS
      typedef tbb::spin_mutex VMuxType;
      VMuxType mux;
#endif
    };

  private:
    friend class View;

    Expr::Manager & exprMan;

#ifdef MTHREADS
    typedef tbb::mutex MMuxType;
    MMuxType mux;
#endif

    std::vector<View *> views;
    Clauses clauses;

    bool tt;
    static uint64_t sat_time;
    static unsigned int sat_count;
  };

}

#endif
