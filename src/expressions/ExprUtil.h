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

#ifndef _ExprUtil_
#define _ExprUtil_

/** @file ExprUtil.h */

#include "Expr.h"

#include <set>
#include <sstream>
#include <unordered_map>
#include <unordered_set>

namespace Expr {
  typedef std::unordered_map<ID, ID> IDMap;
  typedef std::unordered_multimap<ID, ID> IDMMap;
  typedef std::vector<ID> IDVector;
  typedef std::unordered_set<ID> IDSet;
  typedef std::unordered_map<ID, IDSet> IDSetMap;

  /**
   * Creates a string representation of the expression.
   */
  std::string stringOf(Manager::View & v, ID id, int indent = 0);

  /**
   * Adds a short string representation of id to buf.
   */
  void shortStringOfID(Manager::View & v, ID id, std::ostringstream & buf);

  /**
   * Adds short string representations of ids in a vector to buf.
   */
  void shortStringOfID(Manager::View & v, IDVector const & ids, std::ostringstream & buf);

  /**
   *
   */
  void disjuncts(Manager::View & v, ID id, IDVector & rv);

  /**
   *
   */
  void conjuncts(Manager::View & v, ID id, IDVector & rv);

  /**
   * Returns true if expression is a clause
   */
  bool isClause(Manager::View & v, ID id, IDVector * lits = NULL);

  void variables(Manager::View & v, ID id, std::set<ID> & rv);
  void variables(Manager::View & v, IDVector & ids, std::set<ID> & rv);

  /**
   * Complement IDVector
   */
  void complement(Manager::View & v, const IDVector & ids, IDVector & rv);

  /**
   * Applies n primes to the variables of expression id.
   */
  ID primeFormula(Manager::View & v, ID id, int n = 1);
  void primeFormulas(Manager::View & v, IDVector & ids, int n = 1);

  /**
   * Applies the variable-substitution map "sub" to expression id.
   */
  ID varSub(Manager::View & v, const IDMap & sub, ID id, IDMap * oldToNew = NULL);
  void varSub(Manager::View & v, const IDMap & sub, IDVector & ids, IDMap * oldToNew = NULL);

  /**
   * Naively converts the expression id to CNF.  The clauses are
   * returned by being pushed onto the back of rv_clauses.
   */
  ID tseitin(Manager::View & v, ID id, std::vector<IDVector> & rv_clauses,
             IDMap* satIdOfId = NULL, bool assert_roots = true);
  void tseitin(Manager::View & v, IDVector & ids,
               std::vector<IDVector> & rv_clauses, IDMap* satIdOfId = NULL,
               bool assert_roots = true);

  void wilson(Manager::View & v, ID id, std::vector<IDVector> & rv_clauses);
  void wilson(Manager::View & v, IDVector & ids, std::vector<IDVector> & rv_clauses);
  /**
   * Adds the immediate containing expression of each subexpression of
   * id.  Use IDMap::equal_range() to retrieve the parents of an
   * expression.
   */
  void parents(Manager::View & v, ID id, IDMMap & map);

  /**
   * Returns the set of (strict) descendants of each subexpression of id. 
   */
  void descendants(Manager::View & v, ID id, IDSetMap & map);

  /**
   * Returns the set of (strict) ancestors of expression "node" that are
   * subexpressions of the expression "id". The ancestors are
   * topologically-sorted.
   */
  void ancestors(Manager::View & v, ID node, ID id, IDVector & ancestors);

  ID AIGOfExpr(Manager::View & v, ID id);
  void AIGOfExprs(Manager::View & v, std::vector<ID> & ids);

  ID AOIOfExpr(Manager::View & v, ID id);
  void AOIOfExprs(Manager::View & v, std::vector<ID> & ids);

  /**
   * Creates a string encoding the expression(s) in dot format.
   */
  std::string dotOf(Manager::View & v,
		    ID id,
		    std::string name = "anonymous",
		    bool terse = true,
		    bool subgraph = false);
  std::string dotOf(Manager::View & v,
		    std::vector<ID>& idv,
		    std::string name = "anonymous",
		    bool terse = true,
		    bool subgraph = false);

  /**
   * Creates a string encoding the circuit graph in dot format.
   */
  std::string circuitGraphOf(Manager::View & v,
                             std::vector<ID>& idv,
                             std::string name = "anonymous",
                             bool terse = true,
                             bool subgraph = false);

  /**
   * Count number of nodes reachable from a root.
   */
  unsigned int sizeOf(Manager::View & v, ID id);
  /**
   * Count number of nodes reachable from set of roots.
   */
  unsigned int sizeOf(Manager::View & v, std::vector<ID>& idv);

  /**
   * Find the SCCs of the circuit graph reachable from the roots.
   */
  std::vector< std::vector<ID> >
  sccsOf(Manager::View & v, std::vector<ID> const & roots,
         std::vector<ID> const & leaves, std::vector<ID> const & nsfv);
  /**
   * Analyze the SCCs of the circuit graph.
   *
   * The SCCs in the COI of the roots (typically the primary outputs)
   * are analyzed and statistics are printed to cout.
   */
  void analyzeSccs(Manager::View & v, std::vector<ID> const & roots,
                   std::vector<ID> const & leaves,
                   std::vector<ID> const & nsfv);

  /** Sorts state variables by the height of the SCC they belong to, where
   * height of leaf SCCs is 0, and the height of any SCC is the maximum of the
   * height of its fanin SCCs + 1 (i.e., the maximum distance to a leaf SCC).
   * The returned vector's first element has the set of state variable IDs
   * having the smallest height. The second element has the set of IDs having
   * the next smallest height, and so on.
   */

  std::vector< std::vector<std::vector<ID> > >
  sortStateVarsBySccHeight(Manager::View & v,
                          std::vector<ID> const & roots,
                          std::vector<ID> const & leaves,
                          std::vector<ID> const & nsfv);

  /** Sorts state variables by the depth of the SCC they belong to, where depth
   * of the output SCC is 0, and the depth of any SCC is the minimum of the
   * depth of all its fanout SCCs + 1 (i.e., the minimum distance to an output
   * SCC). The returned vector's first element has the set of state variable
   * IDs having the shallowest depth. The second element has the set of IDs
   * having the next shallowest depth, and so on.
   */

  std::vector< std::vector<std::vector<ID> > >
  sortStateVarsBySccDepth(Manager::View & v,
                          std::vector<ID> const & roots,
                          std::vector<ID> const & leaves,
                          std::vector<ID> const & nsfv,
                          bool useMaximum = true);

  std::string printSccQuotientGraph(Manager::View & v,
                        std::vector<ID> const & roots,
                        std::vector<ID> const & leaves,
                        std::vector<ID> const & nsfv);


}

#endif
