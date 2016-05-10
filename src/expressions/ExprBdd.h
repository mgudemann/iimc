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

#ifndef _ExprBdd_
#define _ExprBdd_

/** @file ExprBdd.h */

#include <unordered_map>
#include <vector>
#include "Expr.h"
#include "cuddObj.hh"
#include "Model.h"
#include "Verbosity.h"

namespace Expr {
  typedef std::unordered_map<ID, BDD> IdBddMap;
  /**
   * Build the BDD for an expression.
   */
  BDD bddOf(Manager::View& v, ID id, Model const & model, 
            std::unordered_map<ID, int>& orderMap, 
	    std::unordered_map<ID, int>& auxVarMap,
	    unsigned int limit = 0, bool sweep = false,
            Options::Verbosity verbosity = Options::Silent);
  /**
   * Build the BDDs for a set of expressions.
   */
  IdBddMap bddOf(Manager::View & v, std::vector<ID> & ids,
                 Model const & model, std::unordered_map<ID, int>& orderMap,
		 std::unordered_map<ID, int>& auxVarMap,
		 unsigned int limit = 0, bool sweep = false,
                 Options::Verbosity verbosity = Options::Silent);

  /**
   * Build the BDD for an expression.
   * Model-independent version of bddOf.  Does not allow sweeping.
   */
  BDD bddOf(Manager::View & v, ID id, Cudd const & bddMgr,
            std::unordered_map<ID, int>& orderMap,
            std::unordered_map<ID, int>& auxVarMap, unsigned int limit,
            Options::Verbosity verbosity);

  /**
   * Build the BDDs for a set of expressions.
   * Model-independent version of bddOf.  Does not allow sweeping.
   */
  IdBddMap bddOf(Manager::View & v, std::vector<ID> & ids,
                 Cudd const & bddMgr, std::unordered_map<ID, int>& orderMap,
                 std::unordered_map<ID, int>& auxVarMap, unsigned int limit,
                 Options::Verbosity verbosity);

  /**
   * Compute an order for the variables of an expressions.
   */
  std::vector<ID> bddOrderOf(Manager::View& v, ID root);

  /**
   * Compute an order for the variables of a set of expressions.
   */
  std::vector<ID> bddOrderOf(Manager::View& v, std::vector<ID>& roots);

  /**
   * Compute an order for the variables of an expressions.
   */
  std::vector<ID> linearOrderOf(Manager::View& v, ID root);

  /**
   * Compute an order for the variables of a set of expressions.
   */
  std::vector<ID> linearOrderOf(Manager::View& v, std::vector<ID>& roots);
}

#endif
