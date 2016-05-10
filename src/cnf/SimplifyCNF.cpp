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

#include "Expr.h"
#include "ExprUtil.h"
#include "Model.h"
#include "SimplifyCNF.h"

#include "minisat/simp/SimpSolver.h"
#include "minisat/mtl/Vec.h"

using namespace std;

namespace CNF {

  typedef unordered_map<ID, Var> ID2VAR;
  typedef unordered_map<Var, ID> VAR2ID;
  typedef vec< vec<Lit> * > MSCNF;

  void simplify(Model & m,
                const vector< vector<ID> > & in,
                vector< vector<ID> > & out,
                vector<ID> inputs,
                vector<ID> latches,
                vector<ID> fns,
                bool replace)
  {
    ID2VAR id2var;
    VAR2ID var2id;

    Expr::Manager::View * ev = m.newView();

    // 1. load solver with in; build var2id and id2var maps
    SimpSolver solver;
    for (vector< vector<ID> >::const_iterator it = in.begin(); it != in.end(); ++it) {
      vec<Lit> mscl;
      for (vector<ID>::const_iterator lit = it->begin(); lit != it->end(); ++lit) {
        ID v = ev->op(*lit) == Expr::Not ? ev->apply(Expr::Not, *lit) : *lit;
        ID2VAR::iterator vit = id2var.find(v);
        if (vit == id2var.end()) {
          Var msv = solver.newVar();
          pair<ID2VAR::iterator, bool> rv = id2var.insert(ID2VAR::value_type(v, msv));
          var2id.insert(VAR2ID::value_type(msv, v));
          vit = rv.first;
        }
        mscl.push(Lit(vit->second, ev->op(*lit) == Expr::Not));
      }
      solver.addClause(mscl);
    }

    // 2. freeze unprimed and primed latches and inputs
    for (unsigned int i = 0; i < latches.size(); ++i) {
      ID2VAR::iterator vit = id2var.find(latches[i]);
      if (vit != id2var.end())
        solver.setFrozen(vit->second, true);
      ID2VAR::iterator pvit = id2var.find(ev->prime(latches[i]));
      if (pvit != id2var.end())
        solver.setFrozen(pvit->second, true);
    }
    for (unsigned int i = 0; i < inputs.size(); ++i) {
      ID2VAR::iterator vit = id2var.find(inputs[i]);
      if (vit != id2var.end())
        solver.setFrozen(vit->second, true);
      ID2VAR::iterator pvit = id2var.find(ev->prime(inputs[i]));
      if (pvit != id2var.end())
        solver.setFrozen(pvit->second, true);
    }

    // 3. simplify
    solver.eliminate(false, 5);
    MSCNF * mscnf = solver.simplifiedClauses();

    // 4. retrieve clauses and build up out
    set<ID> vars;
    for (int i = 0; i < mscnf->size(); ++i) {
      vec<Lit> * mscl = (*mscnf)[i];
      vector<ID> cl;
      for (int j = 0; j < mscl->size(); ++j) {
        Lit msl = (*mscl)[j];
        Var msv = var(msl);
        VAR2ID::const_iterator it = var2id.find(msv);
        assert (it != var2id.end());
        ID v = it->second;
        vars.insert(v);
        cl.push_back(sign(msl) ? ev->apply(Expr::Not, v) : v);
      }
      out.push_back(cl);
      delete mscl;
    }
    delete mscnf;

    // 5. replace clauses for missing functions
    if (replace)
      for (unsigned int i = 0; i < latches.size(); ++i) {
        ID pv = ev->prime(latches[i]);
        if (vars.find(pv) == vars.end()) {
          if (m.verbosity() > Options::Informative)
            cout << "SimplifyCNF: replacing: " << Expr::stringOf(*ev, pv) << endl;
          // replace clauses
          if (m.options().count("cnf_wilson")) 
            Expr::wilson(*ev, ev->apply(Expr::Equiv, pv, fns[i]), out);
          else
            Expr::tseitin(*ev, ev->apply(Expr::Equiv, pv, fns[i]), out);
        }
      }

    delete ev;
  }

}
