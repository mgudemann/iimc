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
#include "FCBMC.h"
#include "Util.h"

using namespace std;

namespace FCBMC {

FCBMC::FCBMC(Model & m, const FCBMCOptions & _opts) :
    model(m), opts(_opts), k(1), cnfSize(0) {

  verbosity = opts.silent ? Options::Silent : model.verbosity();

  ExprAttachment const * const eat = (ExprAttachment const *)
      model.constAttachment(Key::EXPR);

  ev = model.newView();

  SAT::Manager * satMan = model.newSATManager();
  if (m.verbosity() > Options::Terse)
    cout << "FCBMC: Using " << opts.backend << " as backend" << endl;
  satView = satMan->newView(*ev, SAT::toSolver(opts.backend));

  //Add initial condition
  const vector<ID> & init = eat->initialConditions();

  for(vector<ID>::const_iterator it = init.begin(); it != init.end(); ++it) {
    SAT::Clause cls;
    cls.push_back(*it);
    satView->add(cls);
    ++cnfSize;
  }

  stateVars = eat->stateVars();
  inputs = eat->inputs();

  fairs = eat->outputFns();

  model.constRelease(eat);

  CNFAttachment const * const cat = (CNFAttachment const *)
      model.constAttachment(Key::CNF);

  tr = cat->getPlainCNF();

  //Add user-constraints
  if(opts.constraints) {
    tr.insert(tr.end(), opts.constraints->begin(), opts.constraints->end());
  }

  model.constRelease(cat);

  addVarsAt(0);
}

FCBMC::~FCBMC() {
  SAT::Manager * satMan = &(satView->manager());
  delete satView;
  delete satMan;
  delete ev;
}

void FCBMC::addVarsAt(int frame) {
  for(vector<ID>::const_iterator it = stateVars.begin(); it != stateVars.end();
      ++it) {
    asgn.insert(SAT::Assignment::value_type(ev->prime(*it, frame), SAT::Unknown));
  }

  for(vector<ID>::const_iterator it = inputs.begin(); it != inputs.end();
      ++it) {
    asgn.insert(SAT::Assignment::value_type(ev->prime(*it, frame), SAT::Unknown));
  }
}

void FCBMC::clearAsgn() {
  for(SAT::Assignment::iterator it = asgn.begin(); it != asgn.end(); ++it) {
    it->second = SAT::Unknown;
  }
}

SAT::Clauses FCBMC::trAt(int frame) {
  SAT::Clauses rv;
  for(SAT::Clauses::const_iterator it = tr.begin(); it != tr.end(); ++it) {
    SAT::Clause cls;
    for(SAT::Clause::const_iterator lit = it->begin(); lit != it->end(); ++lit) {
      cls.push_back(ev->prime(*lit, frame));
    }
    rv.push_back(cls);
  }
  return rv;
}

void FCBMC::extractCex(Lasso & cex) {
  ExprAttachment const * const eat = (ExprAttachment const *)
    model.constAttachment(Key::EXPR);
  vector<Transition> linearCex;
  linearCex.resize(k + 1);
  for(SAT::Assignment::iterator it = asgn.begin(); it != asgn.end(); ++it) {
    if(it->second != SAT::Unknown) {
      ID primed = it->first;
      int numPrimes = ev->nprimes(primed);
      assert(numPrimes <= k);
      ID id = ev->unprime(primed, numPrimes);
      assert(eat->isStateVar(id) || eat->isInput(id));
      vector<ID> & tmp = eat->isStateVar(id) ? linearCex[numPrimes].state :
                                                linearCex[numPrimes].inputs;
      tmp.push_back(it->second == SAT::False ? ev->apply(Expr::Not, id) : id);
    }
  }

  for(vector<Transition>::iterator it = linearCex.begin();
      it != linearCex.end(); ++it) {
    ev->sort(it->state.begin(), it->state.end());
    ev->sort(it->inputs.begin(), it->inputs.end());
  }

  //Find where the trace loops back
  int index;
  for(index = 0; index < k; ++index) {
    if(linearCex[k].state == linearCex[index].state)
      break;
  }
  assert(index < k);
  //State k is the same as state index, therefore stem is from 0 to index - 1,
  //and loop is from index to k - 1
  cex.stem.resize(index);
  cex.loop.resize(k - index);
  copy(linearCex.begin(), linearCex.begin() + index, cex.stem.begin());
  copy(linearCex.begin() + index, linearCex.begin() + k, cex.loop.begin());
  model.constRelease(eat);
}

MC::ReturnValue FCBMC::check(int timeout, int bound, Lasso * cex) {

  int64_t stime = Util::get_user_cpu_time();
  
  if(verbosity > Options::Silent)
    cout << "Fair Cycle BMC: Checking from " << k << endl;

  MC::ReturnValue rv;

  if(bound < 0)
    bound = INT_MAX;

  for(; k <= bound; ++k) {

    if(verbosity > Options::Informative)
      cout << "FCBMC: K = " << k << ", " ;

    //Check for timeout
    if(timeout > 0) {
      int64_t sofar = Util::get_user_cpu_time() - stime;
      if(sofar / 1000000 >= timeout) {
        if(verbosity > Options::Silent) 
          cout << "FCBMC: timeout" << endl;
        rv.returnType = MC::Unknown;
        break;
      }
      double rem = (double) (timeout - sofar / 1000000);
      satView->timeout(rem);
    }

    addVarsAt(k);
    
    //1. Unroll the transition relation
    SAT::Clauses primedTr = trAt(k - 1);
    satView->add(primedTr);
    cnfSize += primedTr.size();

    //2. Add the fair cycle constraints
    vector<ID> disj;

    for(int l = 0; l < k; ++l) {
      //a. State k is the same as state l
      vector<ID> conj;
      for(vector<ID>::const_iterator it = stateVars.begin();
          it != stateVars.end(); ++it) {
        conj.push_back(ev->apply(Expr::Equiv, ev->prime(*it, k),
                                            ev->prime(*it, l)));
      }

      //b. Each fairness constraint is satisfied by some state on the loop 
      //   (l to k-1)
      for(vector<ID>::const_iterator it = fairs.begin();
          it != fairs.end(); ++it) {
        vector<ID> disj2;
        for(int m = l; m < k; ++m) {
          disj2.push_back(primeFormula(*ev, *it, m));
        }
        conj.push_back(ev->apply(Expr::Or, disj2));
      }
      disj.push_back(ev->apply(Expr::And, conj));
    }

    SAT::Clauses fairCycle;
    Expr::wilson(*ev, ev->apply(Expr::Or, disj), fairCycle);
    cnfSize += fairCycle.size();
    if(verbosity > Options::Informative)
      cout << "CNF Size = " << cnfSize << " clauses" << endl;
    SAT::GID gid = satView->newGID();
    try {
      satView->add(fairCycle, gid);
    }
    catch(SAT::Trivial tr) {
      satView->remove(gid);
      continue;
    }

    clearAsgn();
    bool sat;
    try {
      sat = satView->sat(NULL, &asgn);
    }
    catch(Timeout) {
      satView->remove(gid);
      if(verbosity > Options::Silent) 
        cout << "FCBMC: timeout" << endl;
      rv.returnType = MC::Unknown;
      break;
    }
    satView->remove(gid);
    if(sat) {
      if(verbosity > Options::Silent)
        cout << "FCBMC: Counterexample at K = " << k << endl;
      rv.returnType = MC::CEX;
      if(cex) {
        extractCex(*cex);
      }
      break;
    }

  }

  return rv;
}

} //namespace FCBMC
