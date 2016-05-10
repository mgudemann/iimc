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
#include "Slice.h"
#include "Util.h"

using namespace std;

namespace {

ID var(Expr::Manager::View & ev, ID lit) {
  Expr::Op op = ev.op(lit);
  if (op == Expr::Var)
    return lit;
  else {
    assert (op == Expr::Not);
    return var(ev, ev.apply(Expr::Not, lit));
  }
}

void printVector(Expr::Manager::View & ev, const vector<ID> & c) {
  for (vector<ID>::const_iterator it = c.begin(); it != c.end(); it++)
    cout << Expr::stringOf(ev, *it) << " ";
  cout << endl;
}

int slice(SAT::Manager::View * init, SAT::Manager::View * cons, Expr::Manager::View & ev,
          set<ID> & sliced, const vector<ID> & stateVars,
          const vector<ID> & startBits, SAT::Manager::View * other,
          vector< vector<ID> > & constraints, int timeout, int64_t startTime,
          Options::Verbosity v) {

  int total = 0;
  int iter = 0;
  int found;
  do {
    found = 0;
    for (vector<ID>::const_iterator it = stateVars.begin(); it != stateVars.end(); ++it) {
      if(!startBits.empty() && *it == startBits[0])
        continue;
      for (int i = 0; i < 2; ++i) {
        if (timeout > 0) {
          double elapsed = (Util::get_user_cpu_time() - startTime) / 1000000.0;
          if (elapsed > timeout)
            throw Timeout("");
        }
        ID lit = i == 0 ? *it : ev.apply(Expr::Not, *it);
        if(sliced.find(lit) != sliced.end())
          continue;
        vector<ID> cube(1, ev.apply(Expr::Not, lit));
        cube.insert(cube.end(), startBits.begin(), startBits.end());

        //Check initiation
        if (init->sat(&cube))
          continue;

        //Check consecution
        SAT::GID gid = cons->newGID();
        vector<ID> cls;
        Expr::complement(ev, cube, cls);
        cons->add(cls, gid);
        vector<ID> assumps;
        for (vector<ID>::const_iterator it2 = cube.begin(); it2 != cube.end(); ++it2)
          assumps.push_back(primeFormula(ev, *it2));

        bool sat = cons->sat(&assumps);
        cons->remove(gid);
        if (!sat) {
          //Inductive invariant
          if (v > Options::Verbose)
            printVector(ev, cls);

          sliced.insert(lit);
          ++found;
          ++total;
          constraints.push_back(cls);
          //Add to the SAT databases
          cons->add(cls);
          other->add(cls);
          Expr::primeFormulas(ev, cls);
          cons->add(cls);
          other->add(cls);
        }
      }
    }
    if (v > Options::Informative)
      cout << "Iter " << iter << ": found " << found << " inductive invariants" << endl;
    ++iter;
  } while (found != 0);

  if (v > Options::Informative)
    cout << "Total = " << total << endl;
  return total;

}

}

void SliceAction::exec() {

  int64_t startTime = Util::get_user_cpu_time();

  Model & m = model();

  Expr::Manager::View * v = model().newView();
  Expr::Manager::View & ev = *v;

  const string sig = "Slice: ";

  //Detect start bit(s)
  if(m.verbosity() > Options::Terse)
    cout << sig << "Checking for start bit(s)..." << endl;
  vector<ID> startBits;
  ExprAttachment const * const eat = (ExprAttachment const *)
                                     m.constAttachment(Key::EXPR);
  ID npi = eat->outputFns()[0];
  if (npi == ev.btrue() || npi == ev.bfalse()) {
    //Leave it to the proof engines to declare the solve
    m.constRelease(eat);
    delete v;
    if (m.verbosity() > Options::Silent)
      cout << sig << "trivial property" << endl;
    return;
  }
  const vector<ID> & stateVars = eat->stateVars();
  for(vector<ID>::const_iterator it = stateVars.begin(); it != stateVars.end();
      ++it) {
    ID nsf = eat->nextStateFnOf(*it);
    if(nsf == ev.btrue()) {
      startBits.push_back(*it);
      if(m.verbosity() > Options::Terse)
        cout << sig << Expr::stringOf(ev, *it) << endl;
    }
  }
  assert(startBits.size() <= 1); //Assumes SequentialEquivalence has run before

  CNFAttachment const * const cnfat = (CNFAttachment const *) m.constAttachment(Key::CNF);
  vector< vector<ID> > tr = cnfat->getPlainCNF();
  vector< vector<ID> > revtr = cnfat->getPlainCNF();
  m.constRelease(cnfat);

  // switch primed and unprimed vars for the reverse transition relation
  set<ID> tpv(stateVars.begin(), stateVars.end());
  set_union(tpv.begin(), tpv.end(), eat->inputs().begin(), eat->inputs().end(), inserter(tpv, tpv.end()));
  for (vector< vector<ID> >::iterator cl = revtr.begin(); cl != revtr.end(); ++cl) {
    for (vector<ID>::iterator lit = cl->begin(); lit != cl->end(); ++lit) {
      ID v = var(ev, *lit);
      if (tpv.find(v) != tpv.end())
        *lit = *lit == v ? ev.prime(v) : ev.apply(Expr::Not, ev.prime(v));
      else if (ev.nprimes(v))
        *lit = *lit == v ? ev.unprime(v) : ev.apply(Expr::Not, ev.unprime(v));
    }
  }

  int timeout = m.options()["slice_timeout"].as<int>();

  SAT::Manager * forwardConsM = m.newSATManager();
  SAT::Manager::View * forwardCons = forwardConsM->newView(ev);
  forwardCons->add(tr);
  forwardCons->timeout(timeout);

  SAT::Manager * reverseConsM = m.newSATManager();
  SAT::Manager::View * reverseCons = reverseConsM->newView(ev);
  reverseCons->add(revtr);
  reverseCons->timeout(timeout);

  SAT::Manager * forwardInitM = m.newSATManager();
  SAT::Manager::View * forwardInit = forwardInitM->newView(ev);
  const vector<ID> & init = eat->initialConditions();
  for (vector<ID>::const_iterator it = init.begin(); it != init.end(); ++it) {
    vector<ID> cls;
    cls.push_back(*it);
    forwardInit->add(cls);
  }
  forwardInit->timeout(timeout);

  SAT::Manager * reverseInitM = m.newSATManager();
  SAT::Manager::View * reverseInit = reverseInitM->newView(ev);
  SAT::Clauses npi_cnf;
  Expr::tseitin(ev, npi, npi_cnf);
  reverseInit->add(npi_cnf);
  reverseInit->timeout(timeout);

  vector<ID> constraints = eat->constraintFns();
  vector< vector<ID> > constraint_clauses;
  Expr::tseitin(ev, constraints, constraint_clauses);
  forwardInit->add(constraint_clauses);
  reverseInit->add(constraint_clauses);
  m.constRelease(eat);

  if(m.verbosity() > Options::Silent)
    cout << sig << "Checking for inductive invariants..." << endl;

  int found;
  set<ID> sliced;
  vector< vector<ID> > discConstraints;
  bool first = true;
  do {
    if (m.verbosity() > Options::Informative)
      cout << sig << "Reverse:" << endl;
    //Reverse iteration
    try {
      found = slice(reverseInit, reverseCons, ev, sliced, stateVars, startBits,
                    forwardCons, discConstraints, timeout, startTime, m.verbosity());
    }
    catch (Timeout const & t) {
      if (m.verbosity() > Options::Silent)
        cout << sig << "Timeout" << endl;
      break;
    }
    if (!first && found == 0)
      break;
    if (m.verbosity() > Options::Informative)
      cout << sig << "Forward:" << endl;
    //Forward iteration
    try {
      found = slice(forwardInit, forwardCons, ev, sliced, stateVars, startBits,
                    reverseCons, discConstraints, timeout, startTime, m.verbosity());
    }
    catch (Timeout const & t) {
      if (m.verbosity() > Options::Silent)
        cout << sig << "Timeout" << endl;
      break;
    }

    first = false;
  } while (found != 0);

  if (!discConstraints.empty()) {
    auto eat = m.attachment<ExprAttachment>(Key::EXPR);
    int i = constraints.size();
    for (vector< vector<ID> >::const_iterator it = discConstraints.begin();
         it != discConstraints.end(); ++it, ++i) {
      //Add constraint to model
      ostringstream oss;
      oss << "_dc_" << i;
      ID discConstr = ev.newVar(oss.str());
      vector<ID> cube;
      Expr::complement(ev, *it, cube);
      eat->addConstraint(discConstr, ev.apply(Expr::Not, 
                                     ev.apply(Expr::And, cube)));
    }

    m.release(eat);
  }

  delete v;
  delete forwardInit;
  delete forwardInitM;
  delete reverseInit;
  delete reverseInitM;
  delete forwardCons;
  delete forwardConsM;
  delete reverseCons;
  delete reverseConsM;

  if (m.verbosity() > Options::Silent)
    cout << sig << "Total inductive invariants = " << discConstraints.size() << endl;
  if (m.verbosity() > Options::Terse)
    cout << sig << "Spent "
         << (Util::get_user_cpu_time() - startTime) / 1000000.0 << "s" << endl;

};
