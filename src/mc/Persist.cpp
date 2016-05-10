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

#include "Persist.h"
#include "Util.h"

using namespace std;

void PersistentSignalsAction::exec() {
  if (model().verbosity() > Options::Terse)
    cout << "PersistentSignalsAction: starting" << endl;
  RchAttachment const * const crat = (RchAttachment const *) model().constAttachment(Key::RCH);
  if (crat->persistentSignalsUpToDate()) {
    if (model().verbosity() > Options::Terse)
      cout << "PersistentSignalsAction: persistent signals up to date" << endl;
    model().constRelease(crat);
    return;
  }

  int64_t startTime = Util::get_user_cpu_time();

  auto rat = model().attachment<RchAttachment>(Key::RCH);
  ExprAttachment const * const eat = (ExprAttachment const *) model().constAttachment(Key::EXPR);
  Expr::Manager::View * view = model().newView();

  // If the transition relation hasn't been added yet, it is the first invocation of
  // this action.  Existing persistent signals were detected by something else,
  // typically tvsim.  We want to take another look at those signals because tvsim
  // does not check whether persistent signals contradict fair.
  bool veryFirstTime = !rat->persistentSatTrAdded();
  SAT::Manager::View * satView = rat->persistentSatView();
  if (veryFirstTime) { //SAT instance hasn't been created
    CNFAttachment const * const cnfat = (CNFAttachment const *) model().constAttachment(Key::CNF);
    vector< vector<ID> > tr = cnfat->getPlainCNF();
    model().constRelease(cnfat);
    satView->add(tr);
    rat->setPersistentSatTrAdded();
  }

  SAT::Manager * fairMan = model().newSATManager();
  SAT::Manager::View * fairView = fairMan->newView(*view);
  vector<ID> fairs;
  for (vector<ID>::const_iterator it = eat->outputFns().begin(); it !=
       eat->outputFns().end(); ++it) {
    if (*it != view->btrue())
      fairs.push_back(*it);
  }
  vector< vector<ID> > fairsCnf;
  Expr::tseitin(*view, fairs, fairsCnf, NULL, false);
  try {
    fairView->add(fairsCnf);
  }
  catch (SAT::Trivial const & tr) {
    assert(!tr.value());
  }

  //const std::unordered_map< ID, pair<bool, bool> > & persistentSignals = rat->persistentSignals();

  //TODO: Expand to all internal nodes
  vector<ID> signals(eat->stateVars());
  int cnt = 0;
  int conclusion = 2;

  bool changed = true;
  while (changed && conclusion == 2) {
    changed = false;
    for (vector<ID>::const_iterator it = signals.begin(); it != signals.end() && conclusion == 2; ++it) {
      /*
      std::unordered_map< ID, pair<bool, bool> >::const_iterator pit = persistentSignals.find(*it);
      if (pit == persistentSignals.end())
        pit = persistentSignals.find(view->apply(Expr::Not, *it));
      if (pit != persistentSignals.end())
        if (pit->second.first && pit->second.second)
          continue;
      */
      for (unsigned i = 0; i < 2 && conclusion == 2; ++i) {
        ID lit = i == 0 ? *it : view->apply(Expr::Not, *it);
        ID nlit = view->apply(Expr::Not, lit);
        if (rat->isPersistent(nlit))
          continue;
        bool eventuallyTrue = false;
        if (rat->isPersistent(lit)) {
          if (!veryFirstTime)
            continue;
          eventuallyTrue = rat->isEventuallyTrue(lit);
          if (!eventuallyTrue)
            continue;
        }
        if (view->op(lit) == Expr::Var || view->op(nlit) == Expr::Var) {
          vector<ID> assumps;
          assumps.push_back(lit);
          assumps.push_back(primeFormula(*view, nlit));
          if (eventuallyTrue || !satView->sat(&assumps)) {
            //Check whether lit -> !f for any fairness constraint f
            bool contradictsFair = false;
            for (vector<ID>::const_iterator fairLit = fairs.begin(); fairLit != fairs.end(); ++fairLit) {
              vector<ID> assumps2;
              assumps2.push_back(lit);
              assumps2.push_back(*fairLit);
              if (!fairView->sat(&assumps2)) {
                contradictsFair = true;
                break;
              }
            }
            bool unfair = rat->addPersistentSignal(lit, eventuallyTrue, contradictsFair);
            if (unfair)
              conclusion = 0;
            changed = true;
            ++cnt;
            if (model().verbosity() > Options::Informative) {
              ostringstream oss;
              oss << Expr::stringOf(*view, lit);
              if (eventuallyTrue)
                oss << " eventually true";
              if (contradictsFair)
                oss << " contradicts fair";
              oss << endl;
              cout << oss.str();
            }
            break;
          }
        }
        else {
          assert(false);
        }
      }
    }
    veryFirstTime = false;
  }

  if (model().verbosity() > Options::Terse) {
    cout << "PersistentSignalsAction: extracted " << cnt << " persistent signals" << endl;
    cout << "PersistentSignalsAction: spent " << (Util::get_user_cpu_time() - startTime) / 1000000.0
         << " s" << endl;
  }

  rat->setPersistentSignalsUpToDate();

  delete fairView;
  delete fairMan;
  delete view;
  model().constRelease(eat);
  model().release(rat);

  if (conclusion != 2) {
    assert(conclusion == 0);
    auto pat = model().attachment<ProofAttachment>(Key::PROOF);
    pat->setConclusion(conclusion);
    model().release(pat);
  }
}
