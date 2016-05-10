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
#include "StuckAt.h"
#include "ThreeValuedSimulation.h"

#include <set>

using namespace std;
using namespace ThreeValued;

void StuckAtAction::exec() {
  if (model().verbosity() > Options::Terse)
    cout << "StuckAtAction starting" << endl;

  ExprAttachment * const eat = (ExprAttachment *) model().constAttachment(Key::EXPR);
  vector<ID> latches(eat->stateVars());
  vector<ID> fns(eat->nextStateFnOf(latches));
  vector<TV> tvs;
  tvs.resize(latches.size(), TVFalse);

  Expr::Manager::View * v = model().newView();

  // assumes AIGER 1.9
  vector<ID> init(eat->initialConditions());
  set<ID> tl, fl;
  for (size_t i = 0; i < init.size(); ++i)
    if (v->op(init[i]) == Expr::Not)
      fl.insert(v->apply(Expr::Not, init[i]));
    else
      tl.insert(init[i]);
  for (size_t i = 0; i < tvs.size(); ++i)
    if (tl.find(latches[i]) != tl.end())
      tvs[i] = TVTrue;
    else if (fl.find(latches[i]) == fl.end())
      tvs[i] = TVX;

  bool changed = true;
  while (changed) {
    Map map;
    for (unsigned int i = 0; i < latches.size(); ++i)
      map.insert(Map::value_type(latches[i], tvs[i]));
    Folder f(*v, map);
    v->fold(f, fns);
    changed = false;
    for (unsigned int i = 0; i < fns.size(); ++i) {
      Map::const_iterator it = map.find(fns[i]);
      assert (it != map.end());
      if (it->second != tvs[i]) {
        changed = changed || tvs[i] != TVX;
        tvs[i] = TVX;
      }
    }
  }
  model().constRelease(eat);

  Expr::IDMap sub;
  bool reduce = false;
  for (unsigned int i = 0; i < latches.size(); ++i)
    if (tvs[i] != TVX) {
      reduce = true;
      sub.insert(Expr::IDMap::value_type(latches[i], 
                                         tvs[i] == TVFalse ? v->bfalse() : v->btrue()));
    }
  if (reduce) {
    SeqAttachment * seqat = (SeqAttachment *) model().attachment(Key::SEQ);
    ExprAttachment * eat = (ExprAttachment *) model().attachment(Key::EXPR);

    int cnt = 0;
    for (unsigned int i = 0; i < latches.size(); ++i)
      if (tvs[i] != TVX) {
        ++cnt;
        eat->setNextStateFn(latches[i], tvs[i] == TVTrue ? v->btrue() : v->bfalse());
        seqat->optimized.insert(unordered_map<ID, ID>::value_type(latches[i],
            tvs[i] == TVTrue ? v->btrue() : v->bfalse()));
      }
      else
        eat->setNextStateFn(latches[i], Expr::varSub(*v, sub, fns[i]));
    v->keep(eat->nextStateFnOf(eat->stateVars()));

    if (model().verbosity() > Options::Silent)
      cout << "StuckAt: Found " << cnt << " stuck-at latches" << endl;

    vector<ID> constraints(eat->constraints());
    eat->clearConstraints();
    for (vector<ID>::iterator it = constraints.begin(); it != constraints.end(); ++it)
      if (Expr::varSub(*v, sub, *it) == *it)
        eat->addConstraint(*it);
    v->keep(eat->constraints());

    vector<ID> outputs(eat->outputs());
    vector<ID> outputFns(eat->outputFnOf(outputs));
    eat->clearOutputFns();
    Expr::varSub(*v, sub, outputFns);
    eat->setOutputFns(outputs, outputFns);
    v->keep(outputFns);

    vector<ID> bad(eat->bad());
    vector<ID> badFns(eat->badFnOf(bad));
    eat->clearBadFns();
    Expr::varSub(*v, sub, badFns);
    eat->setBadFns(bad, badFns);
    v->keep(badFns);

    vector<ID> fairness(eat->fairness());
    vector<ID> fairnessFns(eat->fairnessFnOf(fairness));
    eat->clearFairnessFns();
    Expr::varSub(*v, sub, fairnessFns);
    eat->setFairnessFns(fairness, fairnessFns);
    v->keep(fairnessFns);

    vector<ID> justice(eat->justice());
    vector< vector<ID> > justiceS(eat->justiceSets());
    eat->clearJusticeSets();
    for (size_t i = 0; i < justiceS.size(); ++i) {
      Expr::varSub(*v, sub, justiceS[i]);
      eat->setJusticeSet(justice[i], justiceS[i]);
      v->keep(justiceS[i]);
    }

    model().release(eat);
    model().release(seqat);
  }
  else if (model().verbosity() > Options::Silent)
    cout << "StuckAt: Found 0 stuck-at latches" << endl;

  delete v;
}
