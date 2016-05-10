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

#include "Expr.h"
#include "ExprUtil.h"
#include "StuckAt.h"
#include "ThreeValuedSimulation.h"
#include "Util.h"

#include <set>

using namespace std;
using namespace ThreeValued;

void StuckAtAction::exec() {
  if (model().verbosity() > Options::Terse)
    cout << "StuckAtAction starting" << endl;

  ExprAttachment * const eat = (ExprAttachment *) model().constAttachment(Key::EXPR);
  AIGAttachment * const aat = (AIGAttachment *) model().constAttachment(Key::AIG);
  AIGTVSim tvsim(aat);
  Opt::RefIDMap & idOfAigRef = aat->ref2id;

  Expr::Manager::View * v = model().newView();

  // assumes AIGER 1.9
  vector<ID> init(eat->initialConditions());
  tvsim.reset(*v, init);

  bool changed = true;
  vector<TV> latchTVs(tvsim.latchBegin(), tvsim.latchEnd());
  int64_t start = Util::get_user_cpu_time();
  int64_t iter = 0;
  while (changed) {
    ++iter;
    tvsim.step();
    changed = false;
    const vector<TV> & nsValues = tvsim.getNSValues();
    for (unsigned i = 0; i < nsValues.size(); ++i) {
      if (nsValues[i] != latchTVs[i]) {
        changed = changed || (latchTVs[i] != TVX);
        latchTVs[i] = TVX;
      }
      else {
        latchTVs[i] = nsValues[i];
      }
    }
    copy(latchTVs.begin(), latchTVs.end(), tvsim.latchBegin());
  }
  model().constRelease(eat);
  if (model().verbosity() > Options::Terse)
    cout << "StuckAtAction: performed " << iter << " tvsim iterations in " << (Util::get_user_cpu_time() - start) / 1000000.0 << "s" << endl;

  Expr::IDMap sub;
  bool reduce = false;
  for (unsigned i = 0; i < latchTVs.size(); ++i)
    if (latchTVs[i] != TVX) {
      reduce = true;
      ID latchID = idOfAigRef[Opt::refOf(i + 1 + aat->aig.numInputs(), false)];
      sub.insert(Expr::IDMap::value_type(latchID, latchTVs[i] == TVFalse ? 
                                                  v->bfalse() : v->btrue()));
    }
  if (reduce) {
    SeqAttachment * seqat = (SeqAttachment *) model().attachment(Key::SEQ);
    ExprAttachment * eat = (ExprAttachment *) model().attachment(Key::EXPR);

    int cnt = 0;
    vector<ID> toSub;
    for (unsigned int i = 0; i < latchTVs.size(); ++i) {
      ID latchID = idOfAigRef[Opt::refOf(i + 1 + aat->aig.numInputs(), false)];
      if (latchTVs[i] != TVX) {
        ++cnt;
        eat->setNextStateFn(latchID, latchTVs[i] == TVTrue ? v->btrue() : v->bfalse());
        seqat->optimized.insert(unordered_map<ID, ID>::value_type(latchID,
            latchTVs[i] == TVTrue ? v->btrue() : v->bfalse()));
      }
      else {
        toSub.push_back(latchID);
      }
    }
    vector<ID> nnsfs = eat->nextStateFnOf(toSub);
    Expr::varSub(*v, sub, nnsfs);
    eat->setNextStateFns(toSub, nnsfs);
    v->keep(eat->nextStateFnOf(eat->stateVars()));

    if (model().verbosity() > Options::Silent)
      cout << "StuckAt: Found " << cnt << " stuck-at latches" << endl;

    vector<ID> constraints(eat->constraints());
    vector<ID> constraintFns(eat->constraintFns());
    eat->clearConstraints();
    for (vector<ID>::size_type i = 0; i != constraintFns.size(); ++i) {
      ID f = Expr::varSub(*v, sub, constraintFns[i]);
      eat->addConstraint(constraints[i], f);
    }
    v->keep(eat->constraintFns());

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
