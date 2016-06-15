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

#include "IC3.h"
#include "KLive.h"
#include "Persist.h"
#include "Util.h"

using namespace std;

KLive::KLive(Model & _model, Options::Verbosity v) : model(_model),
  safetyModel(model), verbosity(v), k(0), view(safetyModel.newView()) {

  auto rat = model.attachment<RchAttachment>(Key::RCH);
  rat->filterDroppedPersistentSignals();
  model.release(rat);

  view->begin_local();
  safetyModel.setView(view);
  constraints.resize(1);

  ExprAttachment const * eat = (ExprAttachment const *)
    safetyModel.constAttachment(Key::EXPR);

  //Extract non-trivial fairness constraints
  vector<ID> ntFair;
  for (vector<ID>::const_iterator it = eat->outputFns().begin(); it !=
       eat->outputFns().end(); ++it) {
    if (*it != view->btrue())
      ntFair.push_back(*it);
  }

  safetyModel.constRelease(eat);

  if (ntFair.empty()) {
    //Add back a trivial constraint
    ntFair.push_back(view->btrue());
  }

  if (ntFair.size() != 1) {
    if (verbosity > Options::Informative)
      cout << "KLive: Degeneralizing automaton" << endl;
    auto eatw = safetyModel.attachment<ExprAttachment>(Key::EXPR);
    //Degeneralize
    int num = ntFair.size();
    vector<ID> newStateVars;
    for (int i = 0; i < num; ++i) {
      ostringstream buf;
      buf << "__dgVar" << i << "__";
      newStateVars.push_back(view->newVar(buf.str()));
    }
    ID fair = view->apply(Expr::And, newStateVars);
    fair = AIGOfExpr(*view, fair);
    for (int i = 0; i < num; ++i) {
      ID nsf = view->apply(Expr::Or, ntFair[i], view->apply(Expr::And, view->apply(Expr::Not, fair), newStateVars[i]));
      nsf = AIGOfExpr(*view, nsf);
      eatw->setNextStateFn(newStateVars[i], nsf);
      eatw->addInitialCondition(view->apply(Expr::Not, newStateVars[i]));
    }
    eatw->clearOutputFns();
    ID dg = view->newVar("__dg__");
    eatw->setOutputFn(dg, fair);
    safetyTarget = fair;
    safetyModel.release(eatw);
  }
  else {
    safetyTarget = ntFair[0];
  }

  //Set the safety model's mode to mIC3 (safety)
  safetyModel.setDefaultMode(Model::mIC3);
}

KLive::~KLive() {
  view->end_local();
  delete view;
}

MC::ReturnValue KLive::check(int timeout, int bound, std::string klive_backend) {
  MC::ReturnValue rv;

  int64_t startTime = Util::get_thread_cpu_time();

  if (verbosity > Options::Silent)
    cout << "KLive: Checking from K = " << k << endl;

  if (bound < 0)
    bound = INT_MAX;

  vector<SAT::Clauses> GR(1, SAT::Clauses());
 
  for ( ; k <= bound; ++k) {
    PersistentSignalsAction(model).make();

    RchAttachment const * const rat = (RchAttachment const *) model.constAttachment(Key::RCH);
    const unordered_map< ID, pair<bool, bool> > & newPersistentSignals = rat->persistentSignals();
    if (newPersistentSignals != persistentSignals) {
      //Update target with the diff
      auto eat = safetyModel.attachment<ExprAttachment>(Key::EXPR);
      vector<ID> conj(1, safetyTarget);
      for (unordered_map< ID, pair<bool, bool> >::const_iterator it = newPersistentSignals.begin();
           it != newPersistentSignals.end(); ++it) {
        unordered_map< ID, pair<bool, bool> >::const_iterator psit = persistentSignals.find(it->first);
        if (psit == persistentSignals.end()) { //New signal
          if (it->second.first) {
            conj.push_back(it->first);
          }
          else if (it->second.second) {
            conj.push_back(view->apply(Expr::Not, it->first));
          }
          else {
            ID constraint = view->apply(Expr::Equiv, it->first, Expr::primeFormula(*view, it->first));
            constraint = Expr::AIGOfExpr(*view, constraint);
            //Express constraint in current-state variables only
            ID stateVar = view->op(it->first) == Expr::Var ? it->first : view->apply(Expr::Not, it->first);
            ID nsf = eat->nextStateFnOf(stateVar);
            Expr::IDMap sub;
            sub.insert(Expr::IDMap::value_type(view->prime(stateVar), nsf));
            conj.push_back(varSub(*view, sub, constraint));
          }
        }
        else if (it->second != psit->second) { //Signal information was updated
          assert(it->second.first || it->second.second);
          //TODO: Implement
          assert(false);
        }
      }
      safetyTarget = Expr::AIGOfExpr(*view, view->apply(Expr::And, conj));
      ID output = eat->outputs()[0];
      eat->setOutputFn(output, safetyTarget);
      persistentSignals = newPersistentSignals;
      safetyModel.release(eat);
    }
    model.constRelease(rat);

    if (verbosity > Options::Informative)
      cout << "KLive: K = " << k << endl;

    //Could possibly populate the safety model's tactics queue and then call
    //the dispatcher.  For now, just call IC3's reach directly to be able to
    //access inductive cubes, control incrementality, etc. Before doing that,
    //create a dummy IC3Action and build its dependencies so that all
    //attachments are ready.
    //To avoid this hack, IC3 should be made a class (or an attachment?) so
    //that information it derives can be retrieved even after it concludes.
    IC3::IC3Action ic3Action(safetyModel, false, false, klive_backend);
    ic3Action.makeDeps();
    
    IC3::IC3Options ic3Opts(safetyModel.options());
    ic3Opts.propagate = true;
    ic3Opts.constraints = &GR;
    ic3Opts.backend = klive_backend;
    //ic3Opts.constraints = &constraints;
    //Set IC3's timeout to remaining time
    if (timeout > 0) {
      int64_t sofar = Util::get_thread_cpu_time() - startTime;
      ic3Opts.timeout = timeout - sofar / 1000000;
    }

    IC3::CubeSet indCubes;
    MC::ReturnValue result = IC3::reach2(safetyModel, ic3Opts, 0, 0, 0, 0, &indCubes, view);
    if (result.returnType == MC::Proof) {
      rv.returnType = MC::Proof;
      break;
    }
    if (result.returnType == MC::Unknown) { //timed out
      rv.returnType = MC::Unknown;
      break;
    }

    if (verbosity > Options::Informative)
      cout << "KLive: " << indCubes.size() << " inductive clauses derived" << endl;
    vector< vector<ID> > newGR;
    for (IC3::CubeSet::const_iterator it = indCubes.begin(); it != indCubes.end();
         ++it) {
      SAT::Clause cls;
      Expr::complement(*view, *it, cls);
      GR[0].push_back(cls);
      newGR.push_back(cls);
    }

    /*
    if (!newGR.empty()) {
      auto rat = model.attachment<RchAttachment>(Key::RCH);
      bool added = rat->addReach(newGR);
      model.release(rat);
      if (!added) { //concluded
        if (verbosity > Options::Informative)
          cout << "KLive: Stable region unsatisfiable" << endl;
        rv.returnType = MC::Proof;
        break;
      }
    }
    */

    //Update safety target
    auto eat = safetyModel.attachment<ExprAttachment>(Key::EXPR);
    ostringstream buf;
    buf << "__kLiveLatch" << k << "__";
    ID newLatch = view->newVar(buf.str());
    //nsf = newLatch | old safety target
    ID nsf = view->apply(Expr::Not, 
                view->apply(Expr::And, view->apply(Expr::Not, newLatch), 
                                       view->apply(Expr::Not, safetyTarget)));
    eat->setNextStateFn(newLatch, nsf);
    eat->addInitialCondition(view->apply(Expr::Not, newLatch));
    safetyTarget = view->apply(Expr::And, newLatch, safetyTarget);
    //Update output function to the new safety target
    ID output = eat->outputs()[0];
    eat->setOutputFn(output, safetyTarget);
    safetyModel.release(eat);
  }

  return rv;
}

void KLiveAction::exec() {
  int timeout = model().options()["klive_timeout"].as<int>();

  int bound = model().options()["klive_bound"].as<int>();

  KLive klive(model(), model().verbosity());

  MC::ReturnValue rv = klive.check(timeout, bound, klive_backend);
  if (rv.returnType != MC::Unknown) {
    std::cout << "----\nKLive conclusion " << (rv.returnType == MC::Proof ? 0 : 1) << "\n----\n";
    if (model().verbosity() > Options::Silent)
      cout << "Conclusion found by KLive." << endl;
    auto pat = model().attachment<ProofAttachment>(Key::PROOF);
    if (rv.returnType == MC::Proof)
      pat->setConclusion(0);
    else
      pat->setConclusion(1);
  }
}
