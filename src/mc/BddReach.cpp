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

#include "Error.h"
#include "BddReach.h"
#include "options.h"
#include "Expr.h"

using namespace std;

void BddFwReachAction::exec() {
  Model & m = model();
  doFwReachability(m);

} // BddFwReachAction::exec


void BddBwReachAction::exec() {
  Model & m = model();
  doBwReachability(m);

} // BddReachAction::exec


/**
 * Do BDD-based forward reachability analysis of the model.
 */
void BddFwReachAction::doFwReachability(Model& model) {
  // Setup.
  BddTrAttachment const * tat = 
    (BddTrAttachment const *) model.constAttachment(Key::BDD_TR);
  if (tat->hasBdds() == false) {
    model.constRelease(tat);
    return;
  }
  tat->resetBddManager("bdd_fw_timeout");

  Options::Verbosity verbosity = model.verbosity();
  // Map iimc verbosity to CUDD verbosity.
  int bddVerbosity = 0;
  if (verbosity == Options::Logorrheic) bddVerbosity = 2;
  else if (verbosity > Options::Terse) bddVerbosity = 1;
  size_t xvSize = tat->currentStateVars().size();

  // Set up initial condition.
  BDD init(tat->initialCondition());
  RchAttachment const *rat = 
    (RchAttachment const *) model.constAttachment(Key::RCH);
  BDD fwLb = rat->forwardBddLowerBound();
  if (fwLb)
    init |= fwLb;

  vector<BDD> invariants(tat->invariants());
  BDD bwLb = rat->backwardBddLowerBound();
  if (bwLb) {
    for (vector<BDD>::iterator it = invariants.begin();
         it != invariants.end(); ++it) {
      *it |= bwLb;
    }
  }
  model.constRelease(rat);

  bool keepGoing = model.options().count("bdd_trav");
  if (!keepGoing && invariants[0].IsZero()) {  // AIGER-specific
    // Trivial case of passing property.
    if (verbosity > Options::Terse)
      cout << "Empty set of bad states" << endl;
    ProofAttachment * pat = (ProofAttachment *) model.attachment(Key::PROOF);
    assert(pat != 0);
    pat->setConclusion(0);
    model.release(pat);
    return;
  }

  bool minFrontier = model.options().count("bdd_mf");
  BDD reached = init;
  bool counterex = false;
  // Variable step gives the reachability step currently underway.
  // A step is completed when the states in the frontier have been
  // checked for violation of the invariants.  So, if step is n at
  // some point, then there is no bad state at distance less than
  // n from the initial states.
  int step = 0;
  int nfrontiers = 0;
  try {
    // Do forward reachability analysis.
    if (verbosity != Options::Silent)
      cout << "Forward Reachability analysis" << endl;
    BDD frontier = init;
    while (!frontier.IsZero()) {
      if (bddVerbosity > 0) cout << "frontier " << step;
      frontier.print(xvSize,bddVerbosity);
      // Check invariants.
      if (!counterex) {
        for (vector<BDD>::const_iterator it = invariants.begin();
             it != invariants.end(); ++it) {
          // AIGER outputs signal failure when asserted.
          if (! (frontier <= !(*it))) {
            counterex = true;
            if (verbosity > Options::Terse) {
              cout << "Failure for output";
              it->print(xvSize,bddVerbosity);
            }
          }
        }
      }
      step++;
      if (counterex && !keepGoing) break;
      BDD imgx = tat->img(frontier);
      frontier = imgx & ~reached;
      reached |= frontier;
      nfrontiers++;
      if (minFrontier)
        frontier = frontier.Squeeze(reached);
    }
    if (bddVerbosity > 0 && (!counterex || keepGoing)) {
      cout << "Reachable states";
      reached.print(xvSize,bddVerbosity);
      if (keepGoing && !reached.IsOne()) {
        BDD unreached = !reached;
        BDD uprime = unreached.LargestCube().MakePrime(unreached);
        RchAttachment const *rat = 
          (RchAttachment const *) model.constAttachment(Key::RCH);
        vector<ID> cube;
        rat->bddToLiteralVector(uprime,cube);
        model.constRelease(rat);
        Expr::Manager::View *v = model.newView();
        cout << "Unreachable cube:";
        for (vector<ID>::const_iterator it = cube.begin();
             it != cube.end(); ++it) {
          cout << Expr::stringOf(*v, *it, 1);
        }
        cout << endl;
        delete v;
        uprime.print(xvSize,bddVerbosity);
      }
    }
    if (model.options().count("bdd_save_fw_reach")) {
      RchAttachment *rat = (RchAttachment *) model.attachment(Key::RCH);
      assert(rat != 0);
      rat->setForwardBddLowerBound(reached);
      model.release(rat);
    } else {
      ProofAttachment * pat = (ProofAttachment *) model.attachment(Key::PROOF);
      assert(pat != 0);
      pat->setConclusion(counterex ? 1 : 0);
      model.release(pat);
    }
  } catch (Timeout& e) {
    if (verbosity > Options::Silent)
      cout << e.what() << endl;

    // AIGER-specific!  Relies on single-cube initial state.

    /* Reset BDD manager.  For the time being, we let this operation
     * run to completion.  It seems to be fast anyway and does not
     * require reordering (which at this point is disabled). */
    bddManager().ClearErrorCode();
    bddManager().UnsetTimeLimit();
    bddManager().ResetStartTime();
    if (nfrontiers > 0) {
      RchAttachment *rat = (RchAttachment *) model.attachment(Key::RCH);
      assert(rat != 0);
      // If the initial states form a cube, find a prime of reached that
      // contains the initial state.
      bool initIsCube = init.IsCube();
      if (initIsCube) {
        BDD enlargedSource = init.MakePrime(reached);
        if (verbosity > Options::Terse) {
          cout << "Prime expansion of init";
          enlargedSource.print(xvSize,bddVerbosity);
          // Find a large prime of the reachable states.
          BDD largePrime = reached.LargestCube().MakePrime(reached);
          cout << "A large prime of reached";
          largePrime.print(xvSize,bddVerbosity);
          // Find all prime expansions of init (relative to reached).
          BDD allPrimes = init.MaximallyExpand(bddManager().bddOne(),reached);
          cout << "All prime expansions of init";
          allPrimes.print(xvSize,bddVerbosity);
        }
        // Save result as expression in the RchAttachment.
        BddAttachment const *bat = 
          (BddAttachment const *) model.constAttachment(Key::BDD);
        assert(bat != 0);
        Expr::Manager::View *v = model.newView();
        ID cubeExpr = bat->exprOf(enlargedSource, *v);
        rat->updateForwardLowerBound(cubeExpr);
        delete v;
        model.constRelease(bat);
      } else {
        if (verbosity > Options::Terse)
          cout << "Init is not a cube.  No enlargement attempted." << endl;
      }
      rat->setForwardStepsBdd(step);
      rat->updateCexLowerBound(step);
      if (verbosity > Options::Terse) {
        cout << "No counterexample shorter than " 
             << rat->cexLowerBound() << endl;
      }
      // Save also the raw BDD for a subset of the reachable states found
      // that includes the initial state(s).
      //BDD dsub = reached.BiasedUnderApprox(init,xvSize,0,1.0,0.9) |
      //BDD dsub = reached.SubsetCompress(xvSize,10000) | init;
      //BDD dsub = reached.RemapUnderApprox(xvSize,0,0.95) | init;
      BDD dsub = reached.SubsetHeavyBranch(xvSize,1000) | init;
      //BDD dsub = reached.SubsetShortPaths(xvSize,1000) | init;
      //(initIsCube ? init.MaximallyExpand(bddManager().bddOne(),reached) : init);
      if (verbosity > Options::Terse) {
        cout << "states reached so far"; reached.print(xvSize,bddVerbosity);
        cout << "dense subset"; dsub.print(xvSize,bddVerbosity);
      }
      if (dsub != init) {
        rat->setForwardBddLowerBound(dsub);
      }
      rat->setBackwardBddLowerBound(invariants[0]); // AIGER-specific
      model.release(rat);
    }
  }
  if (model.options().count("bdd_info")) {
    bddManager().info();
    cout << "CPU time since BDD manager reset = " 
         << ((double) bddManager().ReadElapsedTime()/1000.0)
         << " s" << endl;
  }
  bddManager().UpdateTimeLimit();
  model.constRelease(tat);

} // BddFwReachAction::doFwReachability


/**
 * Do BDD-based backward reachability analysis of the model.
 */
void BddBwReachAction::doBwReachability(Model& model) {
  // Setup.
  BddTrAttachment const * tat = 
    (BddTrAttachment const *) model.constAttachment(Key::BDD_TR);
  if (tat->hasBdds() == false) {
    model.constRelease(tat);
    return;
  }
  tat->resetBddManager("bdd_bw_timeout");

  Options::Verbosity verbosity = model.verbosity();
  // Map iimc verbosity to CUDD verbosity.
  int bddVerbosity = 0;
  if (verbosity == Options::Logorrheic) bddVerbosity = 2;
  else if (verbosity > Options::Terse) bddVerbosity = 1;
  size_t xvSize = tat->currentStateVars().size();

  // Set up initial condition.
  BDD init(tat->initialCondition());
  RchAttachment const *rat = 
    (RchAttachment const *) model.constAttachment(Key::RCH);
  BDD fwLb = rat->forwardBddLowerBound();
  if (fwLb)
    init |= fwLb;

  vector<BDD> invariants(tat->invariants());
  if (invariants.size() != 1) {
    cerr << "Warning: Backward analysis only works for 1 invariant" << endl;
    cerr << "Only the first of the " << invariants.size()
         << " will be used" << endl;
  }
  // AIGER outputs signal failure when asserted.
  BDD target = invariants[0];
  BDD bwLb = rat->backwardBddLowerBound();
  if (bwLb)
    target |= bwLb;
  model.constRelease(rat);

  bool keepGoing = model.options().count("bdd_trav");
  if (!keepGoing && target.IsOne()) {  // AIGER-specific
    // Trivial case of failing property.
    if (verbosity > Options::Terse)
      cout << "All states are bad" << endl;
    ProofAttachment * pat = (ProofAttachment *) model.attachment(Key::PROOF);
    assert(pat != 0);
    pat->setConclusion(1);
    model.release(pat);
    return;
  }

  bool minFrontier = model.options().count("bdd_mf");
  BDD reached = target;
  bool counterex = false;
  // Variable step gives the reachability step currently underway.  A
  // step is completed when the states in the frontier have been
  // checked against the initial states.  So, if step is n at some
  // point, then there is no target state at distance less than n from
  // the initial states.
  int step = 0;
  int nfrontiers = 0;
  try {
    // Do backward reachability analysis.
    if (verbosity != Options::Silent)
      cout << "Backward Reachability analysis" << endl;
    BDD frontier = target;
    while (!frontier.IsZero()) {
      if (bddVerbosity > 0) cout << "frontier " << step;
      frontier.print(xvSize,bddVerbosity);
      // Check invariants.
      if (!counterex) {
        if (!(frontier <= !init)) {
          counterex = true;
          if (verbosity > Options::Terse) {
            cout << "Counterexample" << endl;
          }
        }
      }
      step++;
      if (counterex && !keepGoing) break;
      BDD preimgx = tat->preimg(frontier);
      frontier = preimgx & ~reached;
      reached |= frontier;
      nfrontiers++;
      if (minFrontier)
        frontier = frontier.Squeeze(reached);
    }
    if (bddVerbosity > 0 && (!counterex || keepGoing)) {
      cout << "Backward reachable states";
      reached.print(xvSize,bddVerbosity);
    }
    ProofAttachment * pat = (ProofAttachment *) model.attachment(Key::PROOF);
    assert(pat != 0);
    pat->setConclusion(counterex ? 1 : 0);
    model.release(pat);
  } catch (Timeout& e) {
    if (verbosity > Options::Silent)
      cout << e.what() << endl;

    // AIGER-specific!  Relies on single invariant.

    /* Reset BDD manager.  For the time being, we let this operation
     * run to completion.  It seems to be fast anyway and does not
     * require reordering (which at this point is disabled). */
    bddManager().ClearErrorCode();
    bddManager().UnsetTimeLimit();
    bddManager().ResetStartTime();
    if (nfrontiers > 0) {
      RchAttachment *rat = (RchAttachment *) model.attachment(Key::RCH);
      assert(rat != 0);
      // If target is a cube, find a prime of reached that contains
      // the target states.
      if (target.IsCube()) {
        BDD enlargedTarget = target.LargestCube().MakePrime(reached);
        // Find a large prime of the backward reachable states.
        BDD largePrime = reached.LargestCube().MakePrime(reached);
        if (verbosity > Options::Terse) {
          cout << "Prime expansion of target";
          enlargedTarget.print(xvSize,bddVerbosity);
          cout << "A large prime of (backward) reached";
          largePrime.print(xvSize,bddVerbosity);
        }
        // Save result as expression in the RchAttachment.
        BddAttachment const *bat =
          (BddAttachment const *) model.constAttachment(Key::BDD);
        assert(bat != 0);
        Expr::Manager::View *v = model.newView();
        ID cubeExpr = bat->exprOf(enlargedTarget, *v);
        rat->updateBackwardLowerBound(cubeExpr);
        delete v;
        model.constRelease(bat);
      } else {
        if (verbosity > Options::Terse)
          cout << "Target is not a cube.  No enlargement attempted." << endl;
      }
      rat->setBackwardStepsBdd(step);
      rat->updateCexLowerBound(step);
      if (verbosity > Options::Terse) {
        cout << "No counterexample shorter than " 
             << rat->cexLowerBound() << endl;
      }
      // Save also the raw BDD for a subset of the reachable states found
      // that includes the target state(s).
      BDD dsub = invariants[0] | reached.SubsetHeavyBranch(xvSize,1000);
      //BDD dsub = invariants[0] | reached.RemapUnderApprox(xvSize,0.9);
      if (verbosity > Options::Terse) {
        cout << "states reached so far"; reached.print(xvSize,bddVerbosity);
        cout << "dense subset"; dsub.print(xvSize,bddVerbosity);
      }
      rat->setForwardBddLowerBound(init);
      if (dsub != invariants[0]) {
        rat->setBackwardBddLowerBound(dsub);
      }
      model.release(rat);
    }
  }
  if (model.options().count("bdd_info")) {
    bddManager().info();
    cout << "CPU time since BDD manager reset = " 
         << ((double) bddManager().ReadElapsedTime()/1000.0)
         << " s" << endl;
  }
  if (model.options().count("bdd_info")) {
    bddManager().info();
    cout << "CPU time since BDD manager reset = " 
         << ((double) bddManager().ReadElapsedTime()/1000.0)
         << " s" << endl;
  }
  bddManager().UpdateTimeLimit();
  model.constRelease(tat);

} // BddBwReachAction::doBwReachability
