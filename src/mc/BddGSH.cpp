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
#include "BddGSH.h"
#include "options.h"
#include "Expr.h"

//typedef boost::program_options::variables_map options_map;

using namespace std;

namespace {
  /**
   * Convergence test of the GSH algorithm simplified
   * for backward operators only.
   */
  bool converged(
    BDD hull,
    BDD zeta,
    BDD init,
    unordered_set<int>::size_type tau,
    unordered_set<int>::size_type N,
    unordered_set<int> & gamma) {
    if (init <= !hull) // early termination
      return true;
    if (hull != zeta) {
      gamma.clear();
      if (tau != N-1)
        gamma.insert(tau);
      return false;
    } else {
      gamma.insert(tau);
      return gamma.size() == N;
    }
  }

  /**
   * Choice of operator to apply next to shrink the hull.
   */
  unordered_set<int>::size_type pick(
    unordered_set<int>::size_type N,
    unordered_set<int> & gamma) {
    // Simplistic schedule.
    for (unordered_set<int>::size_type i = 0; i < N; ++i) {
      if (gamma.find(i) == gamma.end())
        return i;
    }
    assert(false);
    return N+1;
  }

  /**
   * Find the states that satisfy invariant U target.
   */
  BDD until(
    BddTrAttachment const * tat,
    BDD invariant,
    BDD target)
  {
    BDD Z = target;
    BDD frontier = target;
    while (!frontier.IsZero()) {
      BDD preimgx = tat->preimg(frontier);
      frontier = preimgx & ~Z & invariant;
      Z |= frontier;
    }
    return Z;
  }

  /**
   * Find the states that satisfy invariant S source.
   */
  BDD since(
    BddTrAttachment const * tat,
    BDD invariant,
    BDD source)
  {
    BDD Z = source;
    BDD frontier = source;
    while (!frontier.IsZero()) {
      BDD imgx = tat->img(frontier);
      frontier = imgx & ~Z & invariant;
      Z |= frontier;
    }
    return Z;
  }

  bool dependOnStateVarsOnly(
    Cudd const & mgr,
    vector<BDD> const & f,
    vector<BDD> const & stateVars)
  {
    vector<unsigned int> fIndices = mgr.SupportIndices(f);
    vector<unsigned int> sIndices = mgr.SupportIndices(stateVars);
    unordered_set<unsigned int> iset(sIndices.begin(), sIndices.end());
    for (vector<unsigned int>::const_iterator it = fIndices.begin();
         it != fIndices.end(); ++it) {
      if (iset.find(*it) == iset.end())
        return false;
    }
    return true;
  }
  
}


void BddGSHAction::exec(void) {
  Model & m = model();

  Options::Verbosity verbosity = m.verbosity();
  // Map iimc verbosity to CUDD verbosity.b
  int bddVerbosity = 0;
  if (verbosity == Options::Logorrheic) bddVerbosity = 2;
  else if (verbosity > Options::Terse) bddVerbosity = 1;

  // Setup.
  BddTrAttachment const * tat = 
    (BddTrAttachment const *) m.constAttachment(Key::BDD_TR);
  if (tat->hasBdds() == false) {
    m.constRelease(tat);
    return;
  }

  // Grab initial condition and fairness conditions.
  // (FixRoots replaces outputs with fairness constraints.)
  BDD init(tat->initialCondition());
  vector<BDD> fairness(tat->invariants());
  if (!dependOnStateVarsOnly(bddManager(), fairness, tat->currentStateVars())) {
    ostringstream oss;
    oss << "GSH: Fairness constraints depend on primary inputs: quitting"
        << endl;
    cout << oss.str();
    return;
  }

  tat->resetBddManager("gsh_timeout");
  size_t xvSize = tat->currentStateVars().size();

  bool forward = m.options().count("gsh_fw");

  // Grab reachability info if present. (Use bdd_trav and bdd_save_fw_reach.)
  RchAttachment const *rat = 
    (RchAttachment const *) m.constAttachment(Key::RCH);
  bool hasReachable = rat->isBddForwardComplete();
  BDD hull;
  if (hasReachable)
    hull = rat->forwardBddLowerBound();
  else
    hull = bddManager().bddOne();
  m.constRelease(rat);

  if (forward && !hasReachable){
    ostringstream oss;
    oss << "GSH: forward analysis currently requires reachable states: quitting"
        << endl;
    cout << oss.str();
    return;
  }

  int step = 0;
  try {
    if (verbosity != Options::Silent) {
      ostringstream oss;
      oss << "GSH" << (forward ? " (forward)" : " (backward)") << endl;
      cout << oss.str();
    }
    if (verbosity > Options::Terse) {
      ostringstream oss;
      oss << fairness.size() << " fairness constraints" << endl;
      cout << oss.str();
    }
    BDD zeta = bddManager().bddZero();
    unordered_set<int> gamma;
    // Number of operators.  EX/EY is N-1.
    unordered_set<int>::size_type N = fairness.size() + 1;
    unordered_set<int>::size_type tau = N-1;
    while (!converged(hull, zeta, init, tau, N, gamma)) {
      if (bddVerbosity > 0) {
        ostringstream oss;
        oss << "iteration " << step;
        if (verbosity > Options::Informative)
          oss << " (" << gamma.size() << " disabled operators) ";
        cout << oss.str();
        hull.print(xvSize,bddVerbosity);
      }
      ++step;
      zeta = hull;
      tau = pick(N, gamma);
      if (verbosity > Options::Informative) {
        ostringstream oss;
        oss << "picked " << tau << endl;
        cout << oss.str();
      }
      if (tau != N-1) {
        if (forward)
          hull = since(tat, hull, fairness[tau] & hull);
        else
          hull = until(tat, hull, fairness[tau] & hull);
      } else {
        if (forward)
          hull &= tat->img(hull);
        else
          hull &= tat->preimg(hull);
      }
    }
    if (bddVerbosity > 0) {
      cout << "Hull: ";
      hull.print(xvSize,bddVerbosity);
    }
    // To be fixed for forward && !hasReachable
    bool empty = init <= !hull;
    ProofAttachment * pat = (ProofAttachment *) m.attachment(Key::PROOF);
    assert(pat != 0);
    pat->setConclusion(empty ? 0 : 1);
    m.release(pat);
    if (verbosity > Options::Silent) {
      ostringstream oss;
      oss << (empty ? "Empty" : "Non-empty") << " language" << endl;
      cout << oss.str();
    }
  } catch (Timeout& e) {
    if (verbosity > Options::Silent)
      cout << e.what() << endl;

    bddManager().ClearErrorCode();
    bddManager().UnsetTimeLimit();
    bddManager().ResetStartTime();
  }
  if (m.options().count("bdd_info")) {
    bddManager().info();
    ostringstream oss;
    oss << "CPU time since BDD manager reset = " 
        << ((double) bddManager().ReadElapsedTime()/1000.0)
        << " s" << endl;
    cout << oss.str();
  }
  bddManager().UpdateTimeLimit();
  m.constRelease(tat);

} // BddGSHAction::exec
