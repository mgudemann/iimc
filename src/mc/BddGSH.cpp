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
#include "BddGSH.h"
#include "options.h"
#include "Expr.h"

using namespace std;

namespace {
  /**
   * Convergence test of the GSH algorithm simplified
   * for same-direction operators only.
   */
  class Convergence {
  public:
    Convergence(unordered_set<int> & gamma, unordered_set<int>::size_type N,
                BDD const & init, bool forward, bool simple, bool slice) :
      gamma(gamma), N(N), init(init), forward(forward),
      simple(simple), slice(slice) {}
    bool operator()(BDD & hull, BDD & zeta, unordered_set<int>::size_type tau)
    {
      if ((forward || slice) ? hull.IsZero() : init <= !hull)
        // early termination
        return true;
      if (hull != zeta) {
        gamma.clear();
        if (tau != N-1 && simple)
          gamma.insert(tau);
        return false;
      } else {
        gamma.insert(tau);
        return gamma.size() == N;
      }
    }
  private:
    unordered_set<int> & gamma;
    unordered_set<int>::size_type N;
    BDD const & init;
    bool forward;
    bool simple;
    bool slice;
  };


  /**
   * Choice of operator to apply next to shrink the hull.
   */
  unordered_set<int>::size_type pick(
    unordered_set<int>::size_type N,
    unordered_set<int> & gamma) {
    static unordered_set<int>::size_type i = N-1;
    // Round robin schedule.
    unordered_set<int>::size_type j = i;
    for (i = (i+1) % N; i != j; i = (i+1) % N) {
      if (gamma.find(i) == gamma.end())
        return i;
    }
    assert(false);
    return N+1;
  }

  class Until {
  public:
    typedef BDD (BddTrAttachment::* PreImgFn)(BDD const &, bool) const;
    Until(BddTrAttachment const * tat, PreImgFn f,
          BDD const & inputCube, bool simple) :
      tat(tat), f(f), inputCube(inputCube), simple(simple) {}
    /**
     * Find the states that satisfy hull U (fairness & hull).
     */
    BDD operator()(BDD hull, BDD fairness) {
      BDD Z;
      if (simple) {
        Z = hull & fairness;
      } else {
        Z = (tat->*f)(hull, true);
        Z = Z.AndAbstract(fairness & hull, inputCube);
      }
      BDD frontier = Z;
      while (!frontier.IsZero()) {
        BDD preimgx = (tat->*f)(frontier, false);
        frontier = preimgx & ~Z & hull;
        Z |= frontier;
      }
      return Z;
    }
  private:
    BddTrAttachment const * tat;
    PreImgFn f;
    BDD const & inputCube;
    bool simple;
  };


  class Since {
  public:
    Since(BddTrAttachment const * tat) : tat(tat) {}
    /**
     * Find the states that satisfy hull S (fairness & hull).
     */
    BDD operator()(BDD hull, BDD fairness)
    {
      BDD Z = hull & fairness;
      BDD frontier = Z;
      while (!frontier.IsZero()) {
        BDD imgx = tat->img(frontier);
        frontier = imgx & ~Z & hull;
        Z |= frontier;
      }
      return Z;
    }
  private:
    BddTrAttachment const * tat;
  };


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

  class ToBeSat {
  public:
    ToBeSat(RchAttachment const * rat,
            vector<BDD> const & fbdd,
            vector<ID> const & fid)
    {
      assert(fbdd.size() == fid.size());
      for (size_t i = 0; i != fbdd.size(); ++i) {
        if (!rat->isSatisfiedFairnessConstraint(fid.at(i)))
          toBe.insert(fbdd.at(i));
      }
    }
    bool operator()(BDD const & fc) {
      return toBe.find(fc) != toBe.end();
    }
  private:
    set<BDD> toBe;
  };

  /** We could sort by number of minterms, but given the chance of
   * overflow and the small size of the vectors, we just go quadratic.
   */
  class Subsumed {
  public:
    Subsumed(vector<BDD> const & f)
    {
      typedef vector<BDD>::size_type size_type;
      size_type s = f.size();
      for (size_type i = 0; i != s; ++i) {
        BDD const & b = f.at(i);
        for (size_type j = 0; j != s; ++j) {
          if ((i != j && f.at(j) < b) || (i < j && f.at(j) == b)) {
            sub.insert(b);
            break;
          }
        }
      }
    }
    bool operator()(BDD const & fc) {
      return sub.find(fc) == sub.end();
    }
  private:
    set<BDD> sub;
  };
  
}


void BddGSHAction::exec(void) {
  Model & m = model();

  Options::Verbosity verbosity = m.verbosity();
  // Map iimc verbosity to CUDD verbosity.
  int bddVerbosity = 0;
  if (verbosity == Options::Logorrheic) bddVerbosity = 2;
  else if (verbosity > Options::Terse) bddVerbosity = 1;

  // Setup.
  auto tat = m.attachment<BddTrAttachment>(Key::BDD_TR);
  if (tat->hasBdds() == false) {
    if (verbosity > Options::Silent) {
      ostringstream oss;
      oss << "GSH: no transition relation found: quitting" << endl;
      cout << oss.str();
    }
    m.release(tat);
    return;
  }

  tat->resetBddManager("gsh_timeout");
  size_t xvSize = tat->currentStateVars().size();
  BDD inputCube = bddManager().bddOne();
  vector<BDD> inputVars = tat->inputVars();
  for (vector<BDD>::const_iterator bit = inputVars.begin();
       bit != inputVars.end(); ++bit) {
    inputCube &= *bit;
  }

  bool forward = m.options().count("gsh_fw");

  RchAttachment const * const rat = (RchAttachment const *) m.constAttachment(Key::RCH);
  bool hasReachable = rat->isBddForwardComplete();

  if (forward && !hasReachable && verbosity > Options::Silent) {
    ostringstream oss;
    oss << "GSH: forward analysis without reachable states is incomplete"
        << endl;
    cout << oss.str();
  }

  // Grab initial condition and fairness conditions.
  // (FixRoots replaces outputs with fairness constraints.)
  BDD init(tat->initialCondition());
  vector<BDD> fairness(tat->invariants());
  ExprAttachment const * const eat =
    (ExprAttachment const *) m.constAttachment(Key::EXPR);
  vector<ID> fairID(eat->outputFns());
  m.constRelease(eat);

  // Prune fairness constraints.
  ToBeSat toBeSat(rat, fairness, fairID);
  vector<BDD>::iterator fit = stable_partition(fairness.begin(), fairness.end(), toBeSat);
  fairness.erase(fit, fairness.end());

  Subsumed subSum(fairness);
  fit = stable_partition(fairness.begin(), fairness.end(), subSum);
  fairness.erase(fit, fairness.end());

  // Grab reachability info if present. (Use bdd_trav and bdd_save_fw_reach.)
  BDD hull = hasReachable ?
    rat->forwardBddLowerBound() : bddManager().bddOne();
  m.constRelease(rat);

  bool svOnly = dependOnStateVarsOnly(bddManager(), fairness,
                                      tat->currentStateVars());
  if (forward && !svOnly) {
    if (verbosity > Options::Silent) {
      ostringstream oss;
      oss << "GSH: Fairness constraints that depend on primary inputs\n"
          << "     are currently incompatible with gsh_fw: quitting"
          << endl;
      cout << oss.str();
    }
    m.release(tat);
    return;
  }

  bool slice = !forward && m.options().count("gsh_slice");
  if (slice && !hasReachable && verbosity > Options::Silent) {
    ostringstream oss;
    oss << "GSH: gsh_slice without reachable states is incomplete" << endl;
    cout << oss.str();
  }

  if (slice && tat->buildGSHTR() == false) {
    if (verbosity > Options::Silent) {
      ostringstream oss;
      oss << "GSH: construction of sliced transition relation failed: quitting"
          << endl;
      cout << oss.str();
    }
    m.release(tat);
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
    Until::PreImgFn preImgPtr =
      slice ? &BddTrAttachment::preimgGSH : &BddTrAttachment::preimg;
    Until until(tat.operator->(), preImgPtr, inputCube, svOnly);
    Since since(tat.operator->());

    BDD zeta = bddManager().bddZero();
    unordered_set<int> gamma;
    // Number of operators.  EX/EY is N-1.
    unordered_set<int>::size_type N = fairness.size() + 1;
    unordered_set<int>::size_type tau = N-1;
    Convergence converged(gamma, N, init, forward, svOnly, slice);

    while (!converged(hull, zeta, tau)) {
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
          hull = since(hull, fairness[tau]);
        else
          hull = until(hull, fairness[tau]);
      } else {
        if (forward)
          hull &= tat->img(hull);
        else
          hull &= ((*tat).*preImgPtr)(hull, false);
      }
    }
    if (bddVerbosity > 0) {
      cout << "Hull: ";
      hull.print(xvSize,bddVerbosity);
    }
    // Since forward and slice are incomplete if !hasReachable, we check
    // separately for emptiness and nonemptiness.
    // If hasReachable, the hull is all reachable, and languange emptiness
    // means hull emptiness.
    bool empty = (forward || slice) ? hull.IsZero() : init <= !hull;
    bool nonEmpty =
      (forward || slice) ? (hasReachable && !hull.IsZero()) : !(init <= !hull);
    if (empty || nonEmpty) { // we have a conclusion
      auto pat = m.attachment<ProofAttachment>(Key::PROOF);
      assert(pat != 0);
      pat->setConclusion(empty ? 0 : 1);
      m.release(pat);
      if (verbosity > Options::Silent) {
        ostringstream oss;
        oss << "Conclusion found by GSH." << endl;
        cout << oss.str();
      }
      if (verbosity > Options::Silent) {
        ostringstream oss;
        oss << "GSH: " << (empty ? "Empty" : "Non-empty")
            << " language" << endl;
        cout << oss.str();
      }
    } else if (verbosity > Options::Silent) {
      ostringstream oss;
      oss << "GSH: Inconclusive run" << endl;
      cout << oss.str();
    }
  } catch (Timeout const & e) {
    if (verbosity > Options::Silent) {
      ostringstream oss;
      oss << e.what() << endl;
      cout << oss.str();
    }
    bddManager().ClearErrorCode();
    bddManager().UnsetTimeLimit();
    bddManager().ResetStartTime();
  }
  m.release(tat);
  if (m.options().count("bdd_info")) {
    bddManager().info();
    ostringstream oss;
    oss << "CPU time since BDD manager reset = " 
        << ((double) bddManager().ReadElapsedTime()/1000.0)
        << " s" << endl;
    cout << oss.str();
  }
  bddManager().UpdateTimeLimit();

} // BddGSHAction::exec
