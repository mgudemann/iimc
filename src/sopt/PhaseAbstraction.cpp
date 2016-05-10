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

#include "ExprUtil.h"
#include "Util.h"
#include "ThreeValuedSimulation.h"
#include "Simplifier.h"
#include "PhaseAbstraction.h"

using namespace std;
using namespace ThreeValued;

namespace {

/** Print the IDs held in a container. */
template<typename Container>
string idString(Expr::Manager::View & ev, Container const &ids, bool nl = true)
{
  ostringstream buf;
  vector<ID> const v(ids.cbegin(), ids.cend());
  shortStringOfID(ev, v, buf);
  if (nl) buf << endl;
  return buf.str();
}


/** Find periodic signals that are related (have the same frequency).
 *  Figure out whether they are mutually exclusive. */
void findPeriodicSets(
  Expr::Manager::View & v,
  vecSeq const & lasso,
  vector<ID> const & sv,
  PeriodicCardMap const & cmap,
  Options::Verbosity verbosity,
  PhaseGroupVec & phaseGroups)
{
  // Build map from ID to column index in the lasso
  // (which is the same as in the state variable vector).
  unordered_map<ID, TVvec::size_type> imap;
  for (vector<ID>::size_type i = 0; i < sv.size(); ++i) {
    PeriodicCardMap::const_iterator it = cmap.find(sv[i]);
    if (it != cmap.end())
      imap[sv[i]] = i;
  }

  // Build a vector of cards sorted in order of increasing period and,
  // for the same period, increasing start time.
  vector< pair<ID, PeriodicSignalCard> > cards(cmap.begin(), cmap.end());
  sort(cards.begin(), cards.end(), comparePeriodic);

  // Keep track of signals already grouped.
  set<ID> grouped;

  for (vector< pair<ID, PeriodicSignalCard> >::const_iterator it1 = cards.begin();
       it1 != cards.end(); ++it1) {
    ID var1 = it1->first;
    if (grouped.find(var1) != grouped.end()) continue;
    grouped.insert(var1);
    // This signal starts a new group.
    PeriodicSignalCard const & card1 = it1->second;
    vecSeq::size_type maxStart = card1.start;
    vecSeq::size_type minStart = card1.start;
    vecSeq::size_type period = card1.period;
    phaseGroups.push_back(PhaseGroupCard(period));
    PhaseGroupCard & phaseGroup = phaseGroups.back();
    phaseGroup.phases.push_back(var1);
    phaseGroup.indices.push_back(imap[var1]);

    vector< pair<ID, PeriodicSignalCard> >::const_iterator it2 = it1;
    for (++it2; it2 != cards.end(); ++it2) {
      ID var2 = it2->first;
      if (grouped.find(var2) != grouped.end()) continue;
      PeriodicSignalCard const & card2 = it2->second;
      if (card2.period == period) {
        if (verbosity > Options::Informative) {
          vector<ID> vec(1,var1);
          vec.push_back(var2);
          cout << "Clocks " << idString< vector<ID> >(v, vec, false)
               << " have the same period" << endl;
        }
        maxStart = card2.start > maxStart ? card2.start : maxStart;
        minStart = card2.start < minStart ? card2.start : minStart;
        bool mutuallyExclusive = true;
        for (vecSeq::size_type i = 0; i < maxStart + period; ++i) {
          if (lasso[i][imap[var2]] != TVFalse) {
            for (vector< vector<ID>::size_type >::size_type j = 0;
                 j < phaseGroup.indices.size(); ++j) {
              if (lasso[i][phaseGroup.indices[j]] != TVFalse) {
                mutuallyExclusive = false;
                break;
              }
            }
          }
        }
        if (mutuallyExclusive) {
          phaseGroup.phases.push_back(var2);
          phaseGroup.indices.push_back(imap[var2]);
          grouped.insert(var2);
        }
      }
    }
    phaseGroup.maxStart = maxStart;
    phaseGroup.minStart = minStart;
    if (verbosity > Options::Terse) {
      cout << "Phase group (period " << phaseGroup.period << ") "
           << idString< vector<ID> >(v, phaseGroup.phases);
    }
  }
}


/** Class to check for equivalence of two signals under assumptions. */
class SATchecker {
public:
  SATchecker(Model & model, Expr::Manager::View & ev, CNFAttachment const * cat, SAT::Clauses * constraints = 0) :
    model_(model), cat_(cat), ev_(ev) {
    satman_ = model.newSATManager();
    sview_ = satman_->newView(ev);
    SAT::Clauses tr = cat->getPlainCNF();
    sview_->add(tr);
    if (constraints)
      sview_->add(*constraints);
  }
  ~SATchecker() {
    delete sview_;
    delete satman_;
  }
  bool operator()(ID f, ID g, ID assumption) {
    if (f == g) return true;
    if (ev_.apply(Expr::Not, f) == g) return false;
    SAT::GID gid = sview_->newGID();
    ID fprime = ev_.prime(f);
    SAT::Clause c1(1,f);
    c1.push_back(fprime);
    SAT::Clauses clauses(1,c1);
    SAT::Clause c2(1,ev_.apply(Expr::Not, f));
    c2.push_back(ev_.apply(Expr::Not, fprime));
    clauses.push_back(c2);
    sview_->add(clauses, gid);
    vector<ID> moreclauses(1,assumption);
    int rv = sview_->sat(&moreclauses);
    sview_->remove(gid);
    return !rv;
  }
private:
  Model & model_;
  CNFAttachment const * cat_;
  Expr::Manager::View & ev_;
  SAT::Manager * satman_;
  SAT::Manager::View * sview_;
};


/* Create clauses from the overapproximation to the reachable states
 * produced by ternary simulation and add them to the set of
 * constraints to be used by the SAT checker. */
void buildConstraintsFromSimulationResults(
  Expr::Manager::View & v,
  vecSeq const & lasso,
  vector<ID> const & sv,
  PersistentCardMap const & pmap,
  PeriodicCardMap const & cmap,
  SAT::Clauses & clauses)
{
  // Add unit clauses for stuck latches.
  vector<bool> isStuck(sv.size(),false);
  for (vector<ID>::size_type i = 0; i < sv.size(); ++i) {
    PersistentCardMap::const_iterator pit = pmap.find(sv[i]);
    if (pit != pmap.end()) {
      pair<ID, PersistentSignalCard> card = *pit;
      if (card.second.numberTransitions == 0) {
        isStuck[i] = true;
        ID id = (card.second.finalValue == TVFalse) ? v.apply(Expr::Not, card.first) : card.first;
        SAT::Clause clause(1,id);
        //cout << ": " << idString<SAT::Clause>(v, clause);
        clauses.push_back(clause);
      }
    }
  }
  // Create DNF for simulation results.
  if (sv.size() * lasso.size() < 1000000) {
    vector<ID> rows;
    for (vecSeq::size_type i = 0; i < lasso.size(); ++i) {
      vector<ID> cube;
      for (vector<ID>::size_type j = 0; j < sv.size(); ++j) {
        if (!isStuck[j] && lasso[i][j] != TVX &&
            (pmap.find(sv[j]) != pmap.end() || cmap.find(sv[j]) != cmap.end())) {
          cube.push_back(lasso[i][j] == TVTrue ? sv[j] : v.apply(Expr::Not, sv[j]));
        }
      }
      rows.push_back(v.apply(Expr::And, cube));
    }
    ID dnf = v.apply(Expr::Or, rows);
    Expr::tseitin(v, dnf, clauses);
  }
  // else we should attempt something else
}


/** Comparison function called by prepareConstraints to sort
 *  persistent signals. */
bool comparePersistentLast(pair<ID, PersistentSignalCard> const & a,
                           pair<ID, PersistentSignalCard> const & b)
{
  return (a.second.lastTransition <  b.second.lastTransition) ||
    ((a.second.lastTransition ==  b.second.lastTransition) &&
     ((a.second.firstTransition <  b.second.firstTransition) ||
      ((a.second.firstTransition ==  b.second.firstTransition) &&
       (a.second.numberTransitions <  b.second.numberTransitions))));
}


/** Build one or two-literal clauses from the persistent signals. */
void prepareConstraints(Expr::Manager::View & v, PersistentCardMap const & map, SAT::Clauses & clauses)
{
  // If a non-stuck signal makes its first transition no sooner than another
  // signal's last transition, then when it has its final value, so does the
  // other signal.  Conversely, when the other signal still has its initial
  // value, so does this signal.  If initial and final values are distinct for
  // the antecedent signal, then we can write clauses expressing these implications.

  // Build a vector of cards sorted in increasing order of last transition.
  // The stuck-at signals come first, followed by the eventually stuck signals.
  vector< pair<ID, PersistentSignalCard> > cards(map.begin(),map.end());
  sort(cards.begin(), cards.end(), comparePersistentLast);

  for (vector< pair<ID, PersistentSignalCard> >::size_type i=0; i < cards.size(); ++i) {
    pair<ID, PersistentSignalCard> card = cards[i];
#if 0
    cout << "Dealing with " << idString< vector<ID> >(v, vector<ID>(1,card.first));
    cout << card.second.initialValue << "," << card.second.finalValue << ","
         << card.second.firstTransition << "," << card.second.lastTransition << ","
         << card.second.wasX << endl;
#endif
    if (card.second.numberTransitions == 0) {
      ID id = (card.second.finalValue == TVFalse) ? v.apply(Expr::Not, card.first) : card.first;
      SAT::Clause clause(1,id);
      //cout << ": " << idString<SAT::Clause>(v, clause);
      clauses.push_back(clause);
    } else if (i > 0) {
      ID id = (card.second.finalValue == TVTrue) ? v.apply(Expr::Not, card.first) : card.first;
      vector< pair<ID, PersistentSignalCard> >::size_type j = i;
      while (j > 0) {
        --j;
        pair<ID, PersistentSignalCard> otherCard = cards[j];
        if (otherCard.second.numberTransitions == 0)
          break;
        if (otherCard.second.lastTransition <= card.second.firstTransition) {
          if (card.second.initialValue != card.second.finalValue) {
            // This signal can imply based on final value.
            SAT::Clause clause(1,id);
            ID otherId = (otherCard.second.finalValue == TVFalse) ?
              v.apply(Expr::Not, otherCard.first) : otherCard.first;
            clause.push_back(otherId);
            //cout << ": " << idString<SAT::Clause>(v, clause);
            clauses.push_back(clause);
            if (card.second.lastTransition <= otherCard.second.firstTransition) {
              // The two signals make exactly one transition at the same time.
              // They are either identical or complementary.
              SAT::Clause secondClause(1,v.apply(Expr::Not, id));
              secondClause.push_back(v.apply(Expr::Not, otherId));
              //cout << ": " << idString<SAT::Clause>(v, secondClause);
              clauses.push_back(secondClause);
            }
            //break;
          } else if (otherCard.second.initialValue != otherCard.second.finalValue) {
            // The other signal can imply based on initial value.
            SAT::Clause clause(1,v.apply(Expr::Not, id));
            ID otherId = (otherCard.second.initialValue == TVTrue) ?
              v.apply(Expr::Not, otherCard.first) : otherCard.first;
            clause.push_back(otherId);
            //cout << ": " << idString<SAT::Clause>(v, clause);
            clauses.push_back(clause);
            //break;
          }
        }
      }
    }
  }
}


/** Collect the roots for the phase finder folder. */
void collectRoots(Expr::Manager::View & v, ExprAttachment const *eat, vector<ID> & roots)
{
  vector<ID> const & sv = eat->stateVars();
  vector<ID> const & of = eat->outputFns();
  vector<ID> const & nsfv = eat->nextStateFns();
  /* If constant values propagate through latches, we want the latches to
   * be visited in order of propagation. */
  vector< vector< vector<ID> > > sccv = sortStateVarsBySccHeight(v, of, sv, nsfv);
  for (vector< vector< vector<ID> > >::const_iterator it = sccv.begin();
       it != sccv.end(); ++it)
    for (vector< vector<ID> >::const_iterator it2 = it->begin();
         it2 != it->end(); ++ it2)
      roots.insert(roots.end(), it2->begin(), it2->end());
  //cout << "Roots: " << idString< vector<ID> >(v, roots);
}


/** Choose the phase to retain. */
TV choosePhase(TV outputPhase, unordered_set<ID> phase0, unordered_set<ID> phase1)
{
  if (phase0.size() > phase1.size())
    return TVTrue;
  else if (phase0.size() < phase1.size())
    return TVFalse;
  else
    return outputPhase;
}

} // anonymous namespace


namespace Expr {

/** Phase finder folder. */
class PhasePhinder : public Manager::View::Folder {
public:
  PhasePhinder(Manager::View & v, Model & model, SATchecker & checker,
               unordered_map<ID,ID> & lmap, unordered_set<ID> & phase0,
               unordered_set<ID> & phase1, unordered_set<ID> & selfDep,
               ID phi0, ID phi1, Options::Verbosity verbosity):
    Manager::View::Folder(v), model_(model), checker_(checker), lmap_(lmap),
    phase0_(phase0), phase1_(phase1), selfDep_(selfDep), phi0_(phi0),
    phi1_(phi1), verbosity_(verbosity), satcalls_(0), satproofs_(0),
    iterations_(0)
  {
    if (verbosity_ > Options::Terse) {
      vector<ID> prv(1, phi1_);
      prv.push_back(phi0_);
      cout << "Phi1, phi0: " << idString(view(), prv);
    }
    // smap0_ is the substitution that asserts phi0_
    // similarly for smap1_
    if (view().op(phi0_) == Not) {
      ID n0 = view().apply(Not, phi0_);
      smap0_[n0] = view().bfalse();
      smap1_[n0] = view().btrue();
    } else {
      smap0_[phi0_] = view().btrue();
      smap1_[phi0_] = view().bfalse();
    }
    if (view().op(phi1_) == Not) {
      ID n1 = view().apply(Not, phi1_);
      smap0_[n1] = view().btrue();
      smap1_[n1] = view().bfalse();
    } else {
      smap0_[phi1_] = view().bfalse();
      smap1_[phi1_] = view().btrue();
    }
  }


  /** Try to label each latch with a phase.  There are two mechanisms
   *  to assign a phase to a latch.  If in one phase of the clock the
   *  latch holds its value, then it's labeled with the other phase.
   *  If all variables in the support of the latch belong to the same
   *  phase, then the latch inherits the opposite phase.  Primary
   *  inputs are labeled lazily as needed.
   */
  ID fold(ID id, int n, const ID * const args) {
    assert(view().op(id) ==  Var);
    unordered_map<ID,ID>::const_iterator it = lmap_.find(id);
    assert(it != lmap_.end());  // only latches should be roots
    if (hasPhase(id)) return id;
    if (id == phi1_ || id == phi0_) return id;
    int phased = -1;
    ID nsf = it->second;
    if (verbosity_ > Options::Informative)
      cout << "Processing " << idString< vector<ID> >(view(), vector<ID>(1, id), false) << ": " << flush;
    if (syntaxPhaseCheck(id, nsf, true /* phase 0 */)) {
      phase0_.insert(id);
      phased = 0;
    } else if (syntaxPhaseCheck(id, nsf, false /* phase 1 */)) {
      phase1_.insert(id);
      phased = 1;
    } else if (nsf == view().btrue() || nsf == view().bfalse()) {
      // If the next state function is constant, the latch changes at most
      // once at time 1.
      // Currently, we assume that latches that only change odd times are
      // phase-0 latches.  It works when the implicit clock is divided by two by
      // a latch that starts at 0.  In general, this needs to be more nuanced.
      phase0_.insert(id);
      phased = 0;
    } else if (iterations_ == 0 && (satproofs_ * 2 + 10 > satcalls_)) {
      // SAT checks don't benefit from iterations: don't repeat them.
      // Also, don't insist if success rate is low.
      bool rv = checker_(id, nsf, phi1_);
      ++satcalls_;
      if (rv) {
        ++satproofs_;
        phase0_.insert(id);
        phased = 0;
      } else {
        rv = checker_(id, nsf, phi0_);
        ++satcalls_;
        if (rv) {
          ++satproofs_;
          phase1_.insert(id);
          phased = 1;
        }
      }
    }
    if (verbosity_ > Options::Informative)
      cout << idString< vector<ID> >(view(), vector<ID>(1,id), false)
           << ": " << phased << endl;
    return id;
  }


  void label(vector<ID> & roots)
  {
    // Iterate labeling to a fixpoint.
    bool improved = true;
    while (improved) {
      unordered_set<ID>::size_type count = phase0_.size() + phase1_.size();
      view().fold(*this, roots);
      ++iterations_;
      improved = phase0_.size() + phase1_.size() > count;
    }
    check();

    // Remove primary inputs from sets of labeled variables.
    for (unordered_set<ID>::iterator it = phase1_.begin();
         it != phase1_.end();)
      if (lmap_.find(*it) == lmap_.end() || *it == phi1_ || *it == phi0_)
        phase1_.erase(it++);
      else
        ++it;
    for (unordered_set<ID>::iterator it = phase0_.begin();
         it != phase0_.end();)
      if (lmap_.find(*it) == lmap_.end() || *it == phi1_ || *it == phi0_)
        phase0_.erase(it++);
      else
        ++it;

    if (verbosity_ > Options::Terse)
      cout << "labeling: " << iterations_ << " iterations and "
           << satcalls_ << " SAT calls (" << satproofs_
           << " successful)" << endl;
  }


  bool outputPhaseCheck(ID f, bool ph0)
  {
    if (ph0) {
      if (phase0_.find(f) != phase0_.end())
        return true;
    } else {
      if (phase1_.find(f) != phase1_.end())
        return true;
    }
    /* Not labeled yet.  This is not a latch. */
    view().begin_local();
    f = varSub(view(), smap1_, f);
    bool ok = syntacticSupportCheck(f, !ph0);
    view().end_local();
    return ok;
  }


  void check()
  {
    unsigned failed = 0;
    if (verbosity_ > Options::Silent)
      cout << "starting check" << endl;
    for (unordered_set<ID>::const_iterator it = phase0_.begin();
         it != phase0_.end(); ++it) {
      unordered_map<ID,ID>::const_iterator fit = lmap_.find(*it);
      if (fit != lmap_.end()) {
        // It's a latch
        ID nsf = fit->second;
        if (!supportCheck(*it, nsf, true /* phase 0 */)) {
          ++failed;
        }
      }
    }
    if (verbosity_ > Options::Silent)
      cout << "done with phase 0 signals" << endl;
    for (unordered_set<ID>::const_iterator it = phase1_.begin();
         it != phase1_.end(); ++it) {
      unordered_map<ID,ID>::const_iterator fit = lmap_.find(*it);
      if (fit != lmap_.end()) {
        ID nsf = fit->second;
        if (!supportCheck(*it, nsf, false /* phase 1 */)) {
          ++failed;
        }
      }
    }
    if (verbosity_ > Options::Silent) {
      cout << "done with phase 1 signals" << endl;
      cout << selfDep_.size() << " latches depend on themselves" << endl;
      if (failed > 0)
        cout << failed << " failed checks" << endl;
    }
  }

private:
  bool supportCheck(ID id,  ID nsf, bool ph0)
  {
    view().begin_local();
    nsf = varSub(view(), (ph0 ? smap0_ : smap1_), nsf);
    set<ID> support;
    variables(view(), nsf, support);
    bool ok = true;

    unordered_set<ID> & otherPhase = ph0 ? phase1_ : phase0_;
    for (set<ID>::const_iterator var = support.begin(); var != support.end(); ++var) {
      if (*var == id) {
        // True if this latch has a gated clock (but not only).
        if (verbosity_ > Options::Informative)
          cout << stringOf(view(), id) << " depends on itself" << endl;
        selfDep_.insert(id);
      } else if (otherPhase.find(*var) == otherPhase.end() && lmap_.find(*var) != lmap_.end()) {
        if (verbosity_ > Options::Informative) {
          cout << stringOf(view(), id) << " fails support check because of "
               << stringOf(view(), *var) << endl;
          cout << "Support: " << idString< set<ID> >(view(), support);
        }
        ok = false;
        break;
      }
    }
    view().end_local();
    return ok;
  }


  bool syntacticSupportCheck(ID f, bool ph0)
  {
    set<ID> support;
    variables(view(), f, support);
    vector<ID> deferredInputs;
    unordered_set<ID> & thisPhase = ph0 ? phase0_ : phase1_;
    unordered_set<ID> & otherPhase = ph0 ? phase1_ : phase0_;
    for (set<ID>::const_iterator var = support.begin(); var != support.end(); ++var) {
      if (otherPhase.find(*var) == otherPhase.end()) {
        if (iterations_ > 0 && lmap_.find(*var) == lmap_.end() && thisPhase.find(*var) == thisPhase.end())
          deferredInputs.push_back(*var);
        else {
          if (verbosity_ > Options::Informative)
            cout << "Checking support: " << idString< set<ID> >(view(), support);
          return false;
        }
      }
    }
    for (vector<ID>::const_iterator var = deferredInputs.begin();
         var != deferredInputs.end(); ++var)
      otherPhase.insert(*var);
    return true;
  }


  bool syntaxPhaseCheck(ID id, ID nsf, bool ph0)
  {
    view().begin_local();
    nsf = varSub(view(), (ph0 ? smap1_ : smap0_), nsf);
    bool ok = id == nsf;
    if (!ok)
      ok = syntacticSupportCheck(nsf, ph0);
    view().end_local();
    return ok;
  }


  bool hasPhase(ID id) {
    if (phase0_.find(id) != phase0_.end()) return true;
    return (phase1_.find(id) != phase1_.end());
  }


  Model & model_;
  SATchecker & checker_;
  unordered_map<ID,ID> & lmap_;
  unordered_set<ID> & phase0_;
  unordered_set<ID> & phase1_;
  unordered_set<ID> & selfDep_;
  ID phi0_;
  ID phi1_;
  IDMap smap0_;
  IDMap smap1_;
  Options::Verbosity verbosity_;
  unsigned satcalls_;
  unsigned satproofs_;
  unsigned iterations_;
};

} // namespace Expr


namespace {

typedef vector< pair<unordered_set<ID>,unordered_set<ID> > > PhasePartition;

/** Find blocks of latches that are amenable to phase abstraction.
 *  Singletons are not explicitly mentioned.
 *  This function is restricted to two-phase clocks.  The clusters
 *  are called Minimal Dependent Layers (MDLs) in Baumgartner et al.. */
void phasePartition(
  Expr::Manager::View & ev,
  Model & model,
  unordered_map<ID,ID> const & lmap,
  unordered_set<ID> const & phase0,
  unordered_set<ID> const & phase1,
  ID ph0,
  ID ph1,
  PhasePartition & partition)
{
  Options::Verbosity verbosity = model.verbosity();

  unordered_map<ID,ID> smap0, smap1;
  // smap0 is the substitution that asserts phi0
  // similarly for smap1
  if (ev.op(ph0) == Expr::Not) {
    ID n0 = ev.apply(Expr::Not, ph0);
    smap0[n0] = ev.bfalse();
    smap1[n0] = ev.btrue();
  } else {
    smap0[ph0] = ev.btrue();
    smap1[ph0] = ev.bfalse();
  }
  if (ev.op(ph1) == Expr::Not) {
    ID n1 = ev.apply(Expr::Not, ph1);
    smap0[n1] = ev.btrue();
    smap1[n1] = ev.bfalse();
  } else {
    smap0[ph1] = ev.bfalse();
    smap1[ph1] = ev.btrue();
  }

  typedef unordered_map<ID, set<ID> > VMap;

  // Build fanin and fanout maps for all latches.
  VMap fanin_map;
  VMap fanout_map;
  // Initialize fanouts to empty sets.
  for (unordered_map<ID,ID>::const_iterator it = lmap.begin(); it != lmap.end(); ++it) {
    set<ID> vars;
    fanout_map.insert(VMap::value_type(it->first,vars));
  }
  ev.begin_local();
  for (unordered_map<ID,ID>::const_iterator it = lmap.begin(); it != lmap.end(); ++it) {
    ID cs = it->first;
    ID nsf = it->second;
    if (phase0.find(cs) != phase0.end()) {
      nsf = varSub(ev, smap0, nsf);
    } else if (phase1.find(cs) != phase1.end()) {
      nsf = varSub(ev, smap1, nsf);
    }
    set<ID> vars;
    variables(ev, nsf, vars);
    fanin_map.insert(VMap::value_type(cs, vars));
    for (set<ID>::const_iterator si = vars.begin(); si != vars.end(); ++si) {
      VMap::iterator fi = fanout_map.find(*si);
      if (fi != fanout_map.end())
        fi->second.insert(cs);
    }
  }
  ev.end_local();

  // Go through the latches one by one and try to form clusters.
  unordered_set<ID> clustered;
  for (unordered_map<ID,ID>::const_iterator it = lmap.begin(); it != lmap.end(); ++it) {
    ID var = it->first;
    if (clustered.find(var) != clustered.end()) continue;
    TV cphase = phase0.find(var) != phase0.end() ? TVFalse :
      phase1.find(var) != phase1.end() ? TVTrue : TVX;
    if (cphase == TVX) continue;
    if (verbosity > Options::Informative) {
      ostringstream oss;
      shortStringOfID(ev, var, oss);
      cout << "Clustering around " << oss.str()
           << " (phase " << cphase << ")" << endl;
    }
    unordered_set<ID> cluster0, cluster1;
    unordered_set<ID> new0, new1;
    if (cphase == TVFalse) {
      cluster0.insert(var);
      new0.insert(var);
    } else {
      cluster1.insert(var);
      new1.insert(var);
    }
    bool phaseOk = true;
    while (phaseOk && new0.size() + new1.size() > 0) {
      for (unordered_set<ID>::const_iterator nit = new0.begin(); nit != new0.end(); ++nit) {
        VMap::const_iterator vit = fanout_map.find(*nit);
        set<ID> const & fo = vit->second;
        for (set<ID>::const_iterator foi = fo.begin(); foi != fo.end(); ++ foi) {
          if (*foi == *nit) continue;
          if (phase1.find(*foi) == phase1.end()) {
            if (verbosity > Options::Terse) {
              ostringstream oss;
              shortStringOfID(ev, *nit, oss);
              cout << "Failed with " << oss.str() << ".  Fanout: " << idString(ev, fo);
            }
            phaseOk = false;
            break;
          }
          if (cluster1.find(*foi) == cluster1.end()) {
            new1.insert(*foi);
            cluster1.insert(*foi);
          }
        }
        if (!phaseOk) break;
      }
      new0.clear();

      if (!phaseOk) break;

      for (unordered_set<ID>::const_iterator nit = new1.begin(); nit != new1.end(); ++nit) {
        VMap::const_iterator vit = fanin_map.find(*nit);
        set<ID> const & fi = vit->second;
        for (set<ID>::const_iterator fii = fi.begin(); fii != fi.end(); ++ fii) {
          if (*fii == *nit || *fii == ph0 || *fii == ph1) continue;
          if (phase0.find(*fii) == phase0.end()) {
            if (verbosity > Options::Terse) {
              ostringstream oss;
              shortStringOfID(ev, *nit, oss);
              cout << "Failed with " << oss.str() << ".  Fanin: " << idString(ev, fi);
            }
            phaseOk = false;
            break;
          }
          if (cluster0.find(*fii) == cluster0.end()) {
            new0.insert(*fii);
            cluster0.insert(*fii);
          }
        }
        if (!phaseOk) break;
      }
      new1.clear();
    }

    if (phaseOk) {
      partition.push_back(PhasePartition::value_type(cluster0,cluster1));
      // Mark all latches as clustered
      for (unordered_set<ID>::const_iterator ci = cluster0.begin(); ci != cluster0.end(); ++ci) {
        clustered.insert(*ci);
      }
      for (unordered_set<ID>::const_iterator ci = cluster1.begin(); ci != cluster1.end(); ++ci) {
        clustered.insert(*ci);
      }
    } else {
      // Phase check didn't work.
      if (verbosity > Options::Terse) {
        ostringstream oss;
        shortStringOfID(ev, var, oss);
        cout << "Failed to cluster " << oss.str() << endl;
      }
      clustered.insert(var);
    }
  }
  if (verbosity > Options::Terse) {
    set<ID>::size_type size0 = 0, size1 = 0;
    cout << "Phase clustering results:" << endl;
    for (PhasePartition::const_iterator it = partition.begin(); it != partition.end(); ++it) {
      size0 += it->first.size();
      size1 += it->second.size();
      cout << "Cluster(0): " << idString(ev, it->first);
      cout << "Cluster(1): " << idString(ev, it->second);
    }
    cout << "Clustered " << size0 << " phase 0 latches and "
         << size1 << " phase 1 latches" << endl;
  }
}


/** Abstract latches of one phase. The phase to be kept is
 *  given by parameter phi. */
void phaseAbstract(
  Model & model,
  Expr::Manager::View * ev,
  ID phi,
  unordered_set<ID> const & tossPhase,
  unordered_set<ID> const & keepPhase,
  unordered_set<ID> const & selfDep,
  vecSeq const & lasso,
  PersistentCardMap const & persistentMap,
  PeriodicCardMap const & periodicMap)
{
  Options::Verbosity verbosity = model.verbosity();
  if (verbosity > Options::Silent)
    cout << "Keeping phase " << Expr::stringOf(*ev, phi) << endl;

  SeqAttachment * squat = (SeqAttachment *) model.attachment(Key::SEQ);
  ExprAttachment * eat = (ExprAttachment *) model.attachment(Key::EXPR);

  if (tossPhase.size() + keepPhase.size() + 1 != eat->stateVars().size())
    cout << (tossPhase.size() + keepPhase.size())
         << " labeled latches instead of "
         << (eat->stateVars().size() - 1)
         << ".  Proceed at your own risk." << endl;

  if (squat->stateVars.empty()) {
    squat->stateVars = eat->stateVars();
    squat->nextStateFns = eat->nextStateFns();
  }

  // Build implication set from lasso.
  implSet implications;
  unordered_map<ID,ID> equivalences;
  unordered_set<ID> ignore;
  // Ignore implications involving latches of the phase to
  // be tossed unless their clock is gated.
  for (unordered_set<ID>::const_iterator it = tossPhase.begin();
       it != tossPhase.end(); ++it) {
    if (selfDep.find(*it) == selfDep.end())
      ignore.insert(*it);
  }
  // It's infeasible to produce all the constraints between
  // latches for large networks.
  if (eat->stateVars().size() > 600)
    findImplicationsLight(*ev, ignore, persistentMap, periodicMap, lasso,
                          implications, equivalences, verbosity);
  else
    findImplications(*ev, eat->stateVars(), ignore, lasso, implications, equivalences, verbosity);
  Expr::Simplifier simp(*ev, implications, equivalences, verbosity);

  // Substitution map for the phase to be abstracted: phi is negated
  // so that the latches are in transparent mode.
  unordered_map<ID,ID> tossMap;

  if (ev->op(phi) == Expr::Not) {
    tossMap.insert(unordered_map<ID, ID>::value_type(ev->apply(Expr::Not, phi),ev->btrue()));
  } else {
    tossMap.insert(unordered_map<ID, ID>::value_type(phi,ev->bfalse()));
  }

  vector<ID> tossCs, tossNs;
  for (unordered_set<ID>::const_iterator it = tossPhase.begin();
       it != tossPhase.end(); ++it) {
    tossCs.push_back(*it);
    ID ns = eat->nextStateFnOf(*it);
    tossNs.push_back(ns);
  }
  Expr::varSub(*ev, tossMap, tossNs);
  simp.simplify(tossNs);

  // Build substitution map.  The current-state variable of each latch to
  // be abstracted is replaced by its next-state function.  The surviving
  // clock phase is asserted.
  unordered_map<ID,ID> map;

  if (ev->op(phi) == Expr::Not) {
    map.insert(unordered_map<ID, ID>::value_type(ev->apply(Expr::Not, phi),ev->bfalse()));
  } else {
    map.insert(unordered_map<ID, ID>::value_type(phi,ev->btrue()));
  }

  for (vector<ID>::size_type i = 0; i < tossCs.size(); ++i) {
    map.insert(unordered_map<ID, ID>::value_type(tossCs[i],tossNs[i]));
    // Don't know what to do.  Arbitrarily replace with ns.
    squat->optimized.insert(unordered_map<ID, ID>::value_type(tossCs[i],tossNs[i]));
  }

  vector<ID> keepCs, keepNs;
  for (unordered_set<ID>::const_iterator it = keepPhase.begin();
       it != keepPhase.end(); ++it) {
    keepCs.push_back(*it);
    ID ns = eat->nextStateFnOf(*it);
    keepNs.push_back(ns);
  }

  Expr::varSub(*ev, map, keepNs);
  simp.simplify(keepNs);

  // Keep self-dependent latches of the other phase.
  for (vector<ID>::size_type i = 0; i < tossCs.size(); ++i) {
    ID cs = tossCs[i];
    if (selfDep.find(cs) != selfDep.end()) {
      keepCs.push_back(cs);
      ID ns = tossNs[i];
      keepNs.push_back(ns);
    }
  }

  eat->clearNextStateFns();
  eat->setNextStateFns(keepCs, keepNs);

  vector<ID> init(eat->initialConditions());
  if (squat->initialConditions.empty())
    squat->initialConditions = init;
  eat->clearInitialConditions();
  for (vector<ID>::const_iterator it = init.begin(); it != init.end(); ++it) {
    ID var = ev->op(*it) == Expr::Not ? ev->apply(Expr::Not, *it) : *it;
    if (keepPhase.find(var) != keepPhase.end() || selfDep.find(var) != selfDep.end())
      eat->addInitialCondition(*it);
  }

  // Currently constraints of all kinds are not dealt with properly.

  vector<ID> outputs(eat->outputs());
  vector<ID> outputFns(eat->outputFnOf(outputs));
  eat->clearOutputFns();
  Expr::varSub(*ev, map, outputFns);
  simp.simplify(outputFns);
  eat->setOutputFns(outputs, outputFns);

  vector<ID> bad(eat->bad());
  vector<ID> badFns(eat->badFnOf(bad));
  eat->clearBadFns();
  Expr::varSub(*ev, map, badFns);
  eat->setBadFns(bad, badFns);

  vector<ID> fairness(eat->fairness());
  vector<ID> fairnessFns(eat->fairnessFnOf(fairness));
  eat->clearFairnessFns();
  Expr::varSub(*ev, map, fairnessFns);
  eat->setFairnessFns(fairness, fairnessFns);

  vector<ID> justice(eat->justice());
  vector< vector<ID> > justiceS(eat->justiceSets());
  eat->clearJusticeSets();
  for (size_t i = 0; i < justiceS.size(); ++i) {
    Expr::varSub(*ev, map, justiceS[i]);
    eat->setJusticeSet(justice[i], justiceS[i]);
  }

  vector<ID> ctlProps(eat->ctlProperties());
  eat->clearCtlProperties();
  Expr::varSub(*ev, map, ctlProps);
  eat->addCtlProperties(ctlProps);

  vector<ID> constraints(eat->constraints());
  vector<ID> constraintFns(eat->constraintFns());
  eat->clearConstraints();
  simp.simplify(constraintFns);
  for (vector<ID>::size_type i = 0; i != constraintFns.size(); ++i) {
    ID f = Expr::varSub(*ev, map, constraintFns[i]);
    if (f != ev->btrue())
      eat->addConstraint(constraints[i], f);
  }
  unordered_set<ID> lset(keepCs.begin(), keepCs.end());
  vector<ID> constrVec;
  for (implSet::const_iterator it = implications.begin(); it != implications.end(); ++it) {
    ID lit0 = it->first;
    ID lit1 = it->second;
    ID n0 = ev->apply(Expr::Not, lit0);
    ID n1 = ev->apply(Expr::Not, lit1);
    ID var0 = (ev->op(lit0) == Expr::Not) ? n0 : lit0;
    ID var1 = (ev->op(lit1) == Expr::Not) ? n1 : lit1;
    assert(lset.find(var0) != lset.end() && lset.find(var1) != lset.end());
    if (keepPhase.find(var0) == keepPhase.end() || keepPhase.find(var1) == keepPhase.end()) {
      continue;
    }
    ID cid = ev->apply(Expr::Or, lit0, lit1);
    constrVec.push_back(cid);
  }
  Expr::varSub(*ev, equivalences, constrVec);
  sort(constrVec.begin(), constrVec.end());
  vector<ID>::iterator newEnd = unique(constrVec.begin(), constrVec.end());
  vector<ID>::size_type i = constraints.size();
  for (vector<ID>::const_iterator it = constrVec.begin(); it != newEnd; ++it) {
    if (*it == ev->btrue())
      continue;
    ostringstream oss;
    oss << 'c' << i;
    string nm = oss.str();
    ID vid = ev->newVar(nm);
    ++i;
    eat->addConstraint(vid, *it);
  }
  model.release(eat);
  model.release(squat);
}


} // namespace anonymous


void PhaseAbstractionAction::exec()
{
  // Setup.  Get attachments and such stuff.
  int64_t startTime = Util::get_user_cpu_time();
  Options::Verbosity verbosity = _model.verbosity();
  bool layered = _model.options().count("phase_layered") > 0;
  if (verbosity > Options::Silent)
    cout << "Phase analysis of model " << _model.name() << endl;

  ExprAttachment const * eat = (ExprAttachment const *) model().constAttachment(Key::EXPR);
  if (eat->constraints().size() > 0) {
    if (verbosity > Options::Terse)
      cout << "Model has transition constraints" << endl;
    return;
  }
  if (eat->justice().size() > 0) {
    if (verbosity > Options::Terse)
      cout << "Model has justice constraints" << endl;
    return;
  }
  if (eat->fairness().size() > 0) {
    if (verbosity > Options::Terse)
      cout << "Model has fairness constraints" << endl;
    return;
  }
  if (eat->outputFns().size() != 1) {
    if (verbosity > Options::Terse)
      cout << "More has more than one output" << endl;
    return;
  }

  Expr::Manager::View * ev = model().newView();

  // Ternary simulation to find periodic and persistent signals.
  bool allowWidening = _model.options().count("tv_narrow") == 0;
  vecSeq lasso;
  AIGAttachment const * aat = (AIGAttachment const *) model().constAttachment(Key::AIG);
  vecSeq::size_type stem = ThreeValued::computeLasso(*ev, eat->initialConditions(), eat->outputFns(),
                                                     aat, lasso, verbosity, allowWidening);
  model().constRelease(aat);
  
  // Find (eventually) periodic and persistent signals.
  vector<ID> const & sv = eat->stateVars();
  PersistentCardMap persistentMap;
  PeriodicCardMap periodicMap;
  findInterestingSignals(lasso, sv, stem, persistentMap, periodicMap);

  printReport(verbosity, lasso, *ev, sv, persistentMap, periodicMap);

  if (layered) {
    PhaseGroupVec phaseGroups;
    findPeriodicSets(*ev, lasso, sv, periodicMap, verbosity, phaseGroups);

    bool abstract = false;
    unordered_set<ID> phase0, phase1, selfDep;
    ID ph1, ph0;
    TV outputPhase = TVX;
    if (!phaseGroups.empty()) {
      vector<ID> const & nsfv = eat->nextStateFns();
      assert(sv.size() == nsfv.size());

      // Create map from state variables to their next-state functions
      // to be used by the folder.
      unordered_map<ID,ID> lmap;
      for (vector<ID>::size_type i = 0; i < sv.size(); ++i) {
        lmap[sv[i]] = nsfv[i];
      }

      // Classify latches.
      CNFAttachment const * cat = (CNFAttachment const *) model().constAttachment(Key::CNF);
      // Prepare constraints and add them as assumptions.
      ev->begin_local();
      SAT::Clauses constraints;
      //prepareConstraints(*ev, persistentMap, constraints);
      buildConstraintsFromSimulationResults(*ev, lasso, sv, persistentMap, periodicMap, constraints);
      if (verbosity > Options::Terse)
        cout << constraints.size()
             << " clauses generated from ternary simulation" << endl;
      if (verbosity > Options::Informative) {
        for (SAT::Clauses::const_iterator it = constraints.begin(); it != constraints.end(); ++it) {
          cout << idString< vector<ID> >(*ev, *it);
        }
      }

      SATchecker checker(model(), *ev, cat, &constraints);

      // There is no need to "keep" the clauses produced by
      // prepareConstraints, because they do not use any new IDs.
      for (SAT::Clauses::const_iterator it = constraints.begin(); it != constraints.end(); ++it)
        ev->keep(*it);
      ev->end_local();

      //assert(eat->outputFns().size() == 1);
      ID outId = eat->outputFns()[0];
      vector<ID> roots;
      collectRoots(*ev, eat, roots);
      for (PhaseGroupVec::const_iterator it = phaseGroups.begin();
           it != phaseGroups.end(); ++it) {
        PhaseGroupCard phaseGroup = *it;
        if (verbosity > Options::Silent) {
          cout << "Clocks: " << idString<vector<ID>>(*ev, phaseGroup.phases);
          for (vector<ID>::const_iterator pit = phaseGroup.phases.begin();
               pit != phaseGroup.phases.end(); ++pit) {
            PeriodicCardMap::const_iterator card = periodicMap.find(*pit);
            cout << stringOf(*ev, *pit) << " (starts at time " << card->second.start << ") wave: ";
            for (TVvec::const_iterator val = card->second.wave.begin();
                 val != card->second.wave.end(); ++val)
              cout << (*val == TVFalse ? "0" : *val == TVTrue ? "1" : "X");
            cout << endl;
          }
        }
        if (phaseGroup.phases.size() > 2) {
          // not ready for more than 2 phases
          if (verbosity > Options::Silent)
            cout << "too many phases: skipping" << endl;
          continue;
        }
        if (phaseGroup.period != 8 && phaseGroup.period != 4 && phaseGroup.period != 2) {
          // heuristic: unlikely to be a group of clock phases
          if (verbosity > Options::Silent)
            cout << "period too long or not a power of 2: skipping" << endl;
          continue;
        }
        if (phaseGroup.minStart > 2 || phaseGroup.maxStart > phaseGroup.period) {
          // heuristic: unlikely to be a group of clock phases
          if (verbosity > Options::Silent)
            cout << "starting too late: skipping" << endl;
          continue;
        }
        ph1 = phaseGroup.phases[0];
        if (phaseGroup.phases.size() == 1)
          ph0 = ev->apply(Expr::Not, ph1);
        else
          ph0 = phaseGroup.phases[1];
        phase0.clear();
        phase1.clear();
        selfDep.clear();
        Expr::PhasePhinder phinder(*ev, model(), checker, lmap, phase0, phase1,
                                   selfDep, ph0, ph1, verbosity);
        phinder.label(roots);
        outputPhase = phinder.outputPhaseCheck(outId, true) ? TVFalse :
          phinder.outputPhaseCheck(outId, false) ? TVTrue : TVX;
        PhasePartition partition;
        phasePartition(*ev, model(), lmap, phase0, phase1, ph0, ph1, partition);
        if (verbosity > Options::Silent) {
          if (outputPhase == TVFalse)
            cout << "Output is a phase-0 signal" << endl;
          else if (outputPhase == TVTrue)
            cout << "Output is a phase-1 signal" << endl;
          cout << "Phase 0 (" << phase0.size() << "): " << endl;
          if (verbosity > Options::Informative)
            cout << idString<unordered_set<ID> >(*ev, phase0);
          cout << "Phase 1 (" << phase1.size() << "): " << endl;
          if (verbosity > Options::Informative)
            cout << idString<unordered_set<ID> >(*ev, phase1);
        }
        if ((phase1.size() + phase0.size()) == (sv.size() - 1)) { // arbitrary hack
          abstract = true;
          break;
        }
      }
      model().constRelease(cat);
      ev->begin_local();
      ev->end_local(true /* full */);
    }
    model().constRelease(eat);

    if (abstract) {
      TV keepPhase = choosePhase(outputPhase, phase0, phase1);
      if (keepPhase == TVFalse) {
        phaseAbstract(model(), ev, ph0, phase1, phase0, selfDep, lasso,
                      persistentMap, periodicMap);
      } else if (keepPhase == TVTrue) {
        phaseAbstract(model(), ev, ph1, phase0, phase1, selfDep, lasso,
                      persistentMap, periodicMap);
      } else {
        if (verbosity > Options::Silent) 
          cout << "No phase abstraction attempted." << endl;
        simplifyModel(model(), *ev, unordered_set<ID>(), lasso,
                      persistentMap, periodicMap);
      }
    } else {
      if (verbosity > Options::Silent)
        cout << "No phase abstraction attempted." << endl;
      simplifyModel(model(), *ev, unordered_set<ID>(), lasso,
                    persistentMap, periodicMap);
    }
  } else {
    model().constRelease(eat);
    PeriodicCardMap periodicFZMap;
    for(PeriodicCardMap::const_iterator it = periodicMap.begin(); it != periodicMap.end(); ++it) {
      if (it->second.start == 0) {
        periodicFZMap.insert(PeriodicCardMap::value_type(it->first, it->second));
      }
    }

    vecSeq::size_type unrolling = lasso.size() - stem;
    if (periodicFZMap.empty()) {
      if (verbosity > Options::Silent) 
        cout << "PhaseAbs: No periodic signals from time zero found. Abstraction not performed." << endl;
    }
    else if (unrolling > model().options()["phase_max"].as<unsigned>()) {
      if (verbosity > Options::Silent) 
        cout << "PhaseAbs: Loop is too long (" << unrolling << "). Abstraction not performed." << endl;
    }
    else {
      ExprAttachment * eat = (ExprAttachment *) model().attachment(Key::EXPR);
      if (verbosity > Options::Silent) 
        cout << "PhaseAbs: Unrolling " << unrolling << " times." << endl;
      vector<ID> roots(eat->nextStateFns());
      roots.insert(roots.end(), eat->outputFns().begin(), eat->outputFns().end());
      assert(eat->outputFns().size() == 1);
      //roots.insert(roots.end(), eat->constraintFns().begin(), eat->constraintFns().end());
      //roots.insert(roots.end(), eat->badFns().begin(), eat->badFns().end());
      //roots.insert(roots.end(), eat->fairnessFns().begin(), eat->fairnessFns().end());
      const vector<ID> & latches(eat->stateVars());
      const vector<ID> & nsfs(eat->nextStateFns());
      const vector<ID> & inputs(eat->inputs());
      vector<ID> newInputs;
      Expr::IDMap sv2nsf;
      for (unsigned i = 0; i < latches.size(); ++i) {
        sv2nsf.insert(Expr::IDMap::value_type(latches[i], nsfs[i]));
      }
      for (int cycle = unrolling - 1;  cycle >= 0; --cycle) {
        Expr::IDMap map = cycle > 0 ? sv2nsf : Expr::IDMap();
        //Replace periodic latches with constants
        for (PeriodicCardMap::const_iterator it = periodicFZMap.begin(); it != periodicFZMap.end(); ++it) {
          ID latch = it->first;
          ThreeValued::TV value = it->second.wave[cycle % it->second.period];
          if (value == ThreeValued::TVTrue)
            map[latch] = ev->btrue();
          if (value == ThreeValued::TVFalse)
            map[latch] = ev->bfalse();
        }
        //Create inputs
        for (vector<ID>::const_iterator it = inputs.begin(); it != inputs.end(); ++it) {
          ID input = *it;
          string name = ev->varName(input);
          ostringstream oss;
          oss << name << "@cycle" << cycle;
          ID newInput = ev->newVar(oss.str());
          newInputs.push_back(newInput);
          map.insert(Expr::IDMap::value_type(input, newInput));
        }
        Expr::varSub(*ev, map, roots);
        if (cycle > 0)
          roots.push_back(eat->outputFns()[0]);
      }
      //TODO: Generalize
      eat->clearInputs();
      eat->addInputs(newInputs);
      vector<ID> outputs = eat->outputs();
      eat->clearOutputFns();
      vector<ID> phaseOutputs(roots.begin() + nsfs.size(), roots.end());
      eat->setOutputFn(outputs[0], Expr::AIGOfExpr(*ev, ev->apply(Expr::Or, phaseOutputs)));
      vector<ID> stateVars = eat->stateVars();
      vector<ID> nnsfs(roots.begin(), roots.begin() + stateVars.size());
      eat->setNextStateFns(stateVars, nnsfs);
      model().release(eat);
    }
  }

  // Endgame.
  delete ev;
  int64_t endTime = Util::get_user_cpu_time(); 
  if (verbosity > Options::Silent)
    cout << "Phase analysis completed in "
         << ((endTime - startTime) / 1000000.0) << " s" << endl;
}
