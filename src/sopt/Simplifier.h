/* -*- C++ -*- */

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

#ifndef Simplifier_
#define Simplifier_

/** @file Simplifier.h */

#include <vector>
#include <unordered_map>
#include "Model.h"
#include "ExprUtil.h"
#include "ExprAttachment.h"
#include "SeqAttachment.h"
#include "RchAttachment.h"
#include "ProofAttachment.h"
#include "ThreeValuedSimulation.h"
#include "options.h"

class IdPairHash {
public:
  size_t operator()(std::pair<ID,ID> const & p) const
  {
    return p.first * 0x9e3779b9 ^ p.second;
  }
};


/** Type of set of implications. */
typedef std::unordered_set< std::pair<ID,ID>, IdPairHash> implSet;


namespace Expr {

class Simplifier : public Manager::View::Folder {
public:
  Simplifier(Manager::View & v, implSet const & implications,
             std::unordered_map<ID,ID> const & equivalences,
             Options::Verbosity verbosity):
    Manager::View::Folder(v), implications_(implications),
    equivalences_(equivalences), verbosity_(verbosity), reduced_(0), rewritten_(0)
  {
  }
  void simplify(std::vector<ID> & roots);
  ID fold(ID id, int n, const ID * const args);

private:
  ID simplifiedVar(ID id);
  ID simpleRewrite(ID id, ID const * const args);
  ID simplifiedAnd(ID id, const ID * const args);

  implSet const & implications_;
  std::unordered_map<ID,ID> const & equivalences_;
  Options::Verbosity verbosity_;
  unsigned reduced_;
  unsigned rewritten_;
};

} // namespace Expr



/** Base class for "cards" describing signals.  Not directly used
 *  right now.  Just in case we want to store together cards of
 *  signals of different types. */
struct SignalCard {
};


/** Card of a persistent signal.  That is, a signal that
 *  satisfies FG v for v either 0 or 1.  */
struct PersistentSignalCard : public SignalCard {
  PersistentSignalCard(ThreeValued::vecSeq const & lasso, ID var,
                       std::vector<ID>::size_type li);
  PersistentSignalCard(std::vector<ID>::size_type pos, ThreeValued::TV iv,
                       ThreeValued::TV fv, ThreeValued::vecSeq::size_type first,
                       ThreeValued::vecSeq::size_type last,
                       ThreeValued::vecSeq::size_type num, bool x) :
    position(pos), initialValue(iv), finalValue(fv), firstTransition(first),
    lastTransition(last), numberTransitions(num), wasX(x) {}
  std::vector<ID>::size_type position;
  ThreeValued::TV initialValue;
  ThreeValued::TV finalValue;
  ThreeValued::vecSeq::size_type firstTransition;
  ThreeValued::vecSeq::size_type lastTransition;
  ThreeValued::vecSeq::size_type numberTransitions;
  bool wasX;
};


/** Card of an eventually periodic signal. */
struct PeriodicSignalCard : public SignalCard {
  PeriodicSignalCard(ThreeValued::vecSeq const & lasso, ID var,
                     ThreeValued::vecSeq::size_type stem,
                     std::vector<ID>::size_type li);
  std::vector<ID>::size_type position;
  ThreeValued::TVvec wave;
  ThreeValued::vecSeq::size_type period;
  ThreeValued::vecSeq::size_type start;
  bool wasX;
};


/** Card of a group of (alleged) clock phases. */
struct PhaseGroupCard : public SignalCard {
  PhaseGroupCard(ThreeValued::vecSeq::size_type p) : period(p)
  {}
  std::vector<ID> phases;
  std::vector< std::vector<ID>::size_type > indices;
  ThreeValued::vecSeq::size_type period;
  ThreeValued::vecSeq::size_type minStart;
  ThreeValued::vecSeq::size_type maxStart;
};


typedef std::unordered_map<ID, PeriodicSignalCard> PeriodicCardMap;
typedef std::unordered_map<ID, PersistentSignalCard> PersistentCardMap;
typedef std::vector<PhaseGroupCard> PhaseGroupVec;


/** Comparison function to sort periodic signals. */
bool comparePeriodic(std::pair<ID, PeriodicSignalCard> const & a,
                     std::pair<ID, PeriodicSignalCard> const & b);


/** Comparison function to sort persistent signals. */
bool comparePersistent(std::pair<ID, PersistentSignalCard> const & a,
                       std::pair<ID, PersistentSignalCard> const & b);


void findInterestingSignals(
  ThreeValued::vecSeq const & lasso,
  std::vector<ID> const & sv,
  ThreeValued::vecSeq::size_type stem,
  PersistentCardMap & persistentMap,
  PeriodicCardMap & periodicMap);

void printSimulationWaves(
  Expr::Manager::View & v, ThreeValued::vecSeq const & lasso,
  std::vector<ID> const & sv, PersistentCardMap const & pmap,
  PeriodicCardMap const & cmap, bool full = false);

void printReport(
  Options::Verbosity verbosity,
  ThreeValued::vecSeq const & lasso,
  Expr::Manager::View & ev,
  std::vector<ID> const & sv,
  PersistentCardMap const & persistentMap,
  PeriodicCardMap const & periodicMap);

void findImplications(
  Expr::Manager::View & ev,
  std::vector<ID> const & sv,
  std::unordered_set<ID> const & ignore,
  ThreeValued::vecSeq const & lasso,
  implSet & implications,
  std::unordered_map<ID,ID> & equivalences,
  Options::Verbosity verbosity);

void findImplicationsLight(
  Expr::Manager::View & ev,
  std::unordered_set<ID> const & ignore,
  PersistentCardMap const & persistentMap,
  PeriodicCardMap const & periodicMap,
  ThreeValued::vecSeq const & lasso,
  implSet & implications,
  std::unordered_map<ID,ID> & equivalences,
  Options::Verbosity verbosity);

void simplifyModel(
  Model & model,
  Expr::Manager::View & ev,
  std::unordered_set<ID> const & ignore,
  ThreeValued::vecSeq const & lasso,
  PersistentCardMap const & persistentMap,
  PeriodicCardMap const & periodicMap);

/** Simplify constrained TR expressions. 
 *  Use ternary simulation to produce constraints. */
void simplifyTV(
  Expr::Manager::View & ev,
  AIGAttachment const * aat,
  std::vector<ID> const & stateVars,
  std::vector<ID> & nextStateFns,
  std::vector<ID> & outputFns,
  std::vector<ID> const & init,
  std::unordered_map<ID,ID> const & assignments,
  Options::Verbosity verbosity = Options::Silent,
  bool allowWidening = true,
  int * pconclusion = 0,
  unsigned int * pstemLength = 0,
  unsigned int * ploopLength = 0,
  unsigned int * pstabilized = 0,
  unsigned int * pfirstNonzero = 0,
  bool * pwidened = 0);


class TvSimplifierAction : public Model::Action {
public:
  TvSimplifierAction(Model & model) : Model::Action(model) {
    ExprAttachment::Factory expFactory;
    requires(Key::EXPR, &expFactory);
    AIGAttachment::Factory aigFactory;
    requires(Key::AIG, &aigFactory);
    SeqAttachment::Factory seqFactory;
    requires(Key::SEQ, &seqFactory);
    RchAttachment::Factory rchFactory;
    requires(Key::RCH, &rchFactory);
    ProofAttachment::Factory proofFactory;
    requires(Key::PROOF, &proofFactory);
  }
  
  virtual void exec();
private:
  static ActionRegistrar action;
};

#endif // Simplifier_
