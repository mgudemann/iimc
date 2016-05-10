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

#ifndef _IICTL_
#define _IICTL_

/** @file IICTL.h **/

#include "BddAttachment.h"
#include "CNFAttachment.h"
#include "COI.h"
#include "ExprAttachment.h"
#include "Fair.h"
#include "IC3.h"
#include "MC.h"
#include "Model.h"
#include "options.h"
#include "ProofAttachment.h"
#include "RchAttachment.h"

#include <ostream>
#include <boost/program_options.hpp>

/** namespace of IICTL */
namespace IICTL {

enum RefineType {None,
                 Upper, 
                 Lower,
                 Both
                };

enum BoundChange {NoSkip,       //Do not skip generalization
                  SkipForUpper, //Skip generalization for updates of upper bound
                  SkipForLower, //Skip generalization for updates of lower bound
                  SkipForBoth   //Skip generalization for updates of either bound
                 };

inline bool _IDVectorComp(const std::vector<ID> & v1,
                          const std::vector<ID> & v2) {
  std::vector<ID>::const_iterator it1 = v1.begin(), it2 = v2.begin();
  for (; it1 != v1.end() && it2 != v2.end(); ++it1, ++it2) {
    if (*it1 < *it2) return true;
    if (*it1 > *it2) return false;
  }
  return (it1 == v1.end() && it2 != v2.end());
}

class IDVectorComp {
public:
  bool operator()(const std::vector<ID> & v1, const std::vector<ID> & v2) {
    return _IDVectorComp(v1, v2);
  }
};

typedef std::unordered_map<ID, ID> IDMap;
typedef std::unordered_map<ID, std::vector< std::vector<ID> > > IDClausesMap;
typedef std::unordered_map<ID, std::vector< std::vector<ID> > > IDCubesMap;
typedef std::unordered_map<ID, bool> IDBoolMap;
typedef std::unordered_map<ID, SAT::Manager::View * > IDSatViewMap;
typedef std::unordered_map<ID, int> IDIntMap;


struct IICTLOptions {
public:
  IICTLOptions(const boost::program_options::variables_map & opts) : 
    ic3_opts(opts), reach_opts(opts), fair_opts(opts) {
      ic3_opts.lift = false;
      reach_opts.lift = false;
  }
  IC3::IC3Options ic3_opts;
  IC3::IC3Options reach_opts;
  Fair::FairOptions fair_opts;
};

class LabelInitFolder;

class IICTLAction : public Model::Action {
public:
  friend class LabelInitFolder;
  IICTLAction(Model & m) : Model::Action(m), _opts(NULL),
      isDescendantOf(descendants), ic3Factor(20), bmcFactor(10) {
    ExprAttachment::Factory eaf;
    requires(Key::EXPR, &eaf);
    ProofAttachment::Factory paf;
    requires(Key::PROOF, &paf);
    CNFAttachment::Factory cnfaf;
    requires(Key::CNF, &cnfaf);
    COIAttachment::Factory caf;
    requires(Key::COI, &caf);
    RchAttachment::Factory raf;
    requires(Key::RCH, &raf);
    if(m.options().count("iictl_count_reach")) {
      BddAttachment::Factory baf;
      requires(Key::BDD, &baf);
    }
    numIC3calls = 0;
    fairnessConstraints = false;
    multiInit = false;
    haveExactRch = false;
  }

  ~IICTLAction();

  virtual void exec();

  void init();

  //Check if model satisfies property
  MC::ReturnValue check();

  void addCubeToManager(std::vector<ID> & cube, ID id);
  bool addCubeToCubes(std::vector<ID> & cube, ID id);
  void addCube(std::vector<ID> & cube, ID id);

  void grabProperty();
  void translateProperty();
  ID translateProperty(ID subFormula, IDMap & visited);

  void initializeLabels();

  bool liftEF(Transition & tr1, ID id, ID aaRep, SAT::GID gid, bool addUnprimed);
  bool liftEX(Transition & tr1, ID id);
  bool bruteForceLiftEF(Transition & tr1, ID id, ID aaRep, SAT::GID gid, bool addUnprimed);
  bool bruteForceLiftEX(Transition & tr1, ID id);
  bool forAllExistsEF(Transition & tr1, SAT::Clauses & q2clauses, ID id, ID aaRep, SAT::GID gid, ID tmpQLB, const SAT::Clauses & ubPrimed, bool reach, bool ic3);
  bool forAllExistsEG(Transition & tr1, SAT::Clauses & q2clauses, ID id, ID aaRep, SAT::GID gid, SAT::Manager::View * q2, ID tmpQLB, const SAT::Clauses & ubPrimed, bool reach, bool ic3);
  bool forAllExistsEX(Transition & tr1, ID id, bool reach, bool ic3);
  void renewQLB(ID id);
  ID disjoinCube(ID id, const std::vector<ID> & cube);
  ID disjoinCubes(ID id, const std::vector< std::vector<ID> > & cubes);
  void generalizeTwoStateTrace(std::vector<Transition> & cex, ID id, ID child);
  void generalizeEFTrace(std::vector<Transition> & cex, ID id);
  void generalizeEUTrace(std::vector<Transition> & cex, ID id, ID child);
  void generalizeLasso(Lasso & lasso, ID id, ID child);
  MC::ReturnValue runIC3(IC3::IC3Options & opts, ID targetID,
                         std::vector<Transition> & cex,
                         std::vector<SAT::Clauses> & proofs,
                         bool incremental, bool propagate);
  bool fair(const std::vector<ID> & source, SAT::Clauses & constraints, SAT::Clauses & negConstraints,
            IC3::ProofProcType grppt, bool globalLast,
            std::vector<SAT::Clauses> & proofs, Lasso & cex, ID id);
  bool reach(const std::vector<ID> & source, ID targetID,
             SAT::Clauses & targetCNF, std::vector<SAT::Clauses> & constraints, SAT::Clauses & negConstraints,
             IC3::ProofProcType ppt, std::vector<SAT::Clauses> & proofs,
             std::vector<Transition> & cex, ID id, bool isEU = false);
  bool isUndecided(const std::vector<ID> & state, ID id);

  bool lbContainsStates(ID id, const std::vector<ID> & state, std::vector<ID> * witness = NULL);
  bool ubContainsStates(ID id, const std::vector<ID> & state);
  bool lbContainsInitStates(std::vector<ID> & state);
  bool ubContainsInitStates();

  void subsumption(std::vector< std::vector<ID> > & cubes);

  bool equivalent(ID id1, ID id2);
  RefineType update(ID id, RefineType childRefinement);
  bool updateAncestorsBounds(ID id, RefineType refinement);
  bool decide(const std::vector<ID> & state, ID id, BoundChange skipGen);

  void countPRStates();

private:

  static ActionRegistrar action;

  class IsDescendantOf {
  public: 
    IsDescendantOf(Expr::IDSetMap & _descendants) : descendants(_descendants) {}
    bool operator()(const ID id1, const ID id2) const {
      assert(descendants.find(id1) != descendants.end());
      if(descendants[id1].find(id2) != descendants[id1].end())
        return false;
      assert(descendants.find(id2) != descendants.end());
      if(descendants[id2].find(id1) != descendants[id2].end())
        return true;
      return (id1 < id2);
    }
  private:
    Expr::IDSetMap & descendants;
  };

  typedef std::map<ID, RefineType, IsDescendantOf> ToUpdate;

  IICTLOptions * _opts;
  ID property;
  Expr::Manager::View * ev;

  //Upper bound on set of states satisfying a node in the CTL formula parse
  //graph represented by a set of clauses
  IDClausesMap UB;
  IDMap UBId;

  //QLB (quasi-lower bound) is a formula represented by a set of clauses, which
  //when conjoined with the upper bound and the set of potentially reachable
  //states, denotes a lower bound on set of states satisfying a node in the CTL
  //formula parse graph
  IDClausesMap QLB;
  IDMap QLBId;

  //Indicates if upper and lower bounds are the same. This is only determined
  //during initialization
  IDBoolMap boundsEqual;

  IDMap baseQLB;
  IDCubesMap QLBcubes;

  bool fairnessConstraints; //Model has fairness constraints
  bool multiInit;

  //Global reachability information (states not known to be unreachable)
  SAT::Clauses GR;

  std::vector<ID> initialConditions;

  SAT::Assignment stateAsgn;       //Latch values
  SAT::Assignment primedStateAsgn; //Primed latch values
  SAT::Assignment fullAsgn;        //Values of latches and inputs

  SAT::Clauses tr;

  IDSatViewMap liftSatViews;
  
  SAT::Manager::View * faeSatView;

  int numIC3calls;

  std::vector<IC3::CubeSet> cubes;
  std::vector<IC3::LevClauses> propClauses;

  IC3::CubeSet ctgs;

  Options::Verbosity verbosity;
  Expr::IDMMap parents;

  Expr::IDSetMap descendants;
  IsDescendantOf isDescendantOf;

  IDIntMap ic3Fail;
  IDIntMap bmcFail;

  const int ic3Factor;
  const int bmcFactor;

  bool haveExactRch;

};

}

#endif
