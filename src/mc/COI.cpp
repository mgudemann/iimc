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

#include "COI.h"
#include "ExprUtil.h"

#include <algorithm>
#include <ostream>
#include <vector>

using namespace std;

// TODO: make less conservative?

void COI::build(Expr::Manager::View & v, ExprAttachment * const eat,
                vector<ID> props, bool internal, Options::Verbosity vrb) {

  if (vrb > Options::Terse)
    cout << "Building k-step COI" << endl;

  kCOI_.clear();
  kCOIplusInt_.clear();
  markers_.clear();
  markersInt_.clear();

  // 1. Construct 0-COI.
  set<ID> latchSet;
  eat->supportStateVars(v, props, latchSet);
  copy(latchSet.begin(), latchSet.end(), back_inserter(kCOI_));
  markers_.push_back(kCOI_.size());

  set<ID> nodeSet; // latches and internal nodes (somewhat redundant)
  if (internal){
    eat->supportNodes(v, props, nodeSet);
    copy(nodeSet.begin(), nodeSet.end(), back_inserter(kCOIplusInt_));
    markersInt_.push_back(kCOIplusInt_.size());
  }

  // 2. Iterate until convergence.
  vector<ID> delta(latchSet.begin(), latchSet.end());
  while (delta.size() > 0) {
    vector<ID> nsfs = eat->nextStateFnOf(delta);
    set<ID> newLatches;
    eat->supportStateVars(v, nsfs, newLatches);
    delta.clear();
    for (set<ID>::const_iterator it = newLatches.begin(); it != newLatches.end(); ++it) {
      if (latchSet.find(*it) == latchSet.end()) {
        delta.push_back(*it);
      }
    }
    copy(delta.begin(), delta.end(), inserter(latchSet, latchSet.end()));
    copy(delta.begin(), delta.end(), back_inserter(kCOI_));
    markers_.push_back(kCOI_.size());

    set<ID> newNodes;
    vector<ID> delta2;
    if (internal){
      eat->supportNodes(v, nsfs, newNodes);
      for (set<ID>::const_iterator it = newNodes.begin(); it != newNodes.end(); ++it) {
	if (nodeSet.find(*it) == nodeSet.end()) {
	  delta2.push_back(*it);
	}
      }
      copy(delta2.begin(), delta2.end(), inserter(nodeSet, nodeSet.end()));
      copy(delta2.begin(), delta2.end(), back_inserter(kCOIplusInt_));
      markersInt_.push_back(kCOIplusInt_.size());
    }
  }
}


void COIAction::exec() {
  COIAttachment * const cat = (COIAttachment *) model().constAttachment(Key::COI);
  SeqAttachment * seqat = (SeqAttachment *) model().attachment(Key::SEQ);
  ExprAttachment * const eat = (ExprAttachment *) model().attachment(Key::EXPR);

  vector<ID> latches, nsfs;
  COI::range coirng = cat->coi().cCOI();
  set<ID> coil(coirng.first,coirng.second);
  bool changed = false;
  int initLatches = eat->stateVars().size();
  if (model().verbosity() > Options::Silent)
    cout << "COI: Initial # latches = " << initLatches << endl;
  for (vector<ID>::const_iterator it = eat->stateVars().begin(); it != eat->stateVars().end(); ++it)
    if (coil.find(*it) != coil.end()) {
      latches.push_back(*it);
      nsfs.push_back(eat->nextStateFnOf(*it));
    }
    else  {
      changed = true;
      seqat->optimized.insert(unordered_map<ID, ID>::value_type(*it, *it));
    }

  model().constRelease(cat);
  model().constRelease(eat);

  if (changed) {
    ExprAttachment * eat = (ExprAttachment *) model().attachment(Key::EXPR);
    if(seqat->stateVars.empty()) {
      seqat->stateVars = eat->stateVars();
      seqat->nextStateFns = eat->nextStateFns();
    }
    eat->clearNextStateFns();
    eat->setNextStateFns(latches, nsfs);

    Expr::Manager::View * ev = model().newView();
    vector<ID> init(eat->initialConditions());
    if(seqat->initialConditions.empty())
      seqat->initialConditions = init;
    eat->clearInitialConditions();
    for (vector<ID>::const_iterator it = init.begin(); it != init.end(); ++it) {
      set<ID> vars, inter;
      Expr::variables(*ev, *it, vars);
      for (set<ID>::const_iterator vit = vars.begin(); vit != vars.end(); ++vit) {
        if (coil.find(*vit) != coil.end()) {
          eat->addInitialCondition(*it);
          break;
        }
      }
    }

    nsfs.insert(nsfs.end(), eat->outputFns().begin(), eat->outputFns().end());
    nsfs.insert(nsfs.end(), eat->constraintFns().begin(), eat->constraintFns().end());
    nsfs.insert(nsfs.end(), eat->badFns().begin(), eat->badFns().end());
    nsfs.insert(nsfs.end(), eat->fairnessFns().begin(), eat->fairnessFns().end());
    for (size_t i = 0; i < eat->justiceSets().size(); ++i) {
      nsfs.insert(nsfs.end(), eat->justiceSets()[i].begin(), 
          eat->justiceSets()[i].end());
    }

    set<ID> vars;
    Expr::variables(*ev, nsfs, vars);
    vector<ID> inputs(eat->inputs());
    if(seqat->inputs.empty())
      seqat->inputs = inputs;
    eat->clearInputs();
    for (vector<ID>::const_iterator it = inputs.begin(); it != inputs.end(); ++it)
      if (vars.find(*it) != vars.end())
        eat->addInput(*it);

    if (model().verbosity() > Options::Silent)
      cout << "COI: Final # latches = " << eat->stateVars().size() << endl;
    model().release(eat);
    delete ev;

    COIAttachment * cat = (COIAttachment *) model().attachment(Key::COI);
    cat->updateTimestamp();
    model().release(cat);
  }
  else {
    if (model().verbosity() > Options::Silent)
      cout << "COI: Final # latches = " << initLatches << endl;
  }
  model().release(seqat);
}

void COIAttachment::build() {
  if (model().verbosity() > Options::Silent)
    cout << "COIAttachment: building" << endl;

  // If we read CTL properties, the attachment is modified.
  ExprAttachment * const eat = (ExprAttachment *) model().constAttachment(Key::EXPR);
  Expr::Manager::View * v = model().newView();

  vector<ID> props;
  vector<ID> constraints = eat->constraintFns();
  vector<ID> bad = eat->badFns();
  vector<ID> fairness = eat->fairnessFns();
  vector< vector<ID> > justice = eat->justiceSets();
  vector<ID> ctlprops = eat->ctlProperties();
  props = eat->outputFns();
  props.insert(props.end(), constraints.begin(), constraints.end()); // conservative
  props.insert(props.end(), bad.begin(), bad.end());
  props.insert(props.end(), fairness.begin(), fairness.end());
  props.insert(props.end(), ctlprops.begin(), ctlprops.end());
  for (size_t i = 0; i < justice.size(); ++i)
    props.insert(props.end(), justice[i].begin(), justice[i].end());
  _coi.build(*v, eat, props, model().options().count("ic3_intNodes"), model().verbosity());

  delete v;
  model().constRelease(eat);
}
