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

#include "COI.h"
#include "ExprUtil.h"

#include <algorithm>
#include <ostream>
#include <vector>

using namespace std;

// TODO: make less conservative?

void COI::build(Expr::Manager::View & v, const IDpv & rltn, ID prop, Options::Verbosity vrb) {
  if (vrb > Options::Terse)
    cout << "Building k-step COI" << endl;

  // 0. Construct set of latches.
  set<ID> latches;
  for (IDpv::const_iterator it = rltn.begin(); it != rltn.end(); ++it)
    latches.insert(it->first);

  // 1. Construct map of latches to fan-in latches.
  typedef unordered_map<ID, set<ID> > VMap;
  VMap vmap;
  for (IDpv::const_iterator it = rltn.begin(); it != rltn.end(); ++it) {
    set<ID> all_vars, vars;
    Expr::variables(v, it->second, all_vars);
    set_intersection(latches.begin(), latches.end(), all_vars.begin(), all_vars.end(), inserter(vars, vars.end()));
    vmap.insert(VMap::value_type(it->first, vars));
  }

  // 2. Construct 0-COI.
  set<ID> all_init, init;
  Expr::variables(v, prop, all_init);
  set_intersection(latches.begin(), latches.end(), all_init.begin(), all_init.end(), inserter(init, init.end()));
  _kCOI.push_back(init);

  // 3. Iterate until convergence.
  set<ID> delta = _kCOI.back();
  for (;;) {
    const set<ID> & prev = _kCOI.back();
    if (vrb > Options::Informative) cout << " " << prev.size() << endl;
    set<ID> curr;
    for (set<ID>::const_iterator it = delta.begin(); it != delta.end(); ++it) {
      VMap::const_iterator vit = vmap.find(*it);
      set_union(curr.begin(), curr.end(), vit->second.begin(), vit->second.end(), inserter(curr, curr.end()));
    }
    delta.clear();
    set_difference(curr.begin(), curr.end(), prev.begin(), prev.end(), inserter(delta, delta.end()));
    set_union(curr.begin(), curr.end(), prev.begin(), prev.end(), inserter(curr, curr.end()));
    if (curr.size() == prev.size())
      return;
    _kCOI.push_back(curr);
  }
}

void COIAction::exec() {
  COIAttachment * const cat = (COIAttachment *) model().constAttachment(Key::COI);
  SeqAttachment * seqat = (SeqAttachment *) model().attachment(Key::SEQ);
  ExprAttachment * const eat = (ExprAttachment *) model().attachment(Key::EXPR);

  vector<ID> latches, nsfs;
  set<ID> coil = cat->coi().cCOI();
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
      set_intersection(vars.begin(), vars.end(), coil.begin(), coil.end(), inserter(inter, inter.end()));
      if (inter.size() > 0)
        eat->addInitialCondition(*it);
    }

    nsfs.insert(nsfs.end(), eat->outputFns().begin(), eat->outputFns().end());
    nsfs.insert(nsfs.end(), eat->constraints().begin(), eat->constraints().end());
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
  vector<ID> latches(eat->stateVars());
  vector<ID> nsfs(eat->nextStateFnOf(latches));

  Expr::Manager::View * v = model().newView();

  vector<ID> props;
  vector<ID> constraints = eat->constraints();
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
  // conjoin w/o simplifying to get one big expression
  ID all_props = v->apply(Expr::And, props, false);
  COI::IDpv rltn;
  for (vector<ID>::const_iterator it1 = latches.begin(), it2 = nsfs.begin(); 
       it1 != latches.end(); 
       ++it1, ++it2)
    rltn.push_back(COI::IDp(*it1, *it2));
  COI coi(*v, rltn, all_props, model().verbosity());
  _coi = coi;

  delete v;
  model().constRelease(eat);
}
