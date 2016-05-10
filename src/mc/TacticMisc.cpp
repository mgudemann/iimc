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

#include "TacticMisc.h"
#include "Util.h"

using namespace std;

void AnalyzeSccs::exec() {
  Expr::Manager::View *v = model().newView();
  ExprAttachment const * const eat = 
    (ExprAttachment const *) model().constAttachment(Key::EXPR);
  vector<ID> const &nsfv = eat->nextStateFns();
  vector<ID> const &roots = eat->outputFns();
  vector<ID> const &leaves = eat->stateVars();
  analyzeSccs(*v, roots, leaves, nsfv);
  model().constRelease(eat);
  delete v;
}


void PrintCircuitSccGraph::exec() {
  Expr::Manager::View *v = model().newView();
  ExprAttachment const * const eat = 
    (ExprAttachment const *) model().constAttachment(Key::EXPR);
  vector<ID> const &nsfv = eat->nextStateFns();
  vector<ID> const &roots = eat->outputFns();
  vector<ID> const &leaves = eat->stateVars();
  cout << printSccQuotientGraph(*v, roots, leaves, nsfv);
  model().constRelease(eat);
  delete v;
}


void PrintExprSize::exec() {
  ExprAttachment const * const eat =
    (ExprAttachment const *) model().constAttachment(Key::EXPR);

  vector<ID> ids = eat->nextStateFns();
  ids.insert(ids.end(), eat->outputFns().begin(), eat->outputFns().end());
  ids.insert(ids.end(), eat->badFns().begin(), eat->badFns().end());
  ids.insert(ids.end(), eat->constraintFns().begin(), eat->constraintFns().end());
  for(vector< vector<ID> >::const_iterator it = eat->justiceSets().begin();
      it != eat->justiceSets().end(); ++it) {
    ids.insert(ids.end(), it->begin(), it->end());
  }
  ids.insert(ids.end(), eat->fairnessFns().begin(), eat->fairnessFns().end());

  Expr::Manager::View *v = model().newView();
  cout << "Model has " << sizeOf(*v, ids) << " nodes" << endl;

  delete v;
  model().constRelease(eat);
}


void PrintOutputExpressions::exec() {
  ExprAttachment const * const eat =
    (ExprAttachment const *) model().constAttachment(Key::EXPR);
  vector<ID> outputs = eat->outputs();
  vector<ID> outFns = eat->outputFns();
  Expr::Manager::View *v = model().newView();
  cout << "Outputs:" << endl;
  for (vector<ID>::size_type i = 0; i != outputs.size(); ++i) {
    cout << Expr::stringOf(*v, outputs[i], 1) + " =";
    if (i < outFns.size())
      cout << Expr::stringOf(*v, outFns[i], 1);
    else
      cout << " undefined";
    cout << endl;
  }
  delete v;
  model().constRelease(eat);
}


void PrintStateGraph::exec() {
  ExprAttachment const * const eat =
    (ExprAttachment const *) model().constAttachment(Key::EXPR);
  const vector<ID> & stateVars = eat->stateVars();
  if (stateVars.size() > 10) {
    model().constRelease(eat);
    cout << "PrintStateGraph: Sorry, cannot handle models with more than 10 state variables" << endl;
    return;
  }
  Expr::Manager::View *v = model().newView();

  cout << "strict digraph \"" << model().name() << "\" {" << endl
       << "rankdir=LR;" << endl
       << "ordering=out;" << endl
       << "{ rank=source;" << endl
       << "invisible [style=invisible];" << endl
       << "}" << endl;
  vector<ID> init = eat->initialConditions();
  ID initCube = v->apply(Expr::And, init);
  ID bad = eat->outputFns()[0];
  const vector<ID> & nextStateFns = eat->nextStateFns();
  const vector<ID> & inputs = eat->inputs();
  uint64_t numStates = pow(2, stateVars.size());
  uint64_t numInputCombs = pow(2, inputs.size());
  vector<Expr::IDMap> states(numStates);
  vector<Expr::IDMap> inputCombs(numInputCombs);
  for (uint64_t inputComb = 0; inputComb < numInputCombs; ++inputComb) {
    boost::dynamic_bitset<> in(inputs.size(), inputComb);
    for (unsigned i = 0; i < in.size(); ++i) {
      inputCombs[inputComb].insert(Expr::IDMap::value_type(inputs[i], in[i] == 0 ? v->bfalse() : v->btrue()));
    }
  }
  for (uint64_t state = 0; state < numStates; ++state) {
    boost::dynamic_bitset<> s(stateVars.size(), state);
    for (unsigned i = 0; i < s.size(); ++i) {
      states[state].insert(Expr::IDMap::value_type(stateVars[i], s[i] == 0 ? v->bfalse() : v->btrue()));
    }
  }
 
  bool printedBad = false;
  for (uint64_t state = 0; state < numStates; ++state) {
    boost::dynamic_bitset<> s(stateVars.size(), state);
    ID sub = varSub(*v, states[state], initCube);
    assert(sub == v->bfalse() || sub == v->btrue());
    bool isInitial = (sub == v->btrue());
    sub = varSub(*v, states[state], bad);
    bool isBad = false;
    if (sub != v->bfalse() && sub != v->btrue()) {
      //output depends on inputs
      for (vector<Expr::IDMap>::const_iterator it = inputCombs.begin(); it != inputCombs.end(); ++it) {
        ID subsub = varSub(*v, *it, sub);
        assert (subsub == v->bfalse() || subsub == v->btrue());
        if (subsub == v->btrue()) {
          isBad = true;
          break;
        }
      }
    }
    else {
      isBad = (sub == v->btrue());
    }
    if (isInitial && isBad) {
      cout << state << " [label = " << s << ",style=filled,color=yellow];" << endl;
    }
    else if (isInitial) {
      cout << "{rank=source;" << endl
           << state << " [label = " << s << ",style=filled,color=lightblue];" << endl
           << "}" << endl;
      cout << "invisible -> " << state << ";" << endl;
    }
    else if (isBad && !printedBad) {
      printedBad = true;
      cout << "{rank=sink;" << endl
           << "bad [label = bad,style=filled,color=tomato];"
           << "}" << endl;
    }
    else if (!isBad) {
      cout << state << " [label = " << s << "];" << endl;
    }

    vector<ID> nsfs(nextStateFns);
    varSub(*v, states[state], nsfs);
    for (vector<Expr::IDMap>::const_iterator it = inputCombs.begin(); it != inputCombs.end(); ++it) {
      vector<ID> nsfsTmp(nsfs);
      varSub(*v, *it, nsfsTmp);
      boost::dynamic_bitset<> ns;
      for (vector<ID>::const_iterator it2 = nsfsTmp.begin(); it2 != nsfsTmp.end(); ++it2) {
        assert(*it2 == v->btrue() || *it2 == v->bfalse());
        ns.push_back(*it2 == v->bfalse() ? 0 : 1);
      }
      unsigned nextState = ns.to_ulong();
      //Check if the next state is a bad one
      bool nsBad = false;
      ID sub = varSub(*v, states[nextState], bad);
      if (sub != v->bfalse() && sub != v->btrue()) {
        //output depends on input
        for (vector<Expr::IDMap>::const_iterator it2 = inputCombs.begin(); it2 != inputCombs.end(); ++it2) {
          ID subsub = varSub(*v, *it2, sub);
          assert (subsub == v->bfalse() || subsub == v->btrue());
          if (subsub == v->btrue()) {
            nsBad = true;
            break;
          }
        }
      }
      else {
        nsBad = (sub == v->btrue());
      }
      if (!isBad || isInitial) {
        if (nsBad)
          cout << state << " -> bad;" << endl;
        else
          cout << state << " -> " << nextState << ";" << endl;
      }
    }
  }
  cout << "}" << endl;
  delete v;
  model().constRelease(eat);
}
