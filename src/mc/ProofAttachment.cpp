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
#include "CNFAttachment.h"
#include "ProofAttachment.h"
#include "SeqAttachment.h"
#include "Util.h"

using namespace std;
/**
 * Make string out of attachment.
 */
std::string ProofAttachment::string(bool includeDetails) const {
  if (includeDetails) {
    std::ostringstream ret;
    ret << "PROOF (Timestamp = " << _ts << "):\n";
    if (_hasConclusion)
      ret << (_safe == 0 ? "Safe" : "Counterexample") << std::endl;
    else
      ret << "No conlusion yet" << std::endl;
    return ret.str();
  } else {
    return "PROOF";
  }
}

/**
 * Print conclusion (or nothing).
 */
void ProofAttachment::printConclusion(std::ostream& os) const
{
  bool printInfo = _model.options().count("print_info") > 0;
  if (printInfo)
    Util::printSystemInfo(os);
  if (_hasConclusion)
    os << _safe << std::endl;
  else
    os << "2" << std::endl;
}

void ProofAttachment::restoreDroppedLatches() {

  if(model().options().count("xmap_cex"))
    return;

  //Currently only works for AIGER 1.0
  
  Expr::Manager::View * ev = model().newView();

  SeqAttachment const * seqat = (SeqAttachment *) model().constAttachment(Key::SEQ);
  set<ID> init;
  unordered_map<ID, ID> missingLatches;
  vector< vector<ID> > tr;
  vector<ID> inputs;
  if(seqat) {
    init.insert(seqat->initialConditions.begin(), seqat->initialConditions.end());
    missingLatches = seqat->optimized;
    vector<ID> trans;
    const vector<ID> & latches = seqat->stateVars;
    const vector<ID> & nsf = seqat->nextStateFns;
    for(unsigned i = 0; i < latches.size(); ++i) {
      trans.push_back(ev->apply(Expr::Equiv,
                                ev->prime(latches[i]),
                                nsf[i]));
    }
    Expr::tseitin(*ev, trans, tr);

    inputs = seqat->inputs;

    model().constRelease(seqat);
  }
  else { //No sequential optimization methods have been applied
    //Therefore, get the initial conditions and set of latches from ExprAttachment
    ExprAttachment const * eat = (ExprAttachment *)
        model().constAttachment(Key::EXPR);
    init.insert(eat->initialConditions().begin(), eat->initialConditions().end());
    set<ID> latches(eat->stateVars().begin(), eat->stateVars().end());
    vector<ID> trans;
    for(vector<ID>::const_iterator it = eat->stateVars().begin();
        it != eat->stateVars().end(); ++it) {
      trans.push_back(ev->apply(Expr::Equiv,
                                ev->prime(*it),
                                eat->nextStateFnOf(*it)));
    }
    Expr::tseitin(*ev, trans, tr);
    inputs = eat->inputs();
    model().constRelease(eat);
    //Although no sequential optimization methods have been applied, engines
    //such as IC3 and BMC use only the set of latches in COI. Must therefore
    //lift the counterexamples from them to the full set of latches of the
    //original model
    COIAttachment const * coiat = (COIAttachment *) model().constAttachment(Key::COI);
    if(coiat) {
      set<ID> coi = coiat->coi().cCOI();
      model().constRelease(coiat);
      //Missing latches is the difference
      set<ID> diff;
      set_difference(latches.begin(), latches.end(), coi.begin(), coi.end(),
          inserter(diff, diff.end()));
      for(set<ID>::iterator it = diff.begin(); it != diff.end(); ++it) {
        missingLatches.insert(unordered_map<ID, ID>::value_type(*it, *it));
      }
    }
  }


  vector<Transition>::iterator cexIt = _cex.begin();

  for(unordered_map<ID, ID>::const_iterator latchIt = missingLatches.begin();
      latchIt != missingLatches.end(); ++latchIt) {
    //Dropped latches must obey initial conditions
    if(init.find(latchIt->first) != init.end()) {
      cexIt->state.push_back(latchIt->first);
    }
    else if(init.find(ev->apply(Expr::Not, latchIt->first)) != init.end()) {
      cexIt->state.push_back(ev->apply(Expr::Not, latchIt->first));
    }
  }
  ev->sort(cexIt->state.begin(), cexIt->state.end());

  /*
  if(seqat && cexIt + 1 != _cex.end()) {
    //Restore inputs
    cexIt->inputs.clear();
    SAT::Manager * sman = model().newSATManager();
    SAT::Manager::View * sview = sman->newView(*ev);
    sview->add(tr);
    vector<ID> assumps = cexIt->state;
    vector<Transition>::iterator nextState = cexIt + 1;
    for(vector<ID>::const_iterator it = nextState->state.begin();
        it != nextState->state.end(); ++it) {
      assumps.push_back(ev->prime(*it));
    }
    SAT::Assignment  asgn;
    for(vector<ID>::const_iterator it = inputs.begin();
        it != inputs.end(); ++it) {
      asgn.insert(SAT::Assignment::value_type(*it, SAT::Unknown));
    }
    bool sat = sview->sat(&assumps, &asgn);
    assert(sat);
    for(SAT::Assignment::const_iterator it = asgn.begin(); it != asgn.end();
        ++it) {
      assert(it->second != SAT::Unknown);
      if(it->second == SAT::True) {
        cexIt->inputs.push_back(it->first);
      }
      else {
        cexIt->inputs.push_back(ev->apply(Expr::Not, it->first));
      }
    }
  }
  */
 
  for(++cexIt; cexIt != _cex.end(); ++cexIt) {
    SAT::Assignment asgn;
    for(unordered_map<ID, ID>::const_iterator latchIt = missingLatches.begin();
           latchIt != missingLatches.end(); ++latchIt) {
      if(latchIt->second == ev->btrue()) {
        cexIt->state.push_back(latchIt->first);
      }
      else if(latchIt->second == ev->bfalse()) {
        cexIt->state.push_back(ev->apply(Expr::Not, latchIt->first));
      }
      else if(latchIt->second != latchIt->first) {
        //Equivalent to another latch
        unordered_map<ID, ID>::const_iterator equivLatch =
            missingLatches.find(latchIt->second);
        //if it's not a missing latch
        if(equivLatch == missingLatches.end()) {
          //The missing latch's value should be the same as that it's
          //equivalent to
          set<ID> state(cexIt->state.begin(), cexIt->state.end());
          if(state.find(latchIt->second) != state.end()) {
            cexIt->state.push_back(latchIt->first);
          }
          else {
            assert(state.find(ev->apply(Expr::Not, latchIt->second)) !=
                state.end());
            cexIt->state.push_back(ev->apply(Expr::Not, latchIt->first));
          }
        }
        else {
          //It is equivalent to a missing latch
          assert(false);
        }
      }
      else {
        //Latch is not in COI. Need to find its value through a SAT query
        asgn.insert(SAT::Assignment::value_type(
            ev->prime(latchIt->first), SAT::Unknown));
      }
    }
    if(!asgn.empty()) {
      SAT::Manager * sman = model().newSATManager();
      SAT::Manager::View * sview = sman->newView(*ev);
      sview->add(tr);
      vector<Transition>::iterator prevState = cexIt - 1;
      vector<ID> assumps = prevState->state;
      assumps.insert(assumps.end(), prevState->inputs.begin(),
          prevState->inputs.end());
      for(vector<ID>::const_iterator it = cexIt->state.begin();
          it != cexIt->state.end(); ++it) {
        assumps.push_back(ev->prime(*it));
      }
      bool sat = sview->sat(&assumps, &asgn);
      assert(sat);
      for(SAT::Assignment::iterator it = asgn.begin(); it != asgn.end();
          ++it) {
        assert(it->second != SAT::Unknown);
        if(it->second == SAT::True) {
          cexIt->state.push_back(ev->unprime(it->first));
        }
        else {
          cexIt->state.push_back(ev->apply(Expr::Not, ev->unprime(it->first)));
        }
      }
      delete sview;
      delete sman;
    }
    ev->sort(cexIt->state.begin(), cexIt->state.end());
  }

  delete ev;

}

void ProofAttachment::addEquivalenceInfo() {

  if(model().options().count("xmap_cex"))
    return;

  SeqAttachment const * seqat = (SeqAttachment *) model().constAttachment(Key::SEQ);
  if(!seqat)
    return;

  Expr::Manager::View * ev = model().newView();

  const unordered_map<ID, ID> & optLatches = seqat->optimized;

  for(unordered_map<ID, ID>::const_iterator it = optLatches.begin();
      it != optLatches.end(); ++it) {
    if(it->second == ev->btrue()) {
      _proof.push_back(vector<ID>(1, it->first));
    }
    else if(it->second == ev->bfalse()) {
      _proof.push_back(vector<ID>(1, ev->apply(Expr::Not, it->first)));
    }
    else if(it->second != it->first) {
      //equivalent to another latch
      vector<ID> clause1, clause2;
      clause1.push_back(it->first);
      clause1.push_back(ev->apply(Expr::Not, it->second));
      _proof.push_back(clause1);
      clause2.push_back(ev->apply(Expr::Not, it->first));
      clause2.push_back(it->second);
      _proof.push_back(clause2);
    }
  }

  delete ev;
  model().constRelease(seqat);



}

void ProofAttachment::printCex(std::ostream& os) const
{
  assert(_hasConclusion && _safe == 1);
  Expr::Manager::View * v = _model.newView();

  os << std::endl << "Counterexample Trace:" << std::endl;
  for(unsigned i = 0; i < _cex.size(); ++i) {
    os << "State " << i << ":" << std::endl;
    if(!_cex[i].state.empty()) {
      os << stringOf(*v, _cex[i].state[0]);
      for(unsigned j = 1; j < _cex[i].state.size(); ++j) {
        os << " & " << stringOf(*v, _cex[i].state[j]);
      }
      os << std::endl;
    }
    os << "Inputs: " << std::endl;
    if(!_cex[i].inputs.empty()) {
      os << stringOf(*v, _cex[i].inputs[0]);
      for(unsigned j = 1; j < _cex[i].inputs.size(); ++j) {
        os << " & " << stringOf(*v, _cex[i].inputs[j]);
      }
      os << std::endl;
    }
    os << std::endl;
  }
  delete v;
}

void ProofAttachment::printProof(std::ostream& os) const
{
  assert(_hasConclusion && _safe == 0);
  Expr::Manager::View * v = _model.newView();

  os << std::endl << "One-step Inductive Strengthening of Property (in CNF):"
     << std::endl;
  for(unsigned i = 0; i < _proof.size(); ++i) {
    os << "Clause " << i << ": ";
    for(unsigned j = 0; j < _proof[i].size(); ++j) {
      os << stringOf(*v, _proof[i][j]) << " ";
    }
    os << std::endl;
  }
  delete v;
}
