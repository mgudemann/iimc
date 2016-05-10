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

#include "COI.h"
#include "CNFAttachment.h"
#include "ProofAttachment.h"
#include "SeqAttachment.h"
#include "Util.h"
#include <boost/regex.hpp>
#include <iostream>
#include <fstream>
#include <string>

using namespace std;

namespace {
  struct nameCompare {
    nameCompare(Expr::Manager::View *v) : v(v) {}
    bool operator ()(ID const a, ID const b) const {
      std::string aString = stringOf(*v, a);
      std::string bString = stringOf(*v, b);
      std::string aName, bName;
      boost::smatch m;

      if (aString[0] == '!')  aString = aString.substr(1);
      if (bString[0] == '!')  bString = bString.substr(1);

      bool aIsPred = !std::strncmp(aString.c_str(), "p_xx", 2);
      bool bIsPred = !std::strncmp(bString.c_str(), "p_xx", 2);
      // put the predicates at the end (they are also poorly sorted)
      if (aIsPred && bIsPred){
	// strip off predicate prefix and continue
	aString = aString.substr(2);
	bString = bString.substr(2);
      }
      else if (aIsPred)
	return false;
      else if (bIsPred)
	return true;

      // get name in !name<3> or name<*2*>
      boost::regex getName ("(.*?)(<\\*?\\d\\*?>)");
      boost::regex_search(aString, m, getName);
      aName = m[1].str();
      boost::regex_search(bString, m, getName);
      bName = m[1].str();
      if (aName != bName)
	return aName < bName;

      // only support single multi-dimensional Ex:  reg [3:0] X [2:0];
      boost::regex getBit ("<(\\d*?)>"); // find 3 in ...<3>...
      boost::regex getWidth ("<\\*(\\d*?)\\*>"); // find 3 in ...<*3*>...
      int bvalA = boost::regex_search(aString, m, getBit) ? 
		       atoi(m[1].str().c_str()) : -1;
      int wvalA = boost::regex_search(aString, m, getWidth) ? 
		       atoi(m[1].str().c_str()) : -1;
      int bvalB = boost::regex_search(bString, m, getBit) ? 
		       atoi(m[1].str().c_str()) : -1;
      int wvalB = boost::regex_search(bString, m, getWidth) ? 
		       atoi(m[1].str().c_str()) : -1;

      if (wvalA != wvalB)
	return wvalA < wvalB;
      else
	return bvalA < bvalB;
    }
  private:
    Expr::Manager::View *v;
  };
}

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
  std::ostringstream oss;
  if (_hasConclusion)
    oss << _safe << std::endl;
  else
    oss << "2" << std::endl;
  os << oss.str() << flush;
}

void ProofAttachment::restoreInitialCondition() {
  ExprAttachment const * const eat = (ExprAttachment const *)
    model().constAttachment(Key::EXPR);

  vector<ID> initialConditions = eat->originalInitialConditions();
  vector<ID> stateVars = eat->originalStateVars();
  model().constRelease(eat);
  unordered_set<ID> hasValue(_cex.front().state.begin(), _cex.front().state.end());
  for (vector<ID>::const_iterator it = initialConditions.begin();
       it != initialConditions.end(); ++it) {
    if (hasValue.find(*it) == hasValue.end())
      _cex.front().state.push_back(*it);
  }

  if (_cex.front().state.size() < stateVars.size())
    if (model().verbosity() > Options::Informative)
      cout << "c Warning: Uninitialized latches were dropped by optimization"
           << endl;

}

/**
 * If this function is called, the model has been decoded.
 * The objective is to undo the effect of optimizations subsequent to
 * decoding (we assume that no optimizations took place before that)
 * and produce a valid counterexample for the unoptimized, still decoded
 * model.  This valid counterexample must specify both input and state
 * values, because some inputs of the encoded model will be derived from
 * the states of the decoded one.
 */
void ProofAttachment::restoreDroppedLatches() {

  //Currently only works for AIGER 1.0
  
  Expr::Manager::View * ev = model().newView();

  // Grab information about the unoptimized decoded model.
  SeqAttachment const * const seat = (SeqAttachment const *)
    model().constAttachment(Key::SEQ);
  assert(seat); // if we reached this point, the attachment should exist
  set<ID> init(seat->decodedInitialConditions.begin(),
               seat->decodedInitialConditions.end());
  const vector<ID> & initialConditions = seat->decodedInitialConditions;
  const vector<ID> & decodedInputs = seat->decodedInputs;
  const vector<ID> & latches = seat->decodedStateVars;
  const vector<ID> & nsf = seat->decodedNextStateFns;
  const vector<ID> & constraintFns = seat->decodedConstraintFns;
  unordered_map<ID, ID> missingLatches = seat->optimized;
  model().constRelease(seat);

  // Build unoptimized decoded transition relation for simulation.
  vector< vector<ID> > tr;
  vector<ID> trans;
  for (unsigned i = 0; i < latches.size(); ++i) {
    trans.push_back(ev->apply(Expr::Equiv,
                              ev->prime(latches[i]),
                              nsf[i]));
  }
  for (vector<ID>::const_iterator cit = constraintFns.begin();
       cit != constraintFns.end(); ++cit) {
    trans.push_back(*cit);
  }
  Expr::tseitin(*ev, trans, tr);
  SAT::Manager * sman = model().newSATManager();
  SAT::Manager::View * sview = sman->newView(*ev);
  sview->add(tr);

  vector<Transition>::iterator cexIt = _cex.begin();

  //Restore initial conditions of missing latches.
  for(unordered_map<ID, ID>::const_iterator latchIt = missingLatches.begin();
      latchIt != missingLatches.end(); ++latchIt) {
    //Dropped latches must obey initial conditions
    if (init.find(latchIt->first) != init.end()) {
      cexIt->state.push_back(latchIt->first);
    }
    else if (init.find(ev->apply(Expr::Not, latchIt->first)) != init.end()) {
      cexIt->state.push_back(ev->apply(Expr::Not, latchIt->first));
    } else {
      // Dubious: Make sure every latch is initialized!
      cexIt->state.push_back(ev->apply(Expr::Not, latchIt->first));
    }
  }
  // Make sure latches that are not missing got their initial conditions.
  set<ID> cexInit(cexIt->state.begin(), cexIt->state.end());
  for (vector<ID>::const_iterator it = initialConditions.begin();
       it != initialConditions.end(); ++it) {
    if (cexInit.find(*it) == cexInit.end())
      cexIt->state.push_back(*it);
  }
  // Add missing inputs in negative phase.
  set<ID> inputSet(cexIt->inputs.begin(), cexIt->inputs.end());
  for (vector<ID>::const_iterator iit = decodedInputs.begin();
       iit != decodedInputs.end(); ++iit) {
    if (inputSet.find(*iit) != inputSet.end()) continue;
    ID negInp = ev->apply(Expr::Not, *iit);
    if (inputSet.find(negInp) == inputSet.end())
      cexIt->inputs.push_back(negInp);
  }


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
        bool complementary = ev->op(latchIt->second) == Expr::Not;
        ID regularEquiv = complementary ?
          ev->apply(Expr::Not, latchIt->second) : latchIt->second;
        unordered_map<ID, ID>::const_iterator equivLatch =
            missingLatches.find(regularEquiv);
        //if it's not a missing latch
        if(equivLatch == missingLatches.end()) {
          //The missing latch should have the same value as the one it's
          //equivalent to
          set<ID> state(cexIt->state.begin(), cexIt->state.end());
          if(state.find(latchIt->second) != state.end()) {
            cexIt->state.push_back(latchIt->first);
          }
          else if (state.find(ev->apply(Expr::Not, latchIt->second)) != state.end()) {
            cexIt->state.push_back(ev->apply(Expr::Not, latchIt->first));
          }
          else {
            asgn.insert(SAT::Assignment::value_type(
                ev->prime(latchIt->first), SAT::Unknown));
          }
        }
        else {
          //It is equivalent to a missing latch.  We let the SAT
          //solver figure out the right value.
          asgn.insert(SAT::Assignment::value_type(
              ev->prime(latchIt->first), SAT::Unknown));
        }
      }
      else {
        //Latch is not in COI. Need to find its value through a SAT query
        asgn.insert(SAT::Assignment::value_type(
            ev->prime(latchIt->first), SAT::Unknown));
      }
    }
    // Add to the assignment the latches that are not missing, but
    // were given no value in this step of the counterexample.
    set<ID> latchSet(cexIt->state.begin(), cexIt->state.end());
    for (vector<ID>::const_iterator latchIt = latches.begin();
         latchIt != latches.end(); ++latchIt) {
      if (latchSet.find(*latchIt) == latchSet.end()) {
        ID negID = ev->apply(Expr::Not, *latchIt);
        if (latchSet.find(negID) == latchSet.end()) {
          asgn.insert(SAT::Assignment::value_type(
              ev->prime(*latchIt), SAT::Unknown));
        }
      }
    }
    // Add missing inputs in negative phase.
    set<ID> inputSet(cexIt->inputs.begin(), cexIt->inputs.end());
    for (vector<ID>::const_iterator iit = decodedInputs.begin();
         iit != decodedInputs.end(); ++iit) {
      if (inputSet.find(*iit) != inputSet.end()) continue;
      ID negInp = ev->apply(Expr::Not, *iit);
      if (inputSet.find(negInp) == inputSet.end())
        cexIt->inputs.push_back(negInp);
    }
    if(!asgn.empty()) {
      // There is at least one latch whose value should be found.
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
    }
  }
  delete sview;
  delete sman;

  delete ev;

}


void ProofAttachment::addEquivalenceInfo() {

  if(model().options().count("xmap_cex"))
    return;

  SeqAttachment const * const seat = (SeqAttachment const *) model().constAttachment(Key::SEQ);
  if(!seat)
    return;

  Expr::Manager::View * ev = model().newView();

  const unordered_map<ID, ID> & optLatches = seat->optimized;

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
  model().constRelease(seat);

}

void ProofAttachment::printCex(std::ostream& os) const
{
  assert(_hasConclusion && _safe == 1);
  Expr::Manager::View * v = _model.newView();

  assert(_model.options().count("print_cex")); // delete this?

  os << std::endl << "1\nCounterexample Trace:" << std::endl;


  std::vector<Transition> cex(_cex);

  // compute changing latches/inputs, take state intersection after sorting by ID
  std::vector <ID> newState (_cex[0].state);
  std::vector <ID> newInputs (_cex[0].inputs);
  std::vector <ID> diffState (_cex[0].state);
  std::vector <ID> diffInputs (_cex[0].inputs);
  if (!_cex.empty()){
    std::sort(cex[0].state.begin(), cex[0].state.end());
    std::sort(cex[0].inputs.begin(), cex[0].inputs.end());
  }
  unsigned i;
  for(i = 1; i < _cex.size(); ++i) {
    std::vector<ID>::iterator endIt;
    std::sort(cex[i].state.begin(), cex[i].state.end()); // by ID, for intersection
    
    endIt = set_difference(cex[i].state.begin(), cex[i].state.end(),
			   cex[i-1].state.begin(), cex[i-1].state.end(), diffState.begin());
    cex[i-1].state = newState;
    newState = std::vector<ID>(diffState.begin(), endIt);
    
    std::sort(cex[i].inputs.begin(), cex[i].inputs.end());
    endIt = set_difference(cex[i].inputs.begin(), cex[i].inputs.end(),
			   cex[i-1].inputs.begin(), cex[i-1].inputs.end(), diffInputs.begin());
    cex[i-1].inputs = newInputs;
    newInputs = std::vector<ID>(diffInputs.begin(), endIt);
  }
  cex[i-1].state = newState;
  cex[i-1].inputs = newInputs;


  // lexographically sort states
  for(unsigned i = 0; i < cex.size(); ++i) {
    sort(cex[i].state.begin(), cex[i].state.end(), nameCompare(v));
    sort(cex[i].inputs.begin(), cex[i].inputs.end(), nameCompare(v));
  }

  // traverse and print each cex state
  for(unsigned i = 0; i < cex.size(); ++i) {
    vector <ID> state (cex[i].state);
    vector <ID> inputs (cex[i].inputs);

    os << "--State " << i << ":" << endl;
    if(!state.empty()) {
      for(unsigned j = 0; j < state.size(); ++j) {
	bool isNeg = v->op(state[j]) == Expr::Not;
	ID baseId = isNeg ? v->apply(Expr::Not, state[j]) : state[j];
	// indentation can be used by some editors to do text folding
	os << "  " << stringOf(*v, baseId) << ":" << !isNeg << endl;
      }
    }
    else
      os << "  No latch change" << std::endl;

    os << "--Inputs: " << std::endl;
    if(!inputs.empty()) {
      for(unsigned j = 0; j < inputs.size(); ++j) {
	bool isNeg = v->op(inputs[j]) == Expr::Not;
	ID baseId = isNeg ? v->apply(Expr::Not, inputs[j]) : inputs[j];
	os << "  " << stringOf(*v, baseId) << ":" << !isNeg << endl;
      }
    }
    else
      os << "  No input change" << std::endl;

    os << std::endl;
  }
  delete v;
}


void ProofAttachment::printWitness(std::ostream& os)
{
  assert(_hasConclusion && _safe == 1);
  Expr::Manager::View * v = model().newView();
  // Get the original inputs and state variables.
  ExprAttachment const * const eat = (ExprAttachment const *) model().constAttachment(Key::EXPR);
  vector<ID> inputVars = eat->originalInputs();
  vector<ID> stateVars = eat->originalStateVars();
  model().constRelease(eat);

  std::string ostr("1\nc witness\nb0\n");
  size_t ostrlen = stateVars.size() + 1 + (inputVars.size() + 1) * _cex.size() + 40;
  ostr.reserve(ostrlen);

  // Print initial state.
  vector<ID> initState(_cex[0].state);
  unordered_map<ID, bool> initMap;
  for (size_t j = 0; j < initState.size(); ++j) {
    ID s = initState[j];
    bool isNeg = v->op(s) == Expr::Not;
    if (isNeg) {
      initMap.insert(unordered_map<ID, bool>::value_type(v->apply(Expr::Not,s),false));
    } else {
      initMap.insert(unordered_map<ID, bool>::value_type(s,true));
    }
  }
  for (size_t j = 0; j < stateVars.size(); ++j) {
    unordered_map<ID, bool>::const_iterator it = initMap.find(stateVars[j]);
    if (it == initMap.end()) {
      ostr.append(1, 'x');
    } else {
      ostr.append(1, it->second ? '1' : '0');
    }
  }
  ostr.append(1, '\n');

  for (unsigned i = 0; i < _cex.size(); ++i) {
    vector<ID> inputs (_cex[i].inputs);
    unordered_map<ID, bool> inputMap;
    for (size_t j = 0; j < inputs.size(); ++j) {
      ID t = inputs[j];
      bool isNeg =v->op(t) == Expr::Not;
      if (isNeg) {
        inputMap.insert(unordered_map<ID, bool>::value_type(v->apply(Expr::Not,t),false));
      } else {
        inputMap.insert(unordered_map<ID, bool>::value_type(t,true));
      }
    }
    for (size_t j = 0; j < inputVars.size(); ++j) {
      unordered_map<ID, bool>::const_iterator it = inputMap.find(inputVars[j]);
      if (it == inputMap.end()) {
        ostr.append(1, 'x');
      } else {
        ostr.append(1, it->second ? '1' : '0');
      }
    }
    ostr.append(1, '\n');
  }
  ostr.append(".\nc end witness\n");
  os << ostr;
  delete v;
}


void ProofAttachment::decodeCounterexample(void)
{
  restoreDroppedLatches();

  SeqAttachment const * const seat = (SeqAttachment const *)
    model().constAttachment(Key::SEQ);
  unordered_map<ID,ID> latchToInput = seat->latchToInput;
  model().constRelease(seat);

  // We need to re-encode inputs and reverse them.  Moreover, the decoded
  // traces are one step shorter, because the initialized latch has been
  // eliminated.  Here we assume that all latches have been restored.
  Expr::Manager::View * v = model().newView();
  vector<Transition> reversedCex;
  // Add last input, which is all Xs.
  reversedCex.push_back(Transition(vector<ID>(), vector<ID>()));
  for (unsigned i = 0; i < _cex.size(); ++i) {
    vector<ID> state;
    vector<ID> inputs(_cex[i].inputs);
    for (vector<ID>::const_iterator sit = _cex[i].state.begin(); sit != _cex[i].state.end(); ++sit) {
      bool isNeg = v->op(*sit) == Expr::Not;
      ID lid = isNeg ? v->apply(Expr::Not, *sit) : *sit;
      unordered_map<ID,ID>::const_iterator it = latchToInput.find(lid);
      if (it != latchToInput.end()) {
        ID iid = isNeg ? v->apply(Expr::Not, it->second) : it->second;
        inputs.push_back(iid);
      }
    }
    if (i == _cex.size() - 1) {
      ExprAttachment const * const eat = (ExprAttachment const *) model().constAttachment(Key::EXPR);
      state = eat->originalInitialConditions();
      model().constRelease(eat);
    }
    reversedCex.push_back(Transition(state,inputs));
  }
  _cex = vector<Transition>(reversedCex.rbegin(),reversedCex.rend());
  delete v;
}


void ProofAttachment::unfoldCounterexample(void)
{
  SeqAttachment const * const seat = (SeqAttachment const *)
    model().constAttachment(Key::SEQ);
  unordered_map<ID, pair<ID, unsigned> > cycleInputs = seat->cycleInputs;
  unsigned int unrollings = seat->unrollings;
  model().constRelease(seat);
  if (unrollings == 1) 
    return;
  std::vector<Transition> newCex;
  newCex.push_back(Transition());
  newCex[0].state = _cex[0].state;
  Expr::Manager::View * v = model().newView();
  // for each input@cycle in _cex, add original input value to correct step
  for (unsigned step = 0; step < _cex.size(); ++step) {
    for (unsigned i = 0; i < unrollings; ++i)
      newCex.push_back(Transition());
    for (vector<ID>::const_iterator jt = _cex[step].inputs.begin(); 
	 jt != _cex[step].inputs.end(); ++jt) {
      bool isNeg = v->op(*jt) == Expr::Not;
      ID baseIndex = isNeg ? v->apply(Expr::Not, *jt) : *jt;
      ID lid = (cycleInputs[baseIndex]).first;
      unsigned phase = (cycleInputs[baseIndex]).second;
      unsigned int newStep = step*unrollings + phase;
      if (isNeg)
	newCex[newStep].inputs.push_back(v->apply(Expr::Not, lid));
      else
	newCex[newStep].inputs.push_back(lid);
    }
  }
  delete v;
  _cex = newCex;
}


void ProofAttachment::produceEvidenceForFailure(void)
{
  boost::program_options::variables_map const & opts = model().options();
  assert(opts.count("print_cex"));
  bool skipMap = opts.count("xmap_cex");
  bool printInfo = opts.count("print_info") > 0;
  if (printInfo)
    Util::printSystemInfo();

  if (!skipMap) {
    // Determine the type of transformation to be applied to the raw
    // counterexample.  We assume that decoding if applied always comes
    // first, and that decoding and phase abstraction are mutually exclusive.
    SeqAttachment const * const seat = (SeqAttachment const *)
      model().constAttachment(Key::SEQ);
    bool decoded = seat && seat->decoded;
    bool phaseAbstracted = seat && (seat-> unrollings > 1);
    model().constRelease(seat);
    assert(!(decoded && phaseAbstracted));

    if (decoded) {
      decodeCounterexample();
    } else if (phaseAbstracted) {
      unfoldCounterexample();
      restoreInitialCondition();
    } else {
      restoreInitialCondition();
    }
  }

  // Determine the output stream.
  bool printToFile = opts.count("cex_file");
  ofstream ofs;
  if (printToFile) {
    // At this point, the conclusion (1) has not been written to cout.
    // If the counterexample goes to a file, we need to duplicate that 1.
    cout << '1' << endl;
    std::string fname = opts["cex_file"].as<std::string>();
    ofs.open(fname.c_str());
  }
  ostream& os = printToFile ? ofs : cout;

  // Select output format.
  bool aigerCex = opts.count("cex_aiger");
  if (aigerCex)
    printWitness(os);
  else
    printCex(os);

  if (printToFile) {
    ofs.close();
  }
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
