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

#include "AutoDriver.h"
#include "IIC.h"
#include "Error.h"
#include "BddAttachment.h"
#include "BddReach.h"
#include "BMC.h"
#include "Fair.h"
#include "FCBMC.h"
#include "IC3.h"
#include "IICTL.h"
#include "MC.h"
#include "StuckAt.h"
#include "SequentialEquivalence.h"
#include "Simplifier.h"
#include "SATSweep.h"
#include "AbsInt.h"
#undef PARSER_HEADER_H
#undef BISON_LOCATION_HH
#undef BISON_POSITION_HH
#undef BISON_STACK_HH
#include "PropCtlDriver.h"

#include <boost/program_options.hpp>

#include <sstream>

using namespace std;

namespace {
  unsigned numSetBits(Automaton::State state) {
    unsigned rv = 0;
    while(state > 0) {
      if(state % 2 == 1)
        ++rv;
      state >>= 1;
    }
    return rv;
  }

  unsigned numEncodingBits(int numStates) {
    --numStates;
    unsigned rv = 1;
    while(numStates > 1) {
      numStates >>= 1;
      ++rv;
    }
    return rv;
  }
 
  void composeAutomaton(Model & m, ExprAttachment * eat) {
    //TODO: Add invariant constraints expressing unreachability of certain
    //automaton states
    const Automaton & aut = eat->automata()[0];
    const unsigned numStates = aut.states.size();
    assert(numStates > 0);
    const unsigned numLatches = numEncodingBits(numStates);
    Expr::Manager::View * v = m.newView();
    std::vector<ID> autLatches;
    for(unsigned latch = 0; latch < numLatches; ++latch) {
      std::stringstream ss;
      ss << "_autVar" << latch;
      assert(!v->varExists(ss.str()));
      autLatches.push_back(v->newVar(ss.str()));
    }
    for(unsigned latch = 0; latch < numLatches; ++latch) {
      //Compute the next-state function of this latch
      //Get all transitions to states with this latch set to 1
      std::vector<ID> disj;
      for(std::vector<Automaton::Transition>::const_iterator it = aut.transitions.begin();
          it != aut.transitions.end(); ++it) {
        Automaton::State dest = it->destination;
        dest >>= latch;
        if(dest % 2 == 1) {
          Automaton::State source = it->source;
          std::vector<ID> conj;
          for(unsigned i = 0; i < numLatches; ++i) {
            conj.push_back(source % 2 == 1 ? autLatches[i] :
                                             v->apply(Expr::Not, autLatches[i]));
            source >>= 1;
          }
          conj.push_back(it->label);
          disj.push_back(v->apply(Expr::And, conj));
        }
      }
      eat->setNextStateFn(autLatches[latch], Expr::AIGOfExpr(*v, v->apply(Expr::Or, disj)));
    }
    eat->addAutStateVars(autLatches);
    Automaton::State init = 0;
    assert(aut.initialStates.size() > 0);
    for(unsigned i = 0; i < aut.initialStates.size() - 1; ++i) {
      init |= (aut.initialStates[i] ^ aut.initialStates[i + 1]);
    }
    unsigned numInitStates = numSetBits(init) + 1;
    if(numInitStates != aut.initialStates.size())
      throw InputError("Could not encode initial state(s) of automaton as a cube.");
    unsigned mask = 1;
    for(unsigned latch = 0; latch < numLatches; ++latch) {
      if((init & mask) == 0) {
        bool high = mask & aut.initialStates[0];
        eat->addInitialCondition(high ? autLatches[latch] :
                                        v->apply(Expr::Not, autLatches[latch]));
      }
      mask <<= 1;
    }
    //Assume single bad state
    assert(aut.badStates.size() == 1);
    Automaton::State badState = aut.badStates[0];
    ID badFn;
    if(!m.options().count("auto_xpre")) {
      std::vector<ID> disj;
      for(std::vector<Automaton::Transition>::const_iterator it = aut.transitions.begin();
          it != aut.transitions.end(); ++it) {
        if(it->destination == badState && it->source != badState) {
          Automaton::State source = it->source;
          std::vector<ID> conj;
          for(unsigned latch = 0; latch < numLatches; ++latch) {
            conj.push_back(source % 2 == 1 ? 
                           autLatches[latch] :
                           v->apply(Expr::Not, autLatches[latch]));
            source >>= 1;
          }
          conj.push_back(it->label);
          disj.push_back(v->apply(Expr::And, conj));
        }
      }
      badFn = v->apply(Expr::Or, disj);
    }
    else {
      std::vector<ID> conj;
      Automaton::State badStateCp = badState;
      for(unsigned latch = 0; latch < numLatches; ++latch) {
        conj.push_back(badStateCp % 2 == 1 ? autLatches[latch] :
                          v->apply(Expr::Not, autLatches[latch]));
        badStateCp >>= 1;
      }
      badFn = v->apply(Expr::And, conj);
    }
    std::set<ID> support;
    for(std::vector<Automaton::Transition>::const_iterator it = aut.transitions.begin();
        it != aut.transitions.end(); ++it) {
      Expr::variables(*v, it->label, support);
    }
    //Add bad state function as first output
    std::vector<ID> outputs = eat->outputs();
    std::vector<ID> keepOutputs;
    set_intersection(support.begin(), support.end(), outputs.begin(),
                     outputs.end(), inserter(keepOutputs, keepOutputs.end()));
    std::vector<ID> keepOutputFns = eat->outputFnOf(keepOutputs);
    eat->clearOutputFns();
    std::stringstream ss;
    ss << "_autBad";
    ID bad = v->newVar(ss.str());
    eat->setOutputFn(bad, Expr::AIGOfExpr(*v, badFn));
    eat->setOutputFns(keepOutputs, keepOutputFns);

    delete v;
  }
}


namespace IIC {
  void FixRoots::exec() {
    model().setDefaultMode(Model::mNONE);

    ExprAttachment * eat = (ExprAttachment *) model().attachment(Key::EXPR);
    unsigned int pi = model().options()["pi"].as<unsigned int>();
    if (model().options().count("ctl") > 0) { // CTL model checking
      std::string filename =  model().options()["ctl"].as<std::string>();
      ctl_driver driver(eat);
      if (driver.parse(filename))
        throw InputError("Error(s) in property file " + filename);
      std::vector<ID> properties = eat->ctlProperties();
      if (pi >= properties.size())
        throw InputError("Property index out of range");
      eat->clearBadFns();
      eat->clearJusticeSets();
      ID ctlp = properties[pi];
      eat->clearCtlProperties();
      eat->addCtlProperty(ctlp);
      std::set<ID> support;
      Expr::Manager::View * v = model().newView();
      Expr::variables(*v, ctlp, support);
      delete v;
      std::set<ID> outputs(eat->outputs().begin(),eat->outputs().end());
      std::vector<ID> poutputs;
      set_intersection(support.begin(), support.end(), outputs.begin(), outputs.end(), inserter(poutputs, poutputs.end()));
      std::vector<ID> poutFns = eat->outputFnOf(poutputs);
      eat->clearOutputFns();
      eat->setOutputFns(poutputs, poutFns);
      model().setDefaultMode(Model::mIICTL);
    }
    else if (model().options().count("auto") > 0) { // automata model checking
      std::string filename =  model().options()["auto"].as<std::string>();
      auto_driver driver(eat);
      if (driver.parse(filename))
        throw InputError("error(s) in property file " + filename);
      std::vector<Automaton> automata = eat->automata();
      if (pi >= automata.size())
        throw InputError("property index out of range");
      if (model().options().count("print_auto") > 0) 
        std::cout << driver.toDot(pi) << std::endl;
      eat->clearBadFns();
      eat->clearJusticeSets();
      Automaton aut = automata[pi];
      eat->clearAutomata();
      eat->addAutomaton(aut);
      composeAutomaton(model(), eat);
      model().setDefaultMode(Model::mIC3);
    }
    else if (eat->bad().size() > 0 && pi < eat->bad().size()) { // safety
      if (model().verbosity() > Options::Silent &&
          (eat->bad().size() > 1 ||
           eat->fairness().size() > 0 || 
           eat->justice().size() > 0))
        std::cout << "IGNORING ALL BUT BAD OUTPUT " << pi << std::endl;
      eat->clearOutputFns();
      std::vector<ID> bad = eat->bad();
      std::vector<ID> badFns = eat->badFns();
      eat->clearBadFns();
      eat->clearFairnessFns();
      eat->clearJusticeSets();
      eat->setOutputFn(bad[pi], badFns[pi]);
      model().setDefaultMode(Model::mIC3);
    }
    else if (eat->justice().size() > 0 && pi - eat->bad().size() < eat->justice().size()) { // progress
      pi -= eat->bad().size();
      assert(pi < eat->justice().size());
      if (model().verbosity() > Options::Silent && eat->justice().size() > 1)
        std::cout << "IGNORING ALL BUT JUSTICE SET " << pi << std::endl;
      eat->clearOutputFns();
      eat->clearBadFns();
      std::vector<ID> fairness = eat->fairness();
      std::vector<ID> fairnessFns = eat->fairnessFns();
      eat->clearFairnessFns();
      for (size_t i = 0; i < fairness.size(); ++i)
        eat->setOutputFn(fairness[i], fairnessFns[i]);
      if (eat->justice().size() > 0) {
        Expr::Manager::View * v = model().newView();
        for (size_t i = 0; i < eat->justiceSets()[pi].size(); ++i) {
          std::stringstream ss;
          ss << "j" << i;
          eat->setOutputFn(v->newVar(ss.str()), eat->justiceSets()[pi][i]);
        }
        delete v;
      }
      eat->clearJusticeSets();
      model().setOption("bdd_trav");
      model().setOption("bdd_save_fw_reach");
      model().setDefaultMode(Model::mFAIR);
    }
    else if (eat->bad().empty() && eat->justice().empty() && pi < eat->outputs().size()) { // AIGER 1.0: safety
      std::vector<ID> outputs = eat->outputs();
      std::vector<ID> outputFns = eat->outputFns();
      eat->clearOutputFns();
      eat->setOutputFn(outputs[pi], outputFns[pi]);
      if (model().verbosity() > Options::Silent && eat->outputs().size() > 1)
        std::cout << "IGNORING ALL BUT OUTPUT " << pi << std::endl;
      model().setDefaultMode(Model::mIC3);
    }
    else {
      throw InputError("Property index out of range");
    }
    model().release(eat);
  }


  void IICAction::exec() {
    if (model().defaultMode() == Model::mIC3) {
      model().pushFrontTactic(new IC3::IC3Action(model()));

      // Run BDD-based reachability analysis if the model is not too large.
      ExprAttachment const * const eat =
        (ExprAttachment const * const) model().constAttachment(Key::EXPR);
      size_t numvars = eat->stateVars().size();
      model().constRelease(eat);
      size_t varlimit = model().options()["check_bdd_max"].as<size_t>();
      if (numvars < varlimit)
        model().pushFrontTactic(new BddFwReachAction(model()));

      model().pushFrontTactic(new BMC::BMCAction(model()));
      model().pushFrontTactic(new IC3::IC3Action(model(), true /* reverse */));
    }
    else if (model().defaultMode() == Model::mFAIR) {
      Fair::FairOptions opts(options());
      opts.ic3_opts.sccH = true;
      model().pushFrontTactic(new Fair::FairAction(model(), &opts));
      model().pushFrontTactic(new FCBMC::FCBMCAction(model()));
    }
    else if (model().defaultMode() == Model::mIICTL) {
      model().pushFrontTactic(new IICTL::IICTLAction(model()));
    }
  }


  void PreProcessAction::exec() {
    model().pushFrontTactic(new COIAction(model()));
    model().pushFrontTactic(new AbsIntAction(model()));
    model().pushFrontTactic(new COIAction(model()));
    model().pushFrontTactic(new TvSimplifierAction(model()));
    model().pushFrontTactic(new COIAction(model()));
    model().pushFrontTactic(new ::Action::SATSweepAction(model()));
    model().pushFrontTactic(new BddSweepAction(model()));
    model().pushFrontTactic(new COIAction(model()));
    model().pushFrontTactic(new SequentialEquivalenceAction(model()));
    model().pushFrontTactic(new StuckAtAction(model()));
    model().pushFrontTactic(new COIAction(model()));
  }


  void SequentialReductionAction::exec() {
    model().pushFrontTactic(new COIAction(model()));
    model().pushFrontTactic(new SequentialEquivalenceAction(model()));
    model().pushFrontTactic(new StuckAtAction(model()));
    model().pushFrontTactic(new COIAction(model()));
  }
}
