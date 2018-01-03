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
#include "KLive.h"
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
#include "PhaseAbstraction.h"
#include "Dispatch.h"
#include "Decode.h"
#include "Slice.h"
#include "BddGSH.h"
#include "Random.h"

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

    auto eat = model().attachment<ExprAttachment>(Key::EXPR);
    unsigned int pi = model().options()["pi"].as<unsigned int>();
    if (model().options().count("ctl") > 0) { // CTL model checking
      std::string filename =  model().options()["ctl"].as<std::string>();
      ctl_driver driver(eat.operator->());
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
      auto_driver driver(eat.operator->());
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
      composeAutomaton(model(), eat.operator->());
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
      if (model().options().count("degen") > 0 && eat->outputs().size() > 1) {
        //Degeneralize
        const vector<ID> & ofns = eat->outputFns();
        int num = ofns.size();
        Expr::Manager::View * v = model().newView();
        vector<ID> newStateVars;
        for (int i = 0; i < num; ++i) {
          ostringstream buf;
          buf << "__dgVar" << i << "__";
          newStateVars.push_back(v->newVar(buf.str()));
        }
        ID fair = v->apply(Expr::And, newStateVars);
        fair = AIGOfExpr(*v, fair);
        for (int i = 0; i < num; ++i) {
          ID fn = v->apply(Expr::Or, ofns[i], v->apply(Expr::And, v->apply(Expr::Not, fair), newStateVars[i]));
          fn = AIGOfExpr(*v, fn);
          eat->setNextStateFn(newStateVars[i], fn);
          eat->addInitialCondition(v->apply(Expr::Not, newStateVars[i]));
        }
        eat->clearOutputFns();
        ID dg = v->newVar("__dg__");
        eat->setOutputFn(dg, fair);
        delete v;
      }
    }
    else if (eat->bad().empty() && eat->justice().empty() && pi < eat->outputs().size()) { // AIGER 1.0: safety
      std::vector<ID> outputs = eat->outputs();
      std::vector<ID> outputFns = eat->outputFns();
      eat->clearOutputFns();
      if (model().options().count("pre")) {
        ID of = outputFns[pi];
        set<ID> support;
        Expr::Manager::View * v = model().newView();
        Expr::variables(*v, of, support);
        bool latchesOnly = true;
        for (set<ID>::const_iterator it = support.begin(); it != support.end(); ++it) {
          if (!eat->isStateVar(*it)) {
            latchesOnly = false;
            break;
          }
        }
        if (latchesOnly) {
          if (model().verbosity() > Options::Silent)
            cout << "Output is a function of state variables only. Performing precondition" << endl;
          const vector<ID> & sv = eat->stateVars();
          const vector<ID> & fns = eat->nextStateFns();
          Expr::IDMap var2fn;
          for (unsigned i = 0; i < sv.size(); ++i) {
            var2fn.insert(Expr::IDMap::value_type(sv[i], fns[i]));
          }
          ID subbed = Expr::varSub(*v, var2fn, of);
          ID disj = v->apply(Expr::Or, of, subbed);
          eat->setOutputFn(outputs[pi], disj);
        }
        else {
          eat->setOutputFn(outputs[pi], outputFns[pi]);
        }
        delete v;
      }
      else {
        eat->setOutputFn(outputs[pi], outputFns[pi]);
      }
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
    // Get number of hardware threads to decide the recipe.
    unsigned long const max_threads = std::thread::hardware_concurrency();
    // Get minimum number of threads to choose multi-thread recipe.
    unsigned long const min_threads = model().options()["min_threads"].as<unsigned long>();
    unsigned long const thread_limit = model().options()["thread_limit"].as<unsigned long>();
    // Check numbers of state variables and expression nodes to decide how many threads
    // to run.  (These are the numbers after preprocessing.)
    ExprAttachment const * const eat =
      (ExprAttachment const *) model().constAttachment(Key::EXPR);
    size_t varlimit = model().options()["check_bdd_max"].as<size_t>();
    size_t numvars = eat->stateVars().size();
    vector<ID> roots(eat->nextStateFns());
    roots.insert(roots.end(), eat->outputFns().begin(), eat->outputFns().end());
    Expr::Manager::View * ev = model().newView();
    unsigned long modelSize = Expr::sizeOf(*ev, roots);
    delete ev;
    model().constRelease(eat);
    // Choose number of threads.
    unsigned nthreads = modelSize > 0 ? ceil((4000000)/modelSize) : thread_limit;
    nthreads = nthreads < thread_limit ? nthreads : thread_limit;
    unsigned long reorder_timeout = 1500*nthreads;
    // Push tactics at the front of the tactic queue in reverse order.
    // This way, the tactics following "standard" are still executed after it.
    if (model().defaultMode() == Model::mIC3) {
      // Run BDD-based reachability analysis if the model is not too large.
      if (max_threads < min_threads) {
        // Single-thread recipe.
        model().pushFrontTactic(new IC3::IC3Action(model()));
        if (numvars < varlimit)
          model().pushFrontTactic(new BddFwReachAction(model()));
        model().pushFrontTactic(new BMC::BMCAction(model()));
        model().pushFrontTactic(new IC3::IC3Action(model(), true /* reverse */));
      } else {
        // Multi-thread recipe.
	if (model().verbosity() > Options::Terse)
	  cout << "Scheduling " << nthreads << " threads. Model size: "<< modelSize << endl;
        // Set option defaults.
        model().setOptionValue("bdd_fw_timeout", (unsigned long) reorder_timeout);
        model().setOptionValue("bdd_timeout", (unsigned long) reorder_timeout);
        model().setOptionValue("bmc_timeout", -1);
        model().setOptionValue("ic3r_timeout", -1);
        model().setOption("ic3_lift");
        // Schedule actions.
	model().pushFrontTactic(new Dispatch::Join(model()));	
	if ((numvars < varlimit) && (nthreads > 3)) {  // BDD_FW
	  if (model().verbosity() > Options::Terse)
	    cout << "Scheduling tactic BddFwReach." << endl;
	  model().pushFrontTactic(new BddFwReachAction(model()));
	  nthreads--;
	}
	int rseed = model().options()["rand"].as<int>();
#ifndef DISABLE_ZCHAFF
        string const defBackE = "zchaff";
#else
        string const defBackE = "minisat";
#endif
	switch (nthreads) {
	  case 12 :   // IC3 - rseed+2
	    model().pushFrontTactic(new IC3::IC3Action(model(), false, false,
						       defBackE, 3, rseed+2));
	  case 11 :   // IC3lr - rseed+1
	    model().pushFrontTactic(new IC3::IC3Action(model(), false, true,
						       defBackE, 3, rseed+1));
	  case 10 :   // IC3R - rseed+1
	    model().pushFrontTactic(new IC3::IC3Action(model(), true, false,
						       defBackE, 3, rseed+1));
	  case 9 :   // BMC - rseed+1
	    model().pushFrontTactic(new BMC::BMCAction(model(), rseed+1));
	  case 8 :   // IC3 - rseed+1
	    model().pushFrontTactic(new IC3::IC3Action(model(), false, false,
						       defBackE, 3, rseed+1));
	  case 7 :   // IC3R - miniSAT
	    model().pushFrontTactic(new IC3::IC3Action(model(), true, false, 
						       "minisat"));
	  case 6 :   // IC3 - CTG 0
	    model().pushFrontTactic(new IC3::IC3Action(model(), false, false, 
						       defBackE, 0));
	  case 5 :   // IC3 - miniSAT
	    model().pushFrontTactic(new IC3::IC3Action(model(), false, false, 
						       "minisat"));
	  case 4 :   // IC3lr
	    model().pushFrontTactic(new IC3::IC3Action(model(), false, true));
	  case 3 :   // IC3R
	    model().pushFrontTactic(new IC3::IC3Action(model(), true));
	  case 2 :   // BMC
	    model().pushFrontTactic(new BMC::BMCAction(model()));
	  case 1 :   // IC3
	    model().pushFrontTactic(new IC3::IC3Action(model(), false, false, defBackE));
	    break;
	  default :
	    assert(false);
	}
	model().pushFrontTactic(new Dispatch::Fork(model()));
      }
    }
    else if (model().defaultMode() == Model::mFAIR) {
      Fair::FairOptions opts(options());
      opts.ic3_opts.sccH = true;
      if (max_threads < min_threads) {
        // Single-thread recipe.
        model().pushFrontTactic(new Fair::FairAction(model(), &opts));
        model().pushFrontTactic(new FCBMC::FCBMCAction(model()));
      } else {
        // Multi-thread recipe.
	if (model().verbosity() > Options::Terse)
	  cout << "Scheduling " << nthreads << " threads. Model size: "<< modelSize << endl;
        // Set option defaults.
        model().setOptionValue("fcbmc_timeout", -1);
        model().setOptionValue("bdd_timeout", (unsigned long) 15);
        model().setOptionValue("bdd_fw_timeout", (unsigned long) 15);
        model().setOptionValue("gsh_timeout", (unsigned long) 6000);
        model().setOption("bdd_trav");
        model().setOption("bdd_save_fw_reach");
        model().pushFrontTactic(new Dispatch::Join(model()));
	if ((numvars < varlimit) && (nthreads > 2)) {  // BDD_FW
	  if (model().verbosity() > Options::Terse)
	    cout << "Scheduling tactics BddFwReach + GSH." << endl;
          model().pushFrontTactic(new Dispatch::End(model()));
          model().pushFrontTactic(new BddGSHAction(model()));
          model().pushFrontTactic(new BddFwReachAction(model()));
          model().pushFrontTactic(new Dispatch::Begin(model()));
	  nthreads--;
	}
#if 0
	int rseed = model().options()["rand"].as<int>();
#endif
	switch (nthreads) {
        case 12:
        case 11:
        case 10:
        case 9:
        case 8:
        case 7:
        case 6:
        case 5:
        case 4:
#if 0
        case 4:
        case 6:   // fair + rand+1
	  {
	  Fair::FairOptions opts(options());
	  opts.ic3_opts.sccH = true;
	  opts.ic3_opts.rseed = rseed+1;
          model().pushFrontTactic(new Fair::FairAction(model(), &opts));
	  }
        case 6:   // fcbmc + rand+1
	  {
	  // set new FCBMC options
	  FCBMC::FCBMCOptions opts(options());
	  opts.rseed = rseed+1;
          model().pushFrontTactic(new FCBMC::FCBMCAction(model(), &opts));
	  }
        case 6:   // klive + minisat
	  {
	  // is not currently safe
	    model().pushFrontTactic(new KLiveAction(model(), std::string("minisat")));
	  }
        case 5:	  // fair + minisat
	  {
	  Fair::FairOptions opts(options());
	  opts.ic3_opts.sccH = true;
	  opts.ic3_opts.backend = "minisat";
          model().pushFrontTactic(new Fair::FairAction(model(), &opts));
	  }
        case 4:	  // fair + phase
	  {
	  Fair::FairOptions opts(options());
	  opts.ic3_opts.sccH = true;
	  opts.doPhase = true; // add to check
          model().pushFrontTactic(new Fair::FairAction(model(), &opts));
	  }
#endif
        case 3:
          model().pushFrontTactic(new KLiveAction(model()));
        case 2:
          model().pushFrontTactic(new FCBMC::FCBMCAction(model()));
        case 1:
          model().pushFrontTactic(new Fair::FairAction(model(), &opts));
          break;
        default:
          assert(false);
        }
        model().pushFrontTactic(new Dispatch::Fork(model()));
      }
    }
    else if (model().defaultMode() == Model::mIICTL) {
      model().pushFrontTactic(new IICTL::IICTLAction(model()));
    }
  }


  void PreProcessAction::exec() {
    if (model().ppIsDisabled()) return;
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


  void HalfPreProcessAction::exec() {
    if (model().ppIsDisabled()) return;
    model().pushFrontTactic(new COIAction(model()));
    model().pushFrontTactic(new TvSimplifierAction(model()));
    model().pushFrontTactic(new COIAction(model()));
    model().pushFrontTactic(new ::Action::SATSweepAction(model()));
    model().pushFrontTactic(new BddSweepAction(model()));
    model().pushFrontTactic(new COIAction(model()));
    model().pushFrontTactic(new StuckAtAction(model()));
    model().pushFrontTactic(new COIAction(model()));
  }


  void SequentialReductionAction::exec() {
    model().pushFrontTactic(new COIAction(model()));
    model().pushFrontTactic(new SequentialEquivalenceAction(model()));
    model().pushFrontTactic(new StuckAtAction(model()));
    model().pushFrontTactic(new COIAction(model()));
  }


  void HwmccAction::exec() {
    model().pushFrontTactic(new IIC::IICAction(model()));
    if (model().defaultMode() == Model::mIC3) {
      model().pushFrontTactic(new SliceAction(model()));
      //model().pushFrontTactic(new IIC::HalfPreProcessAction(model()));
      model().pushFrontTactic(new IIC::PreProcessAction(model()));
      model().pushFrontTactic(new PhaseAbstractionAction(model()));
    }
    model().pushFrontTactic(new IIC::PreProcessAction(model()));
    if (model().defaultMode() == Model::mIC3) {
      model().pushFrontTactic(new DecodeAction(model()));
    }
    model().pushFrontTactic(new IIC::StandardOptionsAction(model()));
  }


  void StandardOptionsAction::exec() {
    if (model().defaultMode() == Model::mIC3) {
      model().setOption("print_cex");
      model().setOption("cex_aiger");
      model().setOptionValue("bdd_sw_timeout", (unsigned long) 30);
      model().setOptionValue("tv_timeout", (int) 200);
      model().setOptionValue("se_timeout", (int) 200);
      model().setOptionValue("absint_timeout", (int) 200);
      // Make results (more) reproducible.
      if (model().options()["rand"].as<int>() == -1) {
        model().setOptionValue("rand", 1);
	Random::set_seed(1);
      }
    }
  }
}
