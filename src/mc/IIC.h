/* -*- C++ -*- */

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

#ifndef _IIC_
#define _IIC_

/** @file IIC.h **/

#include "BddReach.h"
#include "BMC.h"
#include "ExprAttachment.h"
#include "Fair.h"
#include "FCBMC.h"
#include "IC3.h"
#include "IICTL.h"
#include "MC.h"
#include "Model.h"
#include "PropCtlDriver.h"
#include "Error.h"

#include <boost/program_options.hpp>

#include <sstream>

/** namespace of IIC */
namespace IIC {

  /**
   * Chooses the roots of the model that are relevant to this run.
   */
  class FixRoots: public Model::Action {
  public:
    FixRoots(Model & m) : Model::Action(m) {
      ExprAttachment::Factory eaf;
      requires(Key::EXPR, &eaf);
    }
    virtual void exec() {
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
            ss << "jo" << i;
            eat->setOutputFn(v->newVar(ss.str()), eat->justiceSets()[pi][i]);
          }
          delete v;
        }
        eat->clearJusticeSets();
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
  };

  class IICAction : public Model::Action {
  public:
    IICAction(Model & m) : Model::Action(m) {
      ExprAttachment::Factory eaf;
      requires(Key::EXPR, &eaf);
    }
    virtual void exec() {
      if (model().defaultMode() == Model::mIC3) {
        IC3::IC3Action(model(), true /* reverse */).make();
        const ProofAttachment * pat = (const ProofAttachment *) model().attachment(Key::PROOF);
        bool hc = pat->hasConclusion();
        model().constRelease(pat);
        if (hc) return;
        BMC::BMCAction(model()).make();
        pat = (const ProofAttachment *) model().attachment(Key::PROOF);
        hc = pat->hasConclusion();
        model().constRelease(pat);
        if (hc) return;
        BddFwReachAction(model()).make();
        pat = (const ProofAttachment *) model().attachment(Key::PROOF);
        hc = pat->hasConclusion();
        model().constRelease(pat);
        if (hc) return;
        IC3::IC3Action(model()).make();
      }
      else if (model().defaultMode() == Model::mFAIR) {
        FCBMC::FCBMCAction(model()).make();
        const ProofAttachment * pat = (const ProofAttachment *) model().attachment(Key::PROOF);
        bool hc = pat->hasConclusion();
        model().constRelease(pat);
        if (hc) return;
        Fair::FairOptions opts(options());
        opts.ic3_opts.sccH = true;
        Fair::FairAction(model(), &opts).make();
      }
      else if (model().defaultMode() == Model::mIICTL) {
        IICTL::IICTLOptions opts(options());
        // opts.ic3_opts.sccH = true; // ???
        IICTL::IICTLAction(model(), &opts).make();
      }
    }
  };

}

#endif
