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

#ifndef _FCBMC_
#define _FCBMC_

/** @file FCBMC.h */

#include <boost/program_options.hpp>

#include "CNFAttachment.h"
#include "COI.h"
#include "Expr.h"
#include "ExprAttachment.h"
#include "Model.h"
#include "MC.h"
#include "ProofAttachment.h"

/** namespace of BMC */
namespace FCBMC {
  struct FCBMCOptions {
    FCBMCOptions(SAT::Clauses * _constraints = NULL) :
      constraints(_constraints), silent(false), backend("minisat") {}
    FCBMCOptions(const boost::program_options::variables_map & opts) : 
      extractCex(opts.count("print_cex")), constraints(NULL), silent(false),
      backend(opts["fcbmc_backend"].as<std::string>()) {}
    bool extractCex;
    SAT::Clauses * constraints;
    bool silent;
    std::string backend;
  };

  class FCBMC {
  public:
    FCBMC(Model & m, const FCBMCOptions & opts);
    ~FCBMC();
    MC::ReturnValue check(int timeout, int bound,
                          Lasso * cexTrace = NULL);
  private:
    void addVarsAt(int k);
    void clearAsgn();
    SAT::Clauses trAt(int k);
    void extractCex(Lasso & cexTrace);

    Model & model;
    FCBMCOptions opts;
    Expr::Manager::View * ev;
    SAT::Manager::View * satView;
    int k;
    SAT::Clauses tr;
    std::vector<ID> fairs;
    std::vector<ID> stateVars;
    std::vector<ID> inputs;
    SAT::Assignment asgn;
    int cnfSize;
    Options::Verbosity verbosity;
  };

  // Defines the basic BMC tactic.
  class FCBMCAction : public Model::Action {
  public:
    FCBMCAction(Model &m) : Model::Action(m) {
      COIAttachment::Factory caf;
      requires(Key::COI, &caf);
      ExprAttachment::Factory eaf;
      requires(Key::EXPR, &eaf);
      ProofAttachment::Factory paf;
      requires(Key::PROOF, &paf);
      CNFAttachment::Factory cnfaf;
      requires(Key::CNF, &cnfaf);
    }
    virtual void exec() {
      FCBMCOptions opts(options());
      FCBMC fcbmc(model(), opts);
      int timeout = (model().options().count("fcbmc_timeout")) ?
                     model().options()["fcbmc_timeout"].as<int>() : -1;

      int bound = (model().options().count("fcbmc_bound")) ?
                   model().options()["fcbmc_bound"].as<int>() : -1;

      MC::ReturnValue rv = fcbmc.check(timeout, bound);
      if(rv.returnType != MC::Unknown) {
        ProofAttachment * pat = (ProofAttachment *) model().attachment(Key::PROOF);
        if(rv.returnType == MC::Proof) {
          pat->setConclusion(0);
        }
        else {
          pat->setConclusion(1);
        }
      }
    }
  private:
    static ActionRegistrar action;
  };
}

#endif /* _FCBMC_ */
