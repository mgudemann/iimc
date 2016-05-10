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

#ifndef _Fair_
#define _Fair_

/** @file Fair.h **/

#include "CNFAttachment.h"
#include "COI.h"
#include "ExprAttachment.h"
#include "IC3.h"
#include "MC.h"
#include "Model.h"
#include "ProofAttachment.h"
#include "RchAttachment.h"

#include <ostream>
#include <boost/program_options.hpp>

/** namespace of Fair */
namespace Fair {
  struct FairOptions {
  public:
    FairOptions(const boost::program_options::variables_map & opts) : 
      ic3_opts(opts), k(0) {
      k = opts["fair_k"].as<int>();
      printCex = false;
      constraints = NULL;
      proofProc = IC3::STRENGTHEN;
      global_last = false;
      iictl = false;
    }
    IC3::IC3Options ic3_opts;
    int k;
    bool printCex;
    SAT::Clauses * constraints;
    IC3::ProofProcType proofProc;
    bool global_last;
    bool iictl;
  };

  MC::ReturnValue check(Model & m, FairOptions & opts, Lasso * lasso = NULL,
                        std::vector<SAT::Clauses> * proofs = NULL);

  MC::ReturnValue fairPath(Model & m, FairOptions & opts, Lasso * lasso = NULL,
                           std::vector<SAT::Clauses> * proofs = NULL);

  class FairAction : public Model::Action {
  public:
    FairAction(Model & m, FairOptions * _opts = NULL) : Model::Action(m), _opts(_opts) {
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
    }
    virtual void exec() {
      FairOptions opts(options());
      if (_opts) opts = *_opts;

      MC::ReturnValue rv = check(model(), opts);
      if (rv.returnType != MC::Unknown) {
        ProofAttachment * pat = (ProofAttachment *) model().attachment(Key::PROOF);
        if (rv.returnType == MC::Proof)
          pat->setConclusion(0);
        else if (rv.returnType == MC::CEX)
          pat->setConclusion(1);
        model().release(pat);
      }
    }
  private:
    FairOptions * _opts;
  };

}

#endif
