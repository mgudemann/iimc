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

#ifndef _BMC_
#define _BMC_

/** @file BMC.h */

#include <boost/program_options.hpp>

#include "CNFAttachment.h"
#include "COI.h"
#include "Expr.h"
#include "ExprAttachment.h"
#include "IC3.h"
#include "Model.h"
#include "MC.h"
#include "ProofAttachment.h"
#include "RchAttachment.h"

/** namespace of BMC */
namespace BMC {
  struct BMCOptions {
    BMCOptions() : timeout(-1), sim(false), useCOI(true), printCex(false), constraints(NULL), iictl(false), silent(false), proofProc(IC3::STRENGTHEN) {}
    size_t lo;
    size_t * bound;
    int timeout;
    bool sim;
    SAT::Clauses fwd;
    SAT::Clauses bwd;
    SAT::Clauses extra_pi;
    bool useCOI;
    bool printCex;
    std::vector<SAT::Clauses> * constraints;
    bool iictl;
    SAT::Clauses * iictl_clauses;
    bool silent;
    IC3::ProofProcType proofProc;
  };

  // Procedure that performs BMC on the given model with the given bound.
  MC::ReturnValue check(Model &model, const BMCOptions & opts, std::vector<Transition> * cexTrace = NULL,
                        std::vector< std::vector<ID> > * proofCNF = NULL);

  // Defines the basic BMC tactic.
  class BMCAction : public Model::Action {
  public:
    BMCAction(Model &m) : Model::Action(m) {
      COIAttachment::Factory caf;
      requires(Key::COI, &caf);
      ExprAttachment::Factory eaf;
      requires(Key::EXPR, &eaf);
      ProofAttachment::Factory paf;
      requires(Key::PROOF, &paf);
      RchAttachment::Factory raf;
      requires(Key::RCH, &raf);
      CNFAttachment::Factory cnfaf;
      requires(Key::CNF, &cnfaf);
      AIGAttachment::Factory aaf;
      requires(Key::AIG, &aaf);
    }
    virtual void exec();
  };
}

#endif /* _BMC_ */
