/* -*- C++ -*- */

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

#ifndef _FSIS_
#define _FSIS_

/** @file FSIS.h **/

#include "IC3.h"

#include <boost/program_options.hpp>

/** namespace of FSIS */
namespace FSIS {

  MC::ReturnValue check(Model & m, IC3::IC3Options & opts,
                        std::vector<Transition> * cex = NULL,
                        std::vector< std::vector<ID> > * proofCNF = NULL,
                        std::vector<ID> * gprop = NULL,
                        bool useRAT = true);


  class FSISAction : public Model::Action {
  public:
    FSISAction(Model & m) : Model::Action(m) {
      ExprAttachment::Factory eaf;
      requires(Key::EXPR, &eaf);
      COIAttachment::Factory caf;
      requires(Key::COI, &caf);
      RchAttachment::Factory raf;
      requires(Key::RCH, &raf);
      ProofAttachment::Factory paf;
      requires(Key::PROOF, &paf);
      CNFAttachment::Factory cnfaf;
      requires(Key::CNF, &cnfaf);
    }
    virtual void exec() {
      IC3::IC3Options opts(options(), false, false, this);
      opts.ctgs = 0;
      MC::ReturnValue rv;
      std::vector<Transition> cex;
      std::vector< std::vector<ID> > proof;
      rv = FSIS::check(model(), opts, opts.printCex ? &cex : NULL,
          opts.printProof ? &proof : NULL);
      auto pat = model().attachment<ProofAttachment>(Key::PROOF);
      if (rv.returnType != MC::Unknown) {
        if (model().verbosity() > Options::Silent)
          std::cout << "Conclusion found by FSIS." << std::endl;
        if (rv.returnType == MC::Proof) {
          pat->setConclusion(0);
          if(opts.printProof) {
            pat->setProof(proof);
          }
        }
        else if (rv.returnType == MC::CEX) {
          if(opts.printCex) {
            pat->setCex(cex);
          }
          pat->setConclusion(1);
        }
      }
      model().release(pat);
    }
  private:
    static ActionRegistrar action;
  };


}

#endif
