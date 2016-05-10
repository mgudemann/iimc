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

#ifndef _KLIVE_
#define _KLIVE_

/** @file KLive.h **/

#include "ExprAttachment.h"
#include "MC.h"
#include "Model.h"
#include "options.h"
#include "ProofAttachment.h"

class KLive {
public:
  KLive(Model & m, Options::Verbosity verbosity = Options::Silent);
  ~KLive();

  MC::ReturnValue check(int timeout, int bound, std::string klive_backend);

private:
  Model & model;     //Reference to original model
  Model safetyModel; //A clone of the original model for performing the safety queries
  Options::Verbosity verbosity;
  int k;            //Next k to examine
  ID safetyTarget;  //Target for invariant model checker
  std::unordered_map< ID, std::pair<bool, bool> > persistentSignals;
  std::vector<SAT::Clauses> constraints;
  Expr::Manager::View * view;
};

class KLiveAction : public Model::Action {
public:
  KLiveAction(Model & m,
#ifndef DISABLE_ZCHAFF
              std::string klive_backend = std::string("zchaff")
#else
              std::string klive_backend = std::string("minisat")
#endif
              )
    : Model::Action(m), klive_backend(klive_backend) {
    ExprAttachment::Factory eaf;
    requires(Key::EXPR, &eaf);
    RchAttachment::Factory raf;
    requires(Key::RCH, &raf);
    ProofAttachment::Factory paf;
    requires(Key::PROOF, &paf);
  }

  virtual void exec();

private:
  static ActionRegistrar action;
  std::string klive_backend;
};

#endif
