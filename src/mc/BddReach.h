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

#ifndef _BddReach_
#define _BddReach_

/** @file BddReach.h */

#include "Model.h"
#include "BddTrAttachment.h"
#include "ProofAttachment.h"
#include "RchAttachment.h"

typedef boost::program_options::variables_map options_map;

/**
 * Class of forward and backward reachability analysis.
 */
class BddReachAction : public Model::Action {
public:
  BddReachAction(Model & m) : Model::Action(m) {
    BddTrAttachment::Factory b;
    requires(Key::BDD_TR, &b);
    ProofAttachment::Factory p;
    requires(Key::PROOF, &p);
    RchAttachment::Factory r;
    requires(Key::RCH, &r);
  }
};


/**
 * Action to perform forward reachability analysis.
 */
class BddFwReachAction : public BddReachAction {
public:
  BddFwReachAction(Model & m) : BddReachAction(m) {}
  virtual void exec();

  void doFwReachability(Model & model);
private:
  void printFwCex(BddTrAttachment const *tat,
                  std::vector<BDD> const & frontiers,
                  BDD badStates,
                  Options::Verbosity verbosity);
  static ActionRegistrar action;
};


/**
 * Action to perform backward reachability analysis.
 */
class BddBwReachAction : public BddReachAction {
public:
  BddBwReachAction(Model & m) : BddReachAction(m) {}
  virtual void exec();

  void doBwReachability(Model & model);
private:
  static ActionRegistrar action;
};

#endif // _BddReach_
