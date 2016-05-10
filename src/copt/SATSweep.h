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

#ifndef _SATSweep_
#define _SATSweep_

/** @file SATSweep.h */

#include <list>
#include <vector>

#include "Model.h"
#include "options.h"
#include "AIGAttachment.h"
#include "CombAttachment.h"

namespace Opt
{

//Maximum SAT solver timeout in SAT sweeping in seconds
#define MAX_SATSOLVER_TIMEOUT 10.0

struct Stats {
  Stats() : sweepTime(0.0), numMerges(0), numSatQueries(0), numSatSatQueries(0),
      numUnsatSatQueries(0), numIgnoredEquivs(0), complete(false),
      timeout(-1), totalTime(-1) { }
  double sweepTime;
  int numMerges;
  int initialNodes;
  int finalNodes;
  int numSatQueries;
  int numSatSatQueries;
  int numUnsatSatQueries;
  int numIgnoredEquivs;
  bool complete;
  int64_t timeout;
  int64_t startTime;
  int64_t totalTime;
};

/**
 * Performs SAT sweeping on the model.
 */
void satSweep(Model& model, Stats& stats);

} //namespace Opt

namespace Action {

/**
 * An action to perform AIG-based SAT sweeping
 */
class SATSweepAction : public Model::Action {
public:
  SATSweepAction(Model& model) : Model::Action(model) {
    CombAttachment::Factory combFactory;
    AIGAttachment::Factory aigFactory;
    requires(Key::COMB, &combFactory);
    requires(Key::AIG, &aigFactory);
  }
  virtual void exec();
private:
  static ActionRegistrar action;
};

} //namespace Action

#endif // _SATSweep_
