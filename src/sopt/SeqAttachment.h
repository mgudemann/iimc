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

#ifndef _SeqAttachment_
#define _SeqAttachment_

/** @file SeqAttachment.h */

#include "Model.h"

/**
 * A class to store information required to reverse sequential
 * optimizations.  This reversal is necessary when fleshing out a
 * counterexample for the original model from a counterexample for
 * the optimized model produced by some proof engine.
 */
class SeqAttachment : public Model::Attachment {
public:
  SeqAttachment(Model& model) :
    Model::Attachment(model), unrollings(1), decoded(false) {
    ExprAttachment::Factory ef;
    requires(Key::EXPR, &ef);
  }
  SeqAttachment(const SeqAttachment& from, Model& model) : 
    Model::Attachment(from, model), optimized(from.optimized),
    unrollings(from.unrollings), decoded(from.decoded) {
  }
  Key::Type key() const { return Key::SEQ; }
  void build() { 
    if (model().verbosity() > Options::Silent)
      std::cout << "SeqAttachment: building" << std::endl;
  }
  std::string string(bool includeDetails = false) const;

  class Factory : public Model::AttachmentFactory {
  public:
    virtual SeqAttachment * operator()(Model & model) {
      return new SeqAttachment(model);
    }
  };
  //The set of latches that have been optimized by some sequential optimization
  //action, and what they have been optimized to:
  //1) If latch dropped (COI reduction), the mapped value would be the same
  //2) If latch is constant (StuckAt detection), the mapped value would be
  //   trueID or falseID
  //3) If latch is equivalent to another, the mapped value would be the ID of
  //   the latch it is equivalent to
  // Every action that drops a latch must update this map.
  // In theory this map could be used to save more complex dependencies for
  // dropped latches.  Other parts of iimc are not prepared for this more
  // complex use.
  std::unordered_map<ID, ID> optimized;

  // Number of unrollings.  This number is 1 unless phase abstraction was
  // performed.
  int unrollings;
  // Info to allow phase abstraction to be undone.
  // maps each cycle input to a pair <original_input, cycle>
  std::unordered_map<ID, std::pair<ID, unsigned int> > cycleInputs;
  // Final cycle may overshoot bad-state. Must check cycle outputs to see 
  // how far to unroll. TODO
  std::unordered_map<ID, std::vector<ID> > outputToCycleOutputs;

  // Information about the decoding.  Currently, only backward decoding is
  // supported.
  bool decoded; // false unless backward decoding took place.
  // maps each mapped latch to the corresponding suppressed primary input
  std::unordered_map<ID,ID> latchToInput;
  std::vector<ID> decodedInputs;
  std::vector<ID> decodedStateVars;
  std::vector<ID> decodedInitialConditions;
  std::vector<ID> decodedNextStateFns;
  std::vector<ID> decodedConstraintFns;

protected:
  SeqAttachment* clone(Model & model) const { return new SeqAttachment(*this, model); }

};

#endif // _SeqAttachment_

