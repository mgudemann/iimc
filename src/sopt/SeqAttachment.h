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

#ifndef _SeqAttachment_
#define _SeqAttachment_

/** @file SeqAttachment.h */

#include "Model.h"

/**
 * A class to share information between sequential-optimization modules.
 */
class SeqAttachment : public Model::Attachment {
public:
  SeqAttachment(Model& model) : Model::Attachment(model) { }
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
  //trueID or falseID
  //3) If latch is equivalent to another, the mapped value would be the ID of
  //the latch it is equivalent to
  std::unordered_map<ID, ID> optimized;

  std::vector<ID> initialConditions;
  std::vector<ID> inputs;
  std::vector<ID> stateVars;
  std::vector<ID> nextStateFns;

protected:
  SeqAttachment* clone() const { return new SeqAttachment(*this); }

};

#endif // _SeqAttachment_

