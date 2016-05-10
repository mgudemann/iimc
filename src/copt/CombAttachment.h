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

#ifndef _CombAttachment_
#define _CombAttachment_

/** @file CombAttachment.h */

#include "Model.h"

/**
 * A class to share information between combinational-logic modules.
 */
class CombAttachment : public Model::Attachment {
public:
  CombAttachment(Model& model);
  CombAttachment(const CombAttachment & from, Model& model) :
    Model::Attachment(from, model),
    _simplificationEffort(from._simplificationEffort),
    _numEquivalences(from._numEquivalences),
    _unusedTime(from._unusedTime) {
  }
  Key::Type key() const { return Key::COMB; }
  void build() { 
    if (model().verbosity() > Options::Silent)
      std::cout << "CombAttachment: building" << std::endl;
    _simplificationEffort = None;
    _numEquivalences = 0;
    _unusedTime = 0;
  }
  std::string string(bool includeDetails = false) const;
  enum Effort {None, Cursory, Medium, Thorough, Complete};
  Effort& simplificationEffort() { return _simplificationEffort; }
  const Effort& simplificationEffort() const { return _simplificationEffort; }
  int& numEquivalences() { return _numEquivalences; }
  const int& numEquivalences() const { return _numEquivalences; }
  int64_t& unusedTime() { return _unusedTime; }
  const int64_t& unusedTime() const { return _unusedTime; }

  class Factory : public Model::AttachmentFactory {
  public:
    virtual CombAttachment * operator()(Model & model) {
      return new CombAttachment(model);
    }
  };

protected:
  CombAttachment* clone(Model & model) const { return new CombAttachment(*this, model); }

private:
  Effort _simplificationEffort;
  int _numEquivalences;
  //Unused time from previous combinational simplification method in
  //microseconds
  int64_t _unusedTime;
};

#endif // _CombAttachment_

