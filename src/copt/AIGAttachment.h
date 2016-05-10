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

#ifndef _AIGAttachment_
#define _AIGAttachment_

/** @file AIGAttachment.h */

#include "Model.h"
#include "AIG.h"
#include "Expr.h"
#include <vector>

/**
 * A class to attach AIG to a model.
 */
class AIGAttachment : public Model::Attachment {
public:
  AIGAttachment(Model &model);
  AIGAttachment(const AIGAttachment &from);
  AIGAttachment& operator=(AIGAttachment &rhs);

  inline Key::Type key() const { return Key::AIG; }
  std::string string(bool includeDetails = false) const;
  virtual void build();
  void AIG2Expr();
  void AIGOutputs(std::vector<Opt::NodeRef>& out) const;

  class Factory : public Model::AttachmentFactory {
  public:
    virtual AIGAttachment * operator()(Model & model) {
      return new AIGAttachment(model);
    }
  };

  // This is for some decent reason!
  Opt::AIG aig;
  Opt::RefIDMap ref2id;
  Opt::IDRefMap id2ref;
private:
  void buildAIG(Model &model);
  ID IDOf(Opt::NodeRef ref, Expr::Manager::View &v, Opt::IDRefMap& newId2ref,
      Opt::RefIDMap& newRef2id);
};

#endif
