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

#ifndef _ProofAttachment_
#define _ProofAttachment_

/** @file ProofAttachment.h */

#include "ExprAttachment.h"
#include "Model.h"

struct Transition {
  Transition() { };
  Transition(const std::vector<ID> & _state, const std::vector<ID> & _inputs) :
      state(_state), inputs(_inputs) { };
  std::vector<ID> state;
  std::vector<ID> inputs;
};

struct Lasso {
  std::vector<Transition> stem; //Excludes all states in the loop
  std::vector<Transition> loop;
};

/**
 * A class to collect information about the proof.
 */
class ProofAttachment : public Model::Attachment {
public:
  ProofAttachment(Model& model) : Model::Attachment(model), _hasConclusion(false) {
    ExprAttachment::Factory eaf;
    requires(Key::EXPR, &eaf);
  }

  Key::Type key() const { return Key::PROOF; }
  void build() {
    Options::Verbosity verbosity = _model.verbosity();
    if (verbosity > Options::Silent)
      std::cout << "Building proof attachment for model "
                << _model.name() << std::endl;
  }
  std::string string(bool includeDetails = false) const;
  bool hasConclusion() const { return _hasConclusion; }
  int conclusion() const { return _safe; }
  void printConclusion(std::ostream& os = std::cout) const;
  void setConclusion(const int conclusion) { 
    assert(conclusion == 0 || conclusion == 1);
    _safe = conclusion; 
    _hasConclusion = true; 
  }
  void restoreDroppedLatches();
  void printCex(std::ostream& os = std::cout) const;
  void setCex(const std::vector<Transition> & cex) {
    _cex = cex;
  }

  void printProof(std::ostream& os = std::cout) const;
  void addEquivalenceInfo();
  void setProof(const std::vector< std::vector<ID> > & proof) {
    _proof = proof;
  }


  class Factory : public Model::AttachmentFactory {
  public:
    virtual ProofAttachment * operator()(Model & model) {
      return new ProofAttachment(model);
    }
  };

protected:
  ProofAttachment* clone() const { return new ProofAttachment(*this); }

private:
  bool _hasConclusion;
  int _safe;
  std::vector<Transition> _cex;
  std::vector< std::vector<ID> > _proof;
};

#endif // _ProofAttachment_
