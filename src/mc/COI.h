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

#ifndef _COI_
#define _COI_

/** @file COI.h */

#include "Expr.h"
#include "ExprAttachment.h"
#include "Key.h"
#include "Model.h"
#include "options.h"
#include "SeqAttachment.h"

#include <set>

/**
 * A value-type class that represents a stepwise and full cone of influence (COI).
 */
class COI {
public:
  typedef std::pair<std::vector<ID>::const_iterator,std::vector<ID>::const_iterator> range;
  typedef std::pair<ID, ID> IDp;
  typedef std::vector<IDp> IDpv;

  /**
   * Empty constructor, to be populated via operator=.
   */
  COI() {}

  /**
   * Constructor that yields a populated structure.  rltn is a vector
   * of pairs, each pair a latch and its function.  prop is the
   * property with respect to which the COI is being computed.
   */
  COI(Expr::Manager::View & v, ExprAttachment * const eat, std::vector<ID> props, 
      bool internal, Options::Verbosity vrb){ build(v, eat, props, internal, vrb); }

  /**
   * Returns the (converged or full) COI.
   */
  range cCOI(bool internal=false) const { 
    return kCOI(markers_.size(), internal);
  }

  /**
   * Returns the stepwise COI that is k steps away from the property.
   */
  range kCOI(unsigned int k, bool internal=false) const {
    std::vector<ID>::const_iterator begin;
    std::vector<ID>::const_iterator end;
    if (internal){
      assert(!kCOIplusInt_.empty());
      begin = kCOIplusInt_.cbegin();
      if (k >= markersInt_.size())
	end = kCOIplusInt_.cend();
      else
	end = kCOIplusInt_.cbegin() + markersInt_[k];
    }
    else{
      begin = kCOI_.cbegin();
      if (k >= markers_.size())
	end = kCOI_.cend();
      else
	end = kCOI_.cbegin() + markers_[k];
    }
    return range(begin, end);
  }

  /*
   *  Returns reference to modifiable kCOI vector.
   */
  std::vector<ID>* kCOIplusInt() {
    return &kCOIplusInt_;
  }


  /**
   * Returns the number of steps in the COI.
   */
  unsigned int size() const { return markers_.size(); }

  /**
   * Returns the number of latches in the COI.
   */
  std::vector<ID>::size_type count() const { return kCOI_.size(); }

  void build(Expr::Manager::View & v, ExprAttachment * const eat, std::vector<ID> props, bool internal, Options::Verbosity vrb);


private:
  std::vector<ID> kCOI_;
  std::vector<ID> kCOIplusInt_; // internal nodes
  std::vector<std::vector<ID>::size_type> markers_;
  std::vector<std::vector<ID>::size_type> markersInt_;
};

class COIAttachment : public Model::Attachment {
public:
  COIAttachment(Model & model) : Model::Attachment(model) {
    ExprAttachment::Factory eaf;
    requires(Key::EXPR, &eaf);
  }

  virtual void build();

  const COI & coi() const { return _coi; }

  virtual Key::Type key() const { return Key::COI; }
  virtual std::string string(bool includeDetails = false) const { return "COIAttachment"; }
  virtual COIAttachment * clone() const {
    COIAttachment * cat = new COIAttachment(model());
    cat->_coi = _coi;
    return cat;
  }

  class Factory : public Model::AttachmentFactory {
  public:
    virtual COIAttachment * operator()(Model & model) {
      return new COIAttachment(model);
    }
  };

private:
  COI _coi;
};

class COIAction : public Model::Action {
public:
  COIAction(Model & model) : Model::Action(model) {
    SeqAttachment::Factory seqFactory;
    ExprAttachment::Factory eaf;
    COIAttachment::Factory caf;
    requires(Key::SEQ, &seqFactory);
    requires(Key::EXPR, &eaf);
    requires(Key::COI, &caf);
  }

  virtual void exec();
private:
  static ActionRegistrar action;
};

#endif
