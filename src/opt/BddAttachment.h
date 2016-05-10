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

#ifndef _BddAttachment_
#define _BddAttachment_

/** @file BddAttachment.h */

#include "ExprAttachment.h"
#include "CombAttachment.h"
#include "ExprBdd.h"
#include "Model.h"
#include "options.h"

/**
 * A class to attach BDDs to a model.
 */
class BddAttachment : public Model::Attachment {
  friend class BddSweepAction;
public:
  BddAttachment(Model& model) : Model::Attachment(model) {
    ExprAttachment::Factory ef;
    requires(Key::EXPR, &ef);
    CombAttachment::Factory cf;
    requires(Key::COMB, &cf);
  }
  /** Copy constructor. */
  BddAttachment(const BddAttachment& from) : 
    Model::Attachment(from),
    _map(from._map),
    _order(from._order)
  {}
  BddAttachment& operator=(BddAttachment& rhs) {
    if (&rhs != this) {
      _model = rhs._model;
      if (rhs._ts == 0)
	_ts = 0;
      else
	_ts = Model::newTimestamp();
      _map = rhs._map;
      _order = rhs._order;
    }
    return *this;
  }
  /** Return the key of this type of attachment. */
  Key::Type key() const { return Key::BDD; }
  std::string string(bool includeDetails = false) const;
  bool hasBdds() const { return _map.size() > 0; }
  bool hasBdd(ID id) const { return _map.find(id) != _map.end(); }
  BDD bdd(ID id) const;
  ID ithVar(unsigned int i) const;
  std::string orderString() const;
  std::vector<ID> const & order() const { return _order; }
  const std::unordered_map<ID, int>& auxiliaryVars() const { return _auxVar; }
  void build();
  BDD cubeToBdd(const std::vector<ID> & cube, Expr::Manager::View& _view) const;
  BDD cnfToBdd(const std::vector< std::vector<ID> > & cnf, Expr::Manager::View& _view) const;
  void countStates(const std::vector< std::vector<ID> > & cnf, Expr::Manager::View& _view) const;

  class Factory : public Model::AttachmentFactory {
  public:
    virtual BddAttachment * operator()(Model & model) {
      return new BddAttachment(model);
    }
  };

protected:
  BddAttachment* clone() const { return new BddAttachment(*this); }
private:
  void buildVariableOrder(Expr::Manager::View *v, ExprAttachment const *eat, 
                          std::unordered_map<ID, int>& orderMap,
                          bool noNsVars = false);
  void configureBddManager(bool sweep = false) const;
  void collectRoots(ExprAttachment const *eat, std::vector<ID>& roots) const;
  void updateExprAttachment(ExprAttachment *eat, const std::vector<ID>& roots) const;
  std::vector<ID> readOrder(Expr::Manager::View &v, const std::string& filename,
                            std::unordered_map<ID, bool> leaves);

  Expr::IdBddMap _map;
  std::vector<ID> _order;
  std::unordered_map<ID, int> _auxVar;
};

ID exprOf(BDD f, Expr::Manager::View& v, std::vector<ID> const & order);

/**
 * Class to build BDDs for the model.
 */
class BddBuildAction : public Model::Action {
public:
  BddBuildAction(Model& m) : Model::Action(m) {
    BddAttachment::Factory baf;
    requires(Key::BDD, &baf);
  }
  void exec() {}
private:
  static ActionRegistrar action;
};


/**
 * Class to perform BDD sweeping.
 */
class BddSweepAction : public Model::Action {
public:
  BddSweepAction(Model& m) : Model::Action(m) {
    ExprAttachment::Factory eaf;
    requires(Key::EXPR, &eaf);
    CombAttachment::Factory caf;
    requires(Key::COMB, &caf);
  }
  void exec();
private:
  static ActionRegistrar action;
};

#endif // _BddAttachment_
