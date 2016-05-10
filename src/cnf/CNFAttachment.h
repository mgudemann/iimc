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

#ifndef CNFATTACHMENT_H
#define CNFATTACHMENT_H

#include <vector>
#include "ExprAttachment.h"
#include "Model.h"
#include "SimplifyCNF.h"

class CNFAttachment : public Model::Attachment
{
public:
  CNFAttachment(Model& model);

  CNFAttachment(const CNFAttachment& other, Model & model)
    : Model::Attachment(other, model), cnf(other.cnf), _last_npi(0)
  { }

  virtual void build();
  
  virtual Key::Type key() const { return Key::CNF; }

  virtual std::string string(bool includeDetails = false) const;

  class Factory : public Model::AttachmentFactory
  {
  public:
    virtual CNFAttachment* operator()(Model& model)
    {
      return new CNFAttachment(model);
    }
  };

  const std::vector<std::vector<ID> >& getCNF(Expr::Manager::View * ev = NULL) //const
  { 
    ExprAttachment const * const eat = (ExprAttachment const *) _model.constAttachment(Key::EXPR);
    ID npi = eat->outputFnOf(eat->outputs()[0]);
    _model.constRelease(eat);
    if (npi != _last_npi) {
      _last_npi = npi;
      Expr::Manager::View * view = ev ? ev : model().newView();
      ID pi = view->apply(Expr::Not, npi);
      cnf.clear();
      cnf.insert(cnf.end(), _core_cnf.begin(), _core_cnf.end());
      //if(_model.options().count("cnf_wilson"))
      //  Expr::wilson(*view, pi, cnf);
      //else
        Expr::tseitin(*view, pi, cnf);
      //SAT::Clauses simpCNF;
      //if(_model.verbosity() > Options::Terse)
      //  std::cout << "CNF before simp " << cnf.size() << std::endl;
      //CNF::simplify(_model, cnf, simpCNF, eat->inputs(), eat->stateVars(), eat->nextStateFns());
      //cnf = simpCNF;
      //if(_model.verbosity() > Options::Terse)
      //  std::cout << "CNF after simp " << cnf.size() << std::endl;
      if (!ev)
        delete view;
    }
    return cnf; 
  }

  const std::vector<std::vector<ID> > & getPlainCNF() const
  {
    return _core_cnf;
  }

  const std::vector<std::vector<ID> > & getPlainCNFNoConstraints() const
  {
    return _core_cnf_no_constraints;
  }

  const std::vector<std::vector<ID> > getCNFNoRoots() const
  {
    std::vector<std::vector<ID> > result(cnf);
    // drop last entry because it is the root
    result.resize(result.size()-1);
    return result;
  }

  const std::vector<ID> & getRoots() const
  { return roots; }

  Expr::IDMap satIdOfId;

protected:
  virtual CNFAttachment* clone(Model & model) const
  { return new CNFAttachment(*this, model); }
private:
  void techMap(const ExprAttachment * eat, Expr::Manager::View * view, std::vector<ID>& latches, std::vector<ID>& inputs, std::vector<ID>& fns, std::vector<std::vector<ID> >& _cnf);
  void tseitin(const ExprAttachment * eat, Expr::Manager::View * view, std::vector<ID>& latches, std::vector<ID>& inputs, std::vector<ID>& fns, std::vector<std::vector<ID> >& _cnf);
  void wilson(const ExprAttachment * eat, Expr::Manager::View * view, std::vector<ID>& latches, std::vector<ID>& inputs, std::vector<ID>& fns, std::vector<std::vector<ID> >& _cnf);
  void nice(const ExprAttachment * eat, Expr::Manager::View * view, std::vector<ID>& latches, std::vector<ID>& inputs, std::vector<ID>& fns, std::vector<std::vector<ID> >& _cnf);
  std::vector<std::vector<ID> > cnf;
  std::vector<ID> roots;
  void transitionRelation(AIGAttachment& aat, const ExprAttachment& eat);

  ID _last_npi;
  std::vector<std::vector<ID> > _core_cnf, _core_cnf_no_constraints, _pi_cnf;
};

#endif
