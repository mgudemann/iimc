/********************************************************************
Copyright (c) 2010-2012, Regents of the University of Colorado

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

#include "CNFAttachment.h"
#include "SimplifyCNF.h"
#include "TechMapCNF.h"
#include "NiceDAG.h"
#include "StringTR.h"
#include <cfloat>

using namespace std;

namespace
{

  enum CNFModet {TSEITIN, WILSON, TECHMAP, NICE};

  CNFModet getMode(Model& model)
  {
    if(model.options().count("cnf_techmap")) {
      //assert (false);
      return TECHMAP;
    } else if(model.options().count("cnf_nice")) {
      assert (false);
      return NICE;
    } else if(model.options().count("cnf_wilson")) {
      return WILSON;
    } else {
      return TSEITIN;
    }
  }

}

CNFAttachment::CNFAttachment(Model& model) : Model::Attachment(model), _last_npi(0)
{
  switch(getMode(model)) {
    case TECHMAP:
      {
        AIGAttachment::Factory af;
        ExprAttachment::Factory ef;
        requires(Key::AIG, &af);
        requires(Key::EXPR, &ef);
        break;
      }
    case NICE:
    case WILSON:
    case TSEITIN:
      {
        ExprAttachment::Factory f;
        requires(Key::EXPR, &f);
        break;
      }
  }
}


namespace {
  ::Opt::NodeRef aigEquiv(::Opt::AIG& aig, ::Opt::NodeRef a, ::Opt::NodeRef b)
  {
    ::Opt::NodeRef n1 = ::Opt::refOf(aig.addNode(a,b), true);
    ::Opt::NodeRef n2 = ::Opt::refOf(aig.addNode(a,n1), true);
    ::Opt::NodeRef n3 = ::Opt::refOf(aig.addNode(b,n1), true);
    return ::Opt::refOf(aig.addNode(n2,n3), false);
  }
} // namespace anonymous

void CNFAttachment::techMap(const ExprAttachment * eat, Expr::Manager::View * view, vector<ID>& latches, vector<ID>& inputs, vector<ID>& fns, vector<vector<ID> >& _cnf)
{
  // get options
  unsigned k = _model.options()["tmcnf_k"].as<unsigned>();
  unsigned l = _model.options()["tmcnf_l"].as<unsigned>();
  unsigned refinements = _model.options()["tmcnf_refinements"].as<unsigned>();
  double timeOut = DBL_MAX;
  if(_model.options().count("cnf_timeout")) {
    timeOut = _model.options()["cnf_timeout"].as<double>();
  }

  // print status
  if (model().verbosity() > Options::Silent)
    cout << "CNFAttachment: building CNF using Technology Mapping (k = " << k << ", l = " << l << ")\n";
  
  // get mutable aig attachments
  const AIGAttachment* aigat = static_cast<const AIGAttachment *>(_model.constAttachment(Key::AIG));
  AIGAttachment cpaigat(*aigat);

  // save off initial AIG size
  unsigned aig_init_size = cpaigat.aig.size();

  // get the IDs of the primed latches
  vector<ID> primed;
  for(unsigned i = 0; i < latches.size(); ++i) {
    primed.push_back(view->prime(latches[i]));
  }
  
  // add the primed latches to the AIG as additional inputs
  vector< ::Opt::NodeRef> primedaig;
  for(unsigned i = 0; i < primed.size(); ++i) {
    ::Opt::NodeIndex ni = cpaigat.aig.addNode();
    ::Opt::NodeRef nr = ::Opt::refOf(ni, false);
    cpaigat.id2ref[primed[i]] = nr;
    cpaigat.ref2id[nr] = primed[i];
    primedaig.push_back(nr);
  }

  // make aig nodes of fns
  vector< ::Opt::NodeRef> fnsaig;
  for(unsigned i = 0; i < fns.size(); ++i) {
    ::Opt::IDRefMap::const_iterator it = cpaigat.id2ref.find(fns[i]);
    assert(it != cpaigat.id2ref.end());
    fnsaig.push_back(it->second);
  }

  // add equivalences to the aig
  std::vector< ::Opt::NodeRef> conjuncts;
  assert(fnsaig.size() == primedaig.size());
  for(unsigned i = 0; i < fnsaig.size(); ++i) {
    ::Opt::NodeRef nr = ::aigEquiv(cpaigat.aig, primedaig[i], fnsaig[i]);
    //std::cout << nr << std::endl;
    conjuncts.push_back(nr);
  }

  // add negation of output 0 to conjuncts
  vector<ID> outputs(eat->outputs());
  ::Opt::IDRefMap::const_iterator outit = cpaigat.id2ref.find(eat->outputFnOf(outputs[0]));
  assert(outit != cpaigat.id2ref.end());
  conjuncts.push_back(::Opt::invert(outit->second));

  // conjoin the conjuncts in the AIG
  for(unsigned i = 0; i < conjuncts.size() - 1; i += 2) {
    ::Opt::NodeIndex ind = cpaigat.aig.addNode(conjuncts[i], conjuncts[i+1]);
    ::Opt::NodeRef ref = ::Opt::refOf(ind, false);
    conjuncts.push_back(ref);
  }

  // output to compute
  std::vector< ::Opt::NodeRef> output(1);
  output[0] = conjuncts[conjuncts.size()-1];


  // run tech mapping
  typedef std::vector< std::vector< ::Opt::NodeRef> > AIGCNF;
  AIGCNF aigcnf;
  CNF::techMap(model().verbosity(), cpaigat, k, l, refinements, output, aigcnf, timeOut, true);

  // convert the aig cnf to ID cnf

  // keep track of added variables to the AIG and how they map to IDs in Expr
  std::map< ::Opt::NodeIndex, ID> newvars;
  _cnf.resize(0);
  unsigned clause = 0;
  // iterate over clauses
  for(AIGCNF::iterator i = aigcnf.begin(); i != aigcnf.end(); ++i, ++clause) {
    // add a new element to the end of _cnf
    _cnf.resize(_cnf.size()+1);
    // iterate over literals within clauses
    for(::std::vector< ::Opt::NodeRef>::iterator j = i->begin(); j != i->end(); ++j) {
      ID lit;
      if(*j == 0) {
        // map to false
        lit = view->bfalse();
      } else if(*j == 1) {
        // map to true
        lit = view->btrue();
      } else if(cpaigat.aig[ ::Opt::indexOf(*j)].isVar()) {
        // use existing inputs
        lit = cpaigat.ref2id.find(::Opt::refOf(::Opt::indexOf(*j), false))->second;
        if(::Opt::isNot(*j)) {
          // negate input if necessary
          lit = view->apply(::Expr::Not, lit);
        }
      } else {
        std::map< ::Opt::NodeIndex, ID>::iterator fj = newvars.find(::Opt::indexOf(*j));
        if(fj == newvars.end()) {
          // create new variable
          ::std::stringstream ss;
          ss << "tmv" << *j;
          lit = view->newVar(ss.str());
          newvars[::Opt::indexOf(*j)] = lit;
        } else {
          // use existing var
          lit = fj->second;
        }
        if(::Opt::isNot(*j)) {
          // negate variable if necessary
          lit = view->apply(::Expr::Not, lit);
        }
      }

      // add literal to current clause
      _cnf[clause].push_back(lit);
    }
  }


  cpaigat.aig.resize(aig_init_size);

  _model.constRelease(aigat);
}

void CNFAttachment::nice(const ExprAttachment * eat, Expr::Manager::View * view, vector<ID>& latches, vector<ID>& inputs, vector<ID>& fns, vector<vector<ID> >& _cnf)
{
  if (model().verbosity() > Options::Silent)
    cout << "CNFAttachment: building CNF using NiceDAGs translation\n";

  // construct transition relation
  vector<ID> tr;
  for (unsigned int i = 0; i < latches.size(); ++i)
    tr.push_back(view->apply(Expr::Equiv, 
                             view->prime(latches[i]),
                             fns[i]));

  // append property
  tr.push_back(view->apply(Expr::Not, eat->outputFnOf(eat->outputs()[0])));

  //cout << "Before:" << endl;

  //cout << CNF::stringTR(view, tr) << endl;

  /*
  int found = CNF::niceDAG(view, tr);

  cout << "After:" << endl;
  cout << CNF::stringTR(view, tr) << endl;

  cout << "Found " << found << " ITEs" << endl;
  */

  unsigned k = _model.options()["nice_k"].as<unsigned>();


  CNF::niceCNF(model().verbosity(), view, k, tr, _cnf);

  //assert(false);
  //exit(1);
}

void CNFAttachment::tseitin(const ExprAttachment * eat, Expr::Manager::View * view, vector<ID>& latches, vector<ID>& inputs, vector<ID>& fns, vector<vector<ID> >& _cnf)
{
  if (model().verbosity() > Options::Silent)
    cout << "CNFAttachment: building CNF using Tseitin translation\n";

  // construct transition relation
  vector<ID> tr;
  for (unsigned int i = 0; i < latches.size(); ++i)
    tr.push_back(view->apply(Expr::Equiv, 
                             view->prime(latches[i]),
                             fns[i]));
  vector<ID> constraints = eat->constraints();
  //Modified by Zyad 112211
  //tr.insert(tr.end(), constraints.begin(), constraints.end());
  //Expr::primeFormulas(*view, constraints);
  //tr.insert(tr.end(), constraints.begin(), constraints.end());
  for(vector<ID>::const_iterator it = constraints.begin();
      it != constraints.end(); ++it) {
    if(*it != view->btrue()) { //Ignore trivial constraints
      tr.push_back(*it);
      tr.push_back(Expr::primeFormula(*view, *it));
    }
  }

  // convert to CNF
  Expr::tseitin(*view, tr, _cnf);

  // convert property separately
  if (eat->outputs().size() > 0) {
    ID npi = eat->outputFnOf(eat->outputs()[0]);
    _last_npi = npi;
    ID pi = view->apply(Expr::Not, npi);
    Expr::tseitin(*view, pi, _pi_cnf);
  }
}


void CNFAttachment::wilson(const ExprAttachment * eat, Expr::Manager::View * view, vector<ID>& latches, vector<ID>& inputs, vector<ID>& fns, vector<vector<ID> >& _cnf)
{
  if (model().verbosity() > Options::Silent)
    cout << "CNFAttachment: building CNF using Wilson translation\n";

  // construct transition relation
  vector<ID> tr;
  for (unsigned int i = 0; i < latches.size(); ++i)
    tr.push_back(view->apply(Expr::Equiv, 
                             view->prime(latches[i]),
                             fns[i]));
  vector<ID> constraints = eat->constraints();
  for(vector<ID>::const_iterator it = constraints.begin();
      it != constraints.end(); ++it) {
    if(*it != view->btrue()) { //Ignore trivial constraints
      tr.push_back(*it);
      tr.push_back(Expr::primeFormula(*view, *it));
    }
  }

  // convert to CNF
  Expr::wilson(*view, tr, _cnf);

  // convert property separately
  if (eat->outputs().size() > 0) {
    ID npi = eat->outputFnOf(eat->outputs()[0]);
    _last_npi = npi;
    ID pi = view->apply(Expr::Not, npi);
    Expr::wilson(*view, pi, _pi_cnf);
  }
}

namespace
{
  void cnf_stats(std::string prefix, vector<vector<ID> >& cnf)
  {
    // show # clauses and # lits
    unsigned lits = 0;
    for(unsigned i = 0; i < cnf.size(); ++i)
      lits += cnf[i].size();
    std::cout << prefix << " clauses: " << cnf.size() << " lits: " << lits << std::endl;
  }
}

void CNFAttachment::build()
{
  bool disable_simp = model().options().count("cnf_simp_disable");
  // create constant ExprAttachment.  It is used by all CNF conversions
  ExprAttachment const * eat = static_cast<ExprAttachment const *>(_model.constAttachment(Key::EXPR));
  vector<vector<ID> > tmp;
  vector<vector<ID> >& _cnf = disable_simp ? cnf : tmp;

  // create a view of the model
  Expr::Manager::View * view = model().newView();

  // get latches and roots
  vector<ID> latches(eat->stateVars());
  vector<ID> inputs(eat->inputs());
  vector<ID> fns(eat->nextStateFnOf(latches));

  // select the correct cnf conversion algorithm
  switch(getMode(_model)) {
    case TECHMAP:
      techMap(eat, view, latches, inputs, fns, _cnf);
      break;
    case NICE:
      nice(eat, view, latches, inputs, fns, _cnf);
      break;
    case WILSON:
      tseitin(eat, view, latches, inputs, fns, _cnf);
      if (model().verbosity() > Options::Terse)
        cnf_stats("CNFAttachment:", _cnf); 
      _cnf.clear();
      _pi_cnf.clear();
      wilson(eat, view, latches, inputs, fns, _cnf);
      break;
    case TSEITIN:
      tseitin(eat, view, latches, inputs, fns, _cnf);
      break;
  }
  if (model().verbosity() > Options::Terse)
    cnf_stats("CNFAttachment:", _cnf); 

  if(!disable_simp) {
    // optionally run CNF simplification
    CNF::simplify(_model, _cnf, cnf, inputs, latches, fns);

    if (model().verbosity() > Options::Terse)
      cnf_stats("CNFAttachment simplified:", cnf); 
  }

  _core_cnf.insert(_core_cnf.end(), cnf.begin(), cnf.end());
  if (getMode(_model) == TSEITIN || getMode(_model) == WILSON)
    cnf.insert(cnf.end(), _pi_cnf.begin(), _pi_cnf.end());

  // clean up
  delete view;
  model().constRelease(eat);
}

string CNFAttachment::string(bool includeDetails) const
{
  return "";
}
