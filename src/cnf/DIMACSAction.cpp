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

#include "DIMACSAction.h"
#include "AIGAttachment.h"
#include "ExprAttachment.h"
#include "NiceDAG.h"
#include "TechMapCNF.h"
#include<vector>
#include<cfloat>

using namespace std;

namespace {

  enum CNFModet {TSEITIN, TECHMAP, NICE};

  CNFModet getMode(Model& model)
  {
    if(model.options().count("cnf_techmap")) {
      return TECHMAP;
    } else if(model.options().count("cnf_nice")) {
      return NICE;
    } else {
      return TSEITIN;
    }
  }

  struct inttoint {
    long operator()(long l) {
      return l;
    }
  };

  struct reftoint {
    long operator()(::Opt::NodeRef r) {
      return (long)(UIGET(r));
    }
  };

  template<typename T, typename toInt=inttoint>
  void printDIMACS(vector<vector<T> >& cnf)
  {
    long count = 1;
    unordered_map<T, long> varmap;

    vector<vector<long> > dicnf(cnf.size());
    dicnf.clear();

    // rename all of the variables, generating a new cnf
    for(typename vector<vector<T> >::iterator i = cnf.begin(); i != cnf.end(); ++i) {
      vector<long> clause;
      for(typename vector<T>::iterator j = i->begin(); j != i->end(); ++j) {
        T tmp = *j & ~(1UL);
        long val;
        typename unordered_map<T, long>::const_iterator found = varmap.find(tmp);
        if(found == varmap.end()) {
          val = count++;
          varmap[tmp] = val;
        } else {
          val = found->second;
        }
        toInt iti;
        clause.push_back((iti(*j) & 1) ? -val : val);
      }
      dicnf.push_back(clause);
    }

    cout << "p cnf " << varmap.size() << " " << dicnf.size() << endl;

    for(vector<vector<long> >::iterator i = dicnf.begin(); i != dicnf.end(); ++i) {
      for(vector<long>::iterator j = i->begin(); j != i->end(); ++j) {
        cout << *j << " ";
      }
      cout << 0 << "\n";
    }
    cout.flush();
  }

  void di_tseitin(Model& model)
  {
    ExprAttachment const * eat = static_cast<ExprAttachment const *>(model.constAttachment(Key::EXPR));
    Expr::Manager::View * view = model.newView();

    ID output = eat->outputFnOf(eat->outputs()[0]);
    vector<vector<ID> > cnf;
    Expr::tseitin(*view, output, cnf);

    printDIMACS(cnf);
    delete view;
    model.constRelease(eat);
  }

  void di_nice(Model& model)
  {
    ExprAttachment const * eat = static_cast<ExprAttachment const *>(model.constAttachment(Key::EXPR));
    Expr::Manager::View * view = model.newView();

    ID output = eat->outputFnOf(eat->outputs()[0]);
    vector<ID> outputs;
    outputs.push_back(output);

    vector<vector<ID> > cnf;

    unsigned k = model.options()["nice_k"].as<unsigned>();

    CNF::niceCNF(model.verbosity(), view, k, outputs, cnf);

    printDIMACS(cnf);
    delete view;
    model.constRelease(eat);
  }

  void di_techmap(Model& model)
  {
    ExprAttachment const * eat = static_cast<ExprAttachment const *>(model.constAttachment(Key::EXPR));
    AIGAttachment const * aatc = static_cast<AIGAttachment const *>(model.constAttachment(Key::AIG));
    AIGAttachment aat(*aatc);
    // get the options
    unsigned k = model.options()["tmcnf_k"].as<unsigned>();
    unsigned l = model.options()["tmcnf_l"].as<unsigned>();
    unsigned refinements = model.options()["tmcnf_refinements"].as<unsigned>();
    double timeOut = DBL_MAX;
    if(model.options().count("cnf_timeout")) {
      timeOut = model.options()["cnf_timeout"].as<double>();
    }

    ID id_output = eat->outputFnOf(eat->outputs()[0]);
    ::Opt::IDRefMap::const_iterator outit = aat.id2ref.find(id_output);
    assert(outit != aat.id2ref.end());
    std::vector< ::Opt::NodeRef> output;
    output.push_back(outit->second);

    vector<vector< ::Opt::NodeRef> > cnf;
    
    CNF::techMap(model.verbosity(), aat, k, l, refinements, output, cnf, timeOut, true);

    printDIMACS< ::Opt::NodeRef, reftoint>(cnf);

    model.constRelease(aatc);
    model.constRelease(eat);

  }
  
}

namespace CNF {

  DIMACSAction::DIMACSAction(Model& model) : Model::Action(model)
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
      case TSEITIN:
        {
          ExprAttachment::Factory f;
          requires(Key::EXPR, &f);
          break;
        }
    }
  }

  void DIMACSAction::exec()
  {
    switch(getMode(model())) {
      case TECHMAP:
        di_techmap(model());
        break;
      case NICE:
        di_nice(model());
        break;
      case TSEITIN:
        di_tseitin(model());
        break;
    }
  }

}
