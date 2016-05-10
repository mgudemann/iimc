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

#include <boost/program_options.hpp>
#include "options.h"
#include "AIG.h"
#include "AIGAttachment.h"
#include "TechMapCNF.h"
#include "NiceDAG.h"
#include "SAT.h"
#include "StringTR.h"
#include <cstdlib>

namespace CNF
{
  class CNFTestAction : public Model::Action {
  public:
    CNFTestAction(Model & model) : Model::Action(model)
    {
      // CNF attachment builds according to command line
      CNFAttachment::Factory f;
      // Expr attachment used to perform tseitin directly
      ExprAttachment::Factory ef;
      requires(Key::CNF, &f);
      requires(Key::EXPR, &ef);
    }

    std::string satstrOfID(Expr::Manager::View* v, ID id)
    {
      std::string name = stringOfID(v, id);
      for(unsigned i = 0; i < name.length(); ++i) {
        if(name[i] == '(' || name[i] == ')')
          name[i] = '_';
      }
      return name;
    }

    void printCNF(Expr::Manager::View& v, std::vector< std::vector<ID> >& cnf)
    {
      // print variables
      std::set<ID> vars;
      for(unsigned i = 0; i < cnf.size(); ++i) {
        for(unsigned j = 0; j < cnf[i].size(); ++j) {
          if(v.op(cnf[i][j]) == Expr::Not) {
            vars.insert(v.apply(Expr::Not, cnf[i][j]));
          } else {
            vars.insert(cnf[i][j]);
          }
        }
      }

      for(std::set<ID>::iterator i = vars.begin(); i != vars.end(); ++i) {
        std::cout << "(define " << satstrOfID(&v, *i) << "::bool)" << std::endl;
      }

      std::cout << std::endl << "(and";
      for(unsigned i = 0; i < cnf.size(); ++i) {
        std::cout << std::endl << "  (or";
        for(unsigned j = 0; j < cnf[i].size(); ++j) {
          if(v.op(cnf[i][j]) == Expr::Not) {
            int nargs;
            const ID* ids = v.arguments(cnf[i][j], &nargs);
            assert(nargs == 1);
            std::cout << std::endl << "    (not " << satstrOfID(&v,ids[0]) << ")";
          } else {
            std::cout << std::endl << "    " << satstrOfID(&v, cnf[i][j]);
          }
        }
        std::cout << ")";
      }
      std::cout << ")" << std::endl;
    }

    typedef std::pair<bool,bool> ClRet;

    ClRet addClauses(SAT::Manager::View* sview, std::vector<std::vector<ID> >& clauses)
    {
      // add CNF for each transformation, catch trivial sat/unsat
      try {
        // add to global clauses
        sview->add(clauses);
      }
      catch(SAT::Trivial tr) {
        delete sview;
        if(tr.value() == false) {
          return std::make_pair(false, false);
        } else {
          return std::make_pair(false, true);
        }
      }
      return std::make_pair(true, true);
    }

#if 0
    bool checkOutput(SAT::Manager::View* sview, Expr::Manager::View* view, ID coutput, ID toutput)
    {

      try {
        if(model().verbosity() > Options::Terse)
          std::cout << "Checking v" << coutput << " vs v" << toutput << std::endl;
        ID ncoutput = view->apply(Expr::Not, coutput);
        ID ntoutput = view->apply(Expr::Not, toutput);

        std::vector<std::vector<ID> > assume1(2);
        std::vector<std::vector<ID> > assume2(2);
        assume1[0].push_back(coutput);
        assume1[1].push_back(ntoutput);
        assume2[0].push_back(ncoutput);
        assume2[1].push_back(toutput);

        bool trivial_unsat = false;

        SAT::GID g1 = sview->newGID();
        try {
          sview->add(assume1, g1);
        } catch(SAT::Trivial e) {
          if(e.value()) {
            sview->remove(g1);
            return false;
          } else {
            trivial_unsat = true;
          }
        }

        if(!trivial_unsat && sview->sat()) {
          sview->remove(g1);
          return false;
        }
        sview->remove(g1);

        trivial_unsat = false;

        SAT::GID g2 = sview->newGID();
        try {
          sview->add(assume2, g2);
        } catch(SAT::Trivial e) {
          if(e.value()) {
            sview->remove(g2);
            return false;
          } else {
            trivial_unsat = true;
          }
        }

        if(!trivial_unsat && sview->sat()) {
          sview->remove(g2);
          return false;
        }
        sview->remove(g2);

      } catch(...) {
        std::cout << "Exception occured" << std::endl;
      }

      return true;
    }
#endif

    void check(bool option) {
      ExprAttachment const* eat = static_cast< ExprAttachment const*>(model().constAttachment(Key::EXPR));
      Expr::Manager::View* view = _model.newView();

      // result vectors
      std::vector<std::vector<ID> > tcnf;
      std::vector<std::vector<ID> > ncnf;

      std::vector<ID> latches(eat->stateVars());
      std::vector<ID> fns(eat->nextStateFnOf(latches));

      // construct transition relation
      ID root = view->btrue();
      for (unsigned int i = 0; i < latches.size(); ++i)
        root = view->apply(Expr::And, root, view->apply(Expr::Equiv, 
                                             view->prime(latches[i]),
                                             fns[i]));

      // append property
      root = view->apply(Expr::And, root, view->apply(Expr::Not, eat->outputFnOf(eat->outputs()[0])));
     
      std::vector<ID> tr1;
      std::vector<ID> tr2;

      if(option) {
        tr1.push_back(root);
        tr2.push_back(view->apply(Expr::Not, root));
      } else {
        tr1.push_back(view->apply(Expr::Not, root));
        tr2.push_back(root);
      }

      // run tseitin
      Expr::tseitin(*view, tr1, tcnf);
      std::cout << "Tseitin:"<< std::endl;
      printCNF(*view, tcnf);

      // run nice
      unsigned k = _model.options()["nice_k"].as<unsigned>();

      CNF::niceCNF(model().verbosity(), view, k, tr2, ncnf);
      std::cout << "Nice:"<< std::endl;
      printCNF(*view, ncnf);


      // create sat manager
      SAT::Manager* satman = _model.newSATManager();
      SAT::Manager::View* sview = satman->newView(*view);

      // call SAT with ccnf roots positive and tcnf roots negative
      addClauses(sview, tcnf);
      addClauses(sview, ncnf);

      if(sview->sat()) {
        if(option)
          std::cout << "Tseitin & !Nice SAT" << std::endl;
        else
          std::cout << "!Tseitin & Nice SAT" << std::endl;
        return;
      } else {
        if(option)
          std::cout << "Tseitin & !Nice UNSAT" << std::endl;
        else
          std::cout << "!Tseitin & Nice UNSAT" << std::endl;
        return;
      }
    }
#if 1
    virtual void exec() {
      check(true);
      check(false);
    }
#else
    virtual void exec() {
      ::CNFAttachment const* cat = static_cast< ::CNFAttachment const*>(model().constAttachment(Key::CNF));
      model().constRelease(cat);

      Expr::Manager::View* view = _model.newView();
      std::vector<std::vector<ID> > ccnf;
      ccnf = cat->getCNF();
      printCNF(*view, ccnf);

      delete view;


#if 0
      CNFAttachment const* cat = static_cast< CNFAttachment const*>(model().constAttachment(Key::CNF));
      ExprAttachment const* eat = static_cast< ExprAttachment const*>(model().constAttachment(Key::EXPR));
      Expr::Manager::View* view = _model.newView();

      // result vectors
      std::vector<std::vector<ID> > tcnf;
      std::vector<std::vector<ID> > ccnf;
     
      // run CNF attachment
      ccnf = cat->getCNFNoRoots();
      std::vector<ID> croots = cat->getRoots();


      std::vector<ID> tmpvec;

      // run tseitin
      std::vector<ID> latches(eat->stateVars());
      std::vector<ID> fns(eat->nextStateFnOf(latches));
      std::vector<ID> outputs(fns);
      Expr::tseitin(*view, outputs, tcnf, 0, false);



      // print out the models if requested
      if(model().verbosity() >= Options::Logorrheic) {
        std::cout << "CNF Attachment: ";
        printCNF(*view, ccnf);
        std::cout << std::endl;
        std::cout << "Tseitin: ";
        printCNF(*view, tcnf);
      }


      // create sat manager
      SAT::Manager* satman = _model.newSATManager();
      SAT::Manager::View* sview = satman->newView(*view);
      bool success = true;

      // Quick sanity check.  Roots should be the same size
      if(croots.size() != outputs.size()) {
        std::cout << "Fail roots different size" << std::endl;
        goto cleanup;
      }

      // call SAT with ccnf roots positive and tcnf roots negative
      addClauses(sview, ccnf);
      addClauses(sview, tcnf);

      if(model().verbosity() > Options::Terse) {
        std::cout << "Checking " << croots.size() << " outputs." << std::endl;
      }

      for(unsigned i = 0; success && i < croots.size(); ++i) {
        success = checkOutput(sview, view, croots[i], outputs[i]);
      }

      if(success)
        std::cout << "Pass" << std::endl;
      else
        std::cout << "Fail" << std::endl;

cleanup:
      std::cout << "Cleaning up" << std::endl;
      delete sview;

      delete view;

      _model.constRelease(eat);
      _model.constRelease(cat);





      //::CNF::printCNF(cnf);
#endif
    }
#endif
  };
}
