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

#include <ostream>
#include "ExprUtil.h"
#include "ExprBdd.h"
#include "BddReach.h"
#include "Model.h"
#include "ExprAttachment.h"
#include "BddAttachment.h"
#include "BddTrAttachment.h"
#include "StringTR.h"

using namespace std;
using namespace Expr;

typedef boost::program_options::variables_map options_map;

/***********************************************************************
 * Sample Actions.
 **********************************************************************/

/**
 * Local tactic to build expressions for a fixed example model.
 */
class LocalExprAction : public Model::Action {
public:
  /**
   * Constructor used in initialization.
   */
  LocalExprAction(Model & m) :  Model::Action(m) {}
  /**
   * Function that implements this action.
   */
  virtual void exec() {
    Model & m = model();
    Options::Verbosity verbosity = _model.verbosity();
    build(m);
    // Sample queries.
    if (verbosity > Options::Terse)
      cout << "------ queries ------" << endl;
    ExprAttachment const *at = (ExprAttachment *) m.constAttachment(Key::EXPR);
    Manager::View *v = m.newView();  // global view
    const IDVector sv = at->stateVars();
    if (verbosity > Options::Terse) {
      for (IDVector::const_iterator i = sv.begin(); i != sv.end(); ++i)
        cout << stringOf(*v, v->prime(*i)) << " = "
             << stringOf(*v, at->nextStateFnOf(*i)) << endl;
    }
    assert(v->newVar("x0") == sv[0]);
    assert(v->varName(sv[1]) == "x1");
    assert(v->varName(at->inputs()[0]) == "w0");
    assert(v->newVar("z1") == at->outputs()[1]);
    delete v;
    m.constRelease(at);
  }
  void build(Model& model);
};

/**
 * Create model with three inputs, two state variables and two outputs.
 */
void LocalExprAction::build(Model& model)
{
  ExprAttachment *at = (ExprAttachment *) model.attachment(Key::EXPR);
  assert(at != 0);
  Manager::View *v = model.newView();
  v->begin_local();
  vector<ID> w;
  w.push_back(v->newVar("w0"));
  w.push_back(v->newVar("w1"));
  w.push_back(v->newVar("w2"));
  at->addInputs(w);
  ID x0 = v->newVar("x0");
  ID x1 = v->newVar("x1");
  ID f0 = v->apply(Or, w[0], w[1]);
  ID f1 = v->apply(And, w[2], x0);
  at->setNextStateFn(x0,f0);
  at->setNextStateFn(x1,f1);
  vector<ID> z;
  z.push_back(v->newVar("z0"));
  z.push_back(v->newVar("z1"));
  vector<ID> l;
  l.push_back(v->apply(And, x0, v->apply(Not, x1)));
  l.push_back(f1);
  at->setOutputFns(z,l);
  ID init = v->apply(And, v->apply(Not, x0), v->apply(Not, x1));
  at->addInitialCondition(init);
  ID buechi = v->apply(Not, v->apply(And, x0, x1));
  at->addFairnessConstraint(buechi);
  // Commit and clean up.
  at->global(v);
  v->end_local();
  at->keep(v);
  v->clean();
  delete v;
  model.release(at);

} // LocalExprAction::build


/***********************************************************************/

namespace bpo = boost::program_options;

int main(int argc, char **argv)
{
  // Set up.
  bpo::options_description desc("Allowed options");
  desc.add_options()
    ("bdd_reorderings",
     bpo::value<unsigned int>(),
     "Maximum number of dynamic BDD variable reordering")
    ("bdd_static",
     bpo::value<std::string>()->default_value("interleaving"),
     "Static ordering algorithm (interleaving, plain, linear)")
    ("bdd_trav",
     "Ignore property failure in BDD forward reachability analysis")
    ("bdd_save_fw_reach",
     "Save BDD for reachable states after successful reachability analysis")
    ("verbosity,v", 
     bpo::value<int>()->default_value(0),
     "Set verbosity level (0-4)")
    ;
  bpo::variables_map vm;
  bpo::store(bpo::parse_command_line(argc, argv, desc), vm);
  bpo::notify(vm);
  Model model(vm, "test");
  model.setVerbosity(
    vm.count("verbosity")
    ? (Options::Verbosity) vm["verbosity"].as<int>() : Options::Silent);
  Options::Verbosity verbosity = model.verbosity();

  // Perform actions.
  vector<Model::Action*> actions;
  actions.push_back(new LocalExprAction(model));
  actions.push_back(new BddFwReachAction(model));
  for (vector<Model::Action*>::const_iterator it = actions.begin();
       it != actions.end(); it++) {
    (*it)->make();
    delete *it;
  }
  // Print model.
  if (verbosity > Options::Silent) {
    cout << model.string(true);
    cout << model.dot();
  }

  // Test conversion from BDD to expression.
  BddAttachment const *bat = 
    (BddAttachment const *) model.constAttachment(Key::BDD);
  BddTrAttachment const *tat = 
    (BddTrAttachment const *) model.constAttachment(Key::BDD_TR);
  Manager::View *v = model.newView();
  v->begin_local();
  BDD init = tat->initialCondition();
  ID initE = exprOf(init, *v, bat->order());
  if (verbosity > Options::Silent) {
    cout << "Conversion of initial condition from BDD to expression\n"
         << stringOf(*v, initE) << endl;
  }
  model.constRelease(tat);
  model.constRelease(bat);
  // Test conversion from BDD to CNF.
  if (model.options().count("bdd_save_fw_reach")) {
    RchAttachment const *rat = 
      (RchAttachment const *) model.constAttachment(Key::RCH);
    BDD rch = rat->forwardBddLowerBound();
    cout << "Reachable states";
    rch.print(2,3);
    vector< vector<ID> > cnf;
    rat->bddToCnf(rch,cnf);
    cout << CNF::stringOfVectorVectorID(v, cnf) << "\n";
    model.constRelease(rat);
  }
  v->end_local();
  delete v;

  if (verbosity > Options::Silent)
    cout << "preparing to quit" << endl;
  return 0;

} // main
