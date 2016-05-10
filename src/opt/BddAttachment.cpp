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

#include "Error.h"
#include "Expr.h"
#include "ExprUtil.h"
#include "ExprAttachment.h"
#include "BddAttachment.h"
#include "Util.h"

#include <fstream>
#include <string>
#include <algorithm>

using namespace std;

/**
 * Make string out of attachment.
 */
string BddAttachment::string(bool includeDetails) const {
  if (includeDetails) {
    ostringstream ret;
    ret << "BDD (Timestamp = " << _ts 
	<< "):\n  manager, map, and variable order\n  "
	<< _order.size() << " variables and " << _map.size() << " BDDs";
    return ret.str();
  } else {
    return "BDD: manager, map, and variable order";
  }
}

BDD BddAttachment::bdd(ID id) const {
  Expr::IdBddMap::const_iterator iter = _map.find(id);
  assert(iter != _map.end());
  return iter->second;
}

ID BddAttachment::ithVar(unsigned int i) const {
  assert(i < _order.size());
  return _order[i];
}

namespace {
  string idVectorString(Model &m, vector<ID> const &ids)
  {
    ostringstream buf;
    Expr::Manager::View *v = m.newView();
    shortStringOfID(*v, ids, buf);
    buf << endl;
    delete v;
    return buf.str();
  }
}

string BddAttachment::orderString() const {
  return idVectorString(_model, _order);
}

/**
 * Build BDDs for the model.
 */
void BddAttachment::build() {
  // Set-up.

  Options::Verbosity verbosity = _model.verbosity();
  if (verbosity > Options::Silent)
    cout << "Building BDDs for model " << _model.name() << endl;
  if (_map.size() > 0) {
    // BDDs already built.
    return;
  }

  bddManager().ResetStartTime();
  if (bddManager().ReadSize() != 0) {
    // Prepare a clean slate.
    _map.clear();
    _auxVar.clear();
    _order.clear();
  }
  Expr::Manager::View *v = _model.newView();
  bool sweep = _model.options().count("bdd_sweeping") > 0;
  CombAttachment const *cat = 
    (CombAttachment const *) _model.constAttachment(Key::COMB);
  if (cat->simplificationEffort() == CombAttachment::Complete)
    sweep = false;
  _model.constRelease(cat);
  ExprAttachment *eat;
  if (sweep) {
    eat = (ExprAttachment *) _model.attachment(Key::EXPR);
  } else {
    eat = (ExprAttachment *) _model.constAttachment(Key::EXPR);
  }

  unordered_map<ID, int> orderMap;
  buildVariableOrder(v, eat, orderMap);
  if (verbosity > Options::Informative)
    cout << "Order: " << orderString();

  // Pass relevant options to BDD manager.
  configureBddManager();

  // Collect the roots and build their BDDs in one go.
  vector<ID> roots;
  collectRoots(eat, roots);

  unsigned int auxLimit = 2000;
  if (_model.options().count("bdd_threshold")) {
    auxLimit = _model.options()["bdd_threshold"].as<unsigned int>();
  }

  _map = bddOf(*v, roots, _model, orderMap, _auxVar, auxLimit, sweep, verbosity);

  if (verbosity > Options::Terse) {
    vector<BDD> bv;
    for (Expr::IdBddMap::const_iterator i = _map.begin(); i != _map.end(); ++i)
      bv.push_back(i->second);
    cout << bddManager().SharingSize(bv) << " BDD nodes" << endl;
    cout << _auxVar.size() << " auxiliary variable" 
              << (_auxVar.size() != 1 ? "s" : "") << endl;
  }

  delete v;
  if (sweep) {
    updateExprAttachment(eat, roots);
    _model.release(eat);
  } else {
    _model.constRelease(eat);
  }
  if (_model.options().count("bdd_info")) {
    bddManager().info();
    cout << "CPU time since BDD manager reset = " 
         << ((double) bddManager().ReadElapsedTime()/1000.0)
         << " s" << endl;
  }

  bddManager().UpdateTimeLimit();

} // BddAttachment::build 


/**
 * Build BDD variable order.
 *
 * Compute the leaf order by one of these methods
 * (as requested by the options):
 * 1. Apply the interleaving algorithm.
 * 2. Use a linear ordering algorithm.
 * 3. Use the order in which the leaves appear in the model.
 * 4. Read the order from a file.
 *
 * Moreover, create the variable group tree in the manager
 * according to the options.
 */
void BddAttachment::buildVariableOrder(
  Expr::Manager::View *v,
  ExprAttachment const *eat,
  unordered_map<ID, int>& orderMap,
  bool noNsVars)
{
  Options::Verbosity verbosity = _model.verbosity();
  bool groupSift = _model.options().count("bdd_group") > 0;
  // Collect leaves and roots.
  const vector<ID>& iv = eat->inputs();
  const vector<ID>& sv = eat->stateVars();
  unordered_map<ID, bool> leafIsSv;
  for (vector<ID>::const_iterator i = iv.begin(); i != iv.end(); ++i)
    leafIsSv[*i] = false;
  for (vector<ID>::const_iterator i = sv.begin(); i != sv.end(); ++i)
    leafIsSv[*i] = true;
  vector<ID> roots;
  const vector<ID>& nsfv = eat->nextStateFns();
  roots.insert(roots.end(), nsfv.begin(), nsfv.end());
  const vector<ID>& of = eat->outputFns();
  roots.insert(roots.end(), of.begin(), of.end());
  // These are necessary if no COI reduction is performed.
  if (!noNsVars) {
    roots.insert(roots.end(), sv.begin(), sv.end());
    roots.insert(roots.end(), iv.begin(), iv.end());
  }
  vector<ID> gateList;
  if (_model.options().count("bdd_order") > 0) {
    std::string filename =  _model.options()["bdd_order"].as<std::string>();
    gateList = readOrder(*v, filename, leafIsSv);
  } else {
    std::string method = _model.options()["bdd_static"].as<std::string>();
    if (verbosity > Options::Terse) {
      cout << "Static BDD variable ordering method: "
           << method << endl;
    }
    if (method.compare("interleaving") == 0) {
      gateList = bddOrderOf(*v, roots);
    } else if (method.compare("plain") == 0) {
      gateList.insert(gateList.end(), iv.begin(), iv.end());
      gateList.insert(gateList.end(), sv.begin(), sv.end());
    } else if (method.compare("linear") == 0) {
      gateList = linearOrderOf(*v, roots);
    } else {
      cerr << "Unknown static BDD ordering method.  Using interleaving" << endl;
      gateList = bddOrderOf(*v, roots);
    }
  }
  if (verbosity > Options::Verbose)
    cout << "Gate List: " << idVectorString(_model, gateList);
  // Create supergroup of all variables.  Auxiliary variables may be
  // added later.
  if (!groupSift && !noNsVars)
    bddManager().MakeTreeNode(0, iv.size() + 2*sv.size(), MTR_DEFAULT);
  // Extract leaf order from gate order produced by the interleaving
  // algorithm.
  for (vector<ID>::const_iterator i = gateList.begin();
       i != gateList.end(); ++i) {
    if (leafIsSv.find(*i) != leafIsSv.end()) {
      _order.push_back(*i);
      if (leafIsSv[*i] && !noNsVars) {
        _order.push_back(v->prime(*i));
        if (!groupSift && !noNsVars)
          bddManager().MakeTreeNode(_order.size() - 2, 2, MTR_FIXED);
      }
    }
  }
  for (vector<ID>::size_type i = 0; i != _order.size(); ++i) {
    orderMap[_order[i]] = i;
  }

} // BddAttachment::buildVariableOrder


namespace {
  /**
   * Timeout handler to be installed in the Cudd manager.
   */
  void BddAttachmentHandler(string message) {
    throw Timeout(message);
  }
}


/**
 * Pass relevant program options to BDD manager.
 */
void BddAttachment::configureBddManager(bool sweep) const
{
  bddManager().Reserve(_order.size());
  // Enable dynamic variable reordering if so instructed.
  bool groupSift = _model.options().count("bdd_group") > 0;
  Cudd_ReorderingType reordType = 
    groupSift ? CUDD_REORDER_GROUP_SIFT: CUDD_REORDER_SIFT;
  unsigned int firstReordering =
    max(8 * (unsigned int) _order.size(),
        bddManager().ReadNextReordering());
  bddManager().SetNextReordering(firstReordering);
  if ((!sweep && _model.options().count("bdd_reorderings")) ||
      (sweep && _model.options().count("bdd_sw_reorderings"))) {
    unsigned int numReorderings = sweep 
      ? _model.options()["bdd_sw_reorderings"].as<unsigned int>()
      : _model.options()["bdd_reorderings"].as<unsigned int>();
    if (numReorderings > 0) {
      bddManager().SetMaxReorderings(numReorderings);
      bddManager().AutodynEnable(reordType);
    }
  } else {
    bddManager().AutodynEnable(reordType);
  }
  if (_model.verbosity() > Options::Terse)
    bddManager().EnableReorderingReporting();

  // Set up order randomization if so instructed.
  if (_model.options().count("bdd_rand")) {
    unsigned int factor =
      _model.options()["bdd_rand"].as<unsigned int>();
    if (factor != 0) {
      int rseed = _model.options()["rand"].as<int>();
      if (rseed == -1)
        bddManager().Srandom((long) time(0));
      else
        bddManager().Srandom((long) rseed);
      bddManager().SetOrderRandomization(factor);
    }
  }

  // Set timeout if so instructed.
  if ((!sweep && _model.options().count("bdd_timeout")) ||
      (sweep && _model.options().count("bdd_sw_timeout"))) {
    unsigned long timeout = 1000 * 
      (sweep ? _model.options()["bdd_sw_timeout"].as<unsigned long>()
       : _model.options()["bdd_timeout"].as<unsigned long>());
    bddManager().setTimeoutHandler(BddAttachmentHandler);
    bddManager().SetTimeLimit(timeout);
  }

} // BddAttachment::configureManager


/**
 * Collect the roots of the model, which are the nodes for which BDDs
 * should be built.
 */
void BddAttachment::collectRoots(
  ExprAttachment const *eat,
  vector<ID>& roots) const
{
  roots = _order;
  const vector<ID>& ini = eat->initialConditions();
  roots.insert(roots.end(), ini.begin(), ini.end());
  const vector<ID>& nsfv = eat->nextStateFns();
  roots.insert(roots.end(), nsfv.begin(), nsfv.end());
  const vector<ID>& of = eat->outputFns();
  roots.insert(roots.end(), of.begin(), of.end());
  const vector<ID>& cv = eat->constraints();
  roots.insert(roots.end(), cv.begin(), cv.end());
  const vector<ID>& bv = eat->badFns();
  roots.insert(roots.end(), bv.begin(), bv.end());
  const vector<ID>& fv = eat->fairnessFns();
  roots.insert(roots.end(), fv.begin(), fv.end());
  const vector< vector<ID> > & js = eat->justiceSets();
  for (size_t i = 0; i < js.size(); ++i)
    roots.insert(roots.end(), js[i].begin(), js[i].end());
} // BddAttachment::collectRoots


/**
 * Update the ExprAttachment based on the results of sweeping.
 */
void BddAttachment::updateExprAttachment(ExprAttachment *eat,
                                         const vector<ID>& roots) const
{
  vector<ID>::size_type i = _order.size();

  size_t n_ic = eat->initialConditions().size();
  eat->clearInitialConditions();
  for (vector<ID>::size_type j = 0; j < n_ic; ++j, ++i)
    eat->addInitialCondition(roots[i]);

  vector<ID> vars(eat->stateVars());
  eat->clearNextStateFns();
  for (vector<ID>::size_type j = 0; j < vars.size(); ++j, ++i)
    eat->setNextStateFn(vars[j], roots[i]);

  vector<ID> outputs(eat->outputs());
  eat->clearOutputFns();
  for (vector<ID>::size_type j = 0; j < outputs.size(); ++j, ++i)
    eat->setOutputFn(outputs[j], roots[i]);

  size_t n_cs = eat->constraints().size();
  eat->clearConstraints();
  for (vector<ID>::size_type j = 0; j < n_cs; ++j, ++i)
    eat->addConstraint(roots[i]);

  vector<ID> bad(eat->bad());
  eat->clearBadFns();
  for (vector<ID>::size_type j = 0; j < bad.size(); ++j, ++i)
    eat->setBadFn(bad[j], roots[i]);

  vector<ID> fairness(eat->fairness());
  eat->clearFairnessFns();
  for (vector<ID>::size_type j = 0; j < fairness.size(); ++j, ++i)
    eat->setFairnessFn(fairness[j], roots[i]);

  vector<ID> justice(eat->justice());
  vector< vector<ID> > justiceS(eat->justiceSets());
  eat->clearJusticeSets();
  for (vector<ID>::size_type j = 0; j < justice.size(); ++j) {
    vector<ID> js;
    for (size_t k = 0; k < justiceS[j].size(); ++k, ++i)
      js.push_back(roots[i]);
    eat->setJusticeSet(justice[j], js);
  }

#if 0
  // Check if there are equivalent state variables.
  vector<ID> temp = eat->nextStateFns();
  sort(temp.begin(), temp.end());
  cout << "IDs:";
  for (vector<ID>::const_iterator it = temp.begin(); it != temp.end(); ++it)
    cout << " " << *it;
  cout << endl;
  vector<ID>::iterator new_end = unique(temp.begin(), temp.end());
  cout << new_end - temp.begin() << " unique state variables out of " 
       << eat->nextStateFns().size() << endl;
#endif

} // BddAttachment::updateExprAttachment


/**
 * Create an expression from a BDD.
 */
ID BddAttachment::exprOf(BDD f, Expr::Manager::View& v) const
{
  unordered_map<DdNode*,ID> mp;
  DdGen *gen;
  DdNode *node;
  DdManager *manager = f.manager();
  DdNode *root = f.getNode();
  Cudd_ForeachNode(manager, root, gen, node) {
    assert(!Cudd_IsComplement(node));
    if (Cudd_IsConstant(node)) {
      assert(node == Cudd_ReadOne(manager));
      ID id = v.btrue();
      mp[node] = id;
    } else {
      DdNode *T = Cudd_T(node);
      DdNode *E = Cudd_E(node);
      bool complement = Cudd_IsComplement(E);
      unsigned int index = Cudd_NodeReadIndex(node);
      vector<ID> ops;
      ops.push_back(_order[index]);
      assert(mp.find(T) != mp.end());
      ops.push_back(mp[T]);
      assert(mp.find(Cudd_Regular(E)) != mp.end());
      ID eid = mp[Cudd_Regular(E)];
      ops.push_back(complement ?  v.apply(Expr::Not, eid) : eid);
      ID id = v.apply(Expr::ITE, ops);
      mp[node] = id;
    }
  }
  ID rid = mp[Cudd_Regular(root)];
  bool compRoot =  Cudd_IsComplement(root);
  if (compRoot) {
    return v.apply(Expr::Not, rid);
  } else {
    return rid;
  }

} // BddAttachment::exprOf

void BddAttachment::countStates(const vector< vector<ID> > & cnf, Expr::Manager::View& _view) const {
  //Build BDD for cnf
  assert(hasBdds());

  int numClauses = cnf.size();
  BDD *clauses = new BDD[numClauses];
  int j = 0;
  for(vector< vector<ID> >::const_iterator it = cnf.begin(); it != cnf.end();
      ++it) {
    const vector<ID> & cube = *it;
    size_t n = cube.size();
    BDD *vars = new BDD[n];
    for (vector<ID>::size_type i = 0; i != n; ++i) {
      ID literal = cube[i];
      bool complement = _view.op(literal) != Expr::Var;
      assert((complement && _view.op(literal) == Expr::Not)
             || (!complement && _view.op(literal) == Expr::Var));
      ID var = complement ? _view.apply(Expr::Not, literal) : literal;
      assert(hasBdd(var));
      BDD b = bdd(var);
      vars[i] = complement ? b : !b;
    }
    clauses[j++] = !bddManager().bddComputeCube(vars, 0, n);
    delete[] vars;
  }
  BDD cnfBdd = bddManager().bddComputeCube(clauses, 0, numClauses);
  ExprAttachment const * eat = (ExprAttachment *) _model.constAttachment(Key::EXPR);
  int numSV = eat->stateVars().size();
  _model.constRelease(eat);

  cnfBdd.print(numSV, 1);
}


/**
 * Read the variable order from a file.
 *
 * The file should contain all inputs and current state variables
 * and nothing else.
 */
vector<ID> BddAttachment::readOrder(
  Expr::Manager::View &v, 
  const std::string& filename, 
  unordered_map<ID, bool> leaves)
{
  vector<ID> gateList;
  unordered_set<ID> seen;
  ifstream ifs(filename.c_str());
  if (!ifs.good())
    throw InputError("Cannot open order file.");
  std::string name;
  while (ifs >> name) {
    ID id = v.newVar(name);
    if (leaves.find(id) == leaves.end())
      throw InputError("Unrecognized leaf in order file.");
    if (seen.find(id) != seen.end())
      throw InputError("Duplicate name in order file.");
    seen.insert(id);
    gateList.push_back(id);
  }
  if (gateList.size() != leaves.size())
    throw InputError("Incomplete order file.");
  return gateList;

} // BddAttachment::readOrder


/**
 * Perform BDD sweeping.
 */
void BddSweepAction::exec() {

  Options::Verbosity verbosity = _model.verbosity();
  if (verbosity > Options::Silent)
    cout << "BDD sweeping of model " << _model.name() << endl;

  CombAttachment const *cat = 
    (CombAttachment const *) _model.constAttachment(Key::COMB);
  if (cat->simplificationEffort() == CombAttachment::Complete) {
    _model.constRelease(cat);
    return;
  }

  int64_t startTime = Util::get_user_cpu_time();

  Cudd saveBddMgr = _model.newBddManager(Cudd());

  BddAttachment *bat = new BddAttachment(_model);
  Expr::Manager::View *v = _model.newView();
  ExprAttachment *eat = 
    (ExprAttachment *) _model.attachment(Key::EXPR);

  unordered_map<ID, int> orderMap;
  bat->buildVariableOrder(v, eat, orderMap, true);
  if (verbosity > Options::Informative)
    cout << "Order: " << bat->orderString();

  // Pass relevant options to BDD manager.
  bat->configureBddManager(true);

  // Collect the roots and build their BDDs in one go.
  vector<ID> roots;
  bat->collectRoots(eat, roots);

  unsigned int auxLimit = 250;
  if (_model.options().count("bdd_sw_threshold")) {
    auxLimit = _model.options()["bdd_sw_threshold"].as<unsigned int>();
  }

  bat->_map = bddOf(*v, roots, _model, orderMap, bat->_auxVar, auxLimit, true, verbosity);

  if (verbosity > Options::Terse) {
    vector<BDD> bv;
    for (Expr::IdBddMap::const_iterator i = bat->_map.begin(); i != bat->_map.end(); ++i)
      bv.push_back(i->second);
    cout << bddManager().SharingSize(bv) << " BDD nodes" << endl;
    cout << bat->_auxVar.size() << " auxiliary variable" 
              << (bat->_auxVar.size() != 1 ? "s" : "") << endl;
  }

  delete v;

  int64_t endTime = Util::get_user_cpu_time(); 

  if (verbosity > Options::Terse) {
    cout << "BDD Sweeping: " << ((endTime - startTime) / 1000000.0)
         << "s spent in sweeping" << endl;
  }

  bat->updateExprAttachment(eat, roots);
  _model.release(eat);
  delete bat;
  if (_model.options().count("bdd_info")) {
    bddManager().info();
    cout << "CPU time since BDD manager reset = " 
         << ((double) bddManager().ReadElapsedTime()/1000.0)
         << " s" << endl;
  }

  (void) _model.newBddManager(saveBddMgr);

} // BddSweepAction::exec
