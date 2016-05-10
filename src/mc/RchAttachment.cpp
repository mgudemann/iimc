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

#include "RchAttachment.h"
#include "SeqAttachment.h"
#include "Simplifier.h"

using namespace std;

void RchAttachment::build()
{
  if (model().verbosity() > Options::Silent)
    cout << "RchAttachment: building" << endl;
  _fw_lb = _view->bfalse();
  _fw_ub = _view->btrue();
  _bw_lb = _view->bfalse();
  _bw_ub = _view->btrue();
  // We assume that transformations of the expressions do not
  // decrease the lower bound on the length of counterexamples.
  // Hence, we do not reset _cex_lb.
  //_cex_lb = 0;

} // RchAttachment::build

RchAttachment::~RchAttachment() {
  delete _view; 
  if (_periodicMap) delete _periodicMap;
  if (_persSatView) delete _persSatView;
  if (_persSatMan) delete _persSatMan;
}
RchAttachment::RchAttachment(const RchAttachment& from, Model & model) : 
  Model::Attachment(from, model),
  _view(model.newView()),
  _fw_lb(from._fw_lb),
  _fw_ub(from._fw_ub),
  _bw_lb(from._bw_lb),
  _bw_ub(from._bw_ub),
  _cex_lb(from._cex_lb),
  _has_tv_info(from._has_tv_info),
  _stem_length(from._stem_length),
  _loop_length(from._loop_length),
  _stabilized(from._stabilized),
  _widened(from._widened),
  _periodicMap(from._has_tv_info ? new PeriodicCardMap(*(from._periodicMap)) : 0),
  _fw_steps_bdd(0),
  _bw_steps_bdd(0),
  _fw_bdd_complete(false),
  _bw_bdd_complete(false),
  _persSatMan(0), _persSatView(0), _persSatTrAdded(false),
  _persUpToDate(false)
{}

std::string RchAttachment::string(bool) const
{
  std::ostringstream ret;
  ret << "RCH (Timestamp = " << _ts 
      << "):\n  upper and lower bounds on forward and backward reachable states\n"; 
  return ret.str();

} // RchAttachment::string


ID RchAttachment::updateBound(ID update, ID bound, Expr::Op op)
{
  // We work directly in the global view since we do not produce garbage.
  Expr::Manager::View *v = _model.newView();
  ID newBound = v->apply(op, update, bound);
  v->keep(newBound);
  delete v;
  return newBound;

} // RchAttachment::updateBound


unsigned int RchAttachment::updateCexLowerBound(unsigned int newLb, std::string who) {
  if (newLb > _cex_lb) {
    _cex_lb = newLb;
    if (model().options().count("cex_aiger")) {
      ostringstream oss;
      //_cex_lb = n means no counterexamples with n states which is equivalent
      //to bound n - 1 in the competition semantics
      //Need to take into account the unrolling, if any, which is stored
      //in SeqAttachment.
      int unrollings = 1;
      SeqAttachment const * const seat = (SeqAttachment const *) model().constAttachment(Key::SEQ);
      if (seat)
        unrollings = seat->unrollings;
      model().constRelease(seat);
      oss << "u" << unrollings * _cex_lb - 1;
      if (model().verbosity() > Options::Silent) {
        oss << ' ' << who;
      }
      oss << endl;
      cout << oss.str() << flush;
    }
  }
  return _cex_lb;
} // RchAttachment::updateCexLowerBound


void RchAttachment::setCexLowerBound(unsigned int newLb){
  // _cex_lb is the lower bound of the current model, possibly after processing
  // modify the cex bound to be set if the semantics change (i.e., phase unrolling)
  // everywhere else should use updateCexLowerBound()
  _cex_lb = newLb;
}


void RchAttachment::setTvInfo(unsigned int stem, unsigned int loop,
                              unsigned int stable, bool widened,
                              PeriodicCardMap * pMap) {
  delete _periodicMap;
  _has_tv_info = true;
  _stem_length = stem;
  _loop_length = loop;
  _stabilized = stable;
  _widened = widened;
  _periodicMap = pMap;
}


void RchAttachment::setForwardBddLowerBound(BDD newFwLb) {
  if (_fw_lb_bdd) {
    _fw_lb_bdd |= newFwLb;
  } else {
    _fw_lb_bdd = newFwLb;
  }
} // RchAttachment::setForwardBddLowerBound


void RchAttachment::setBackwardBddLowerBound(BDD newBwLb) {
  if (_bw_lb_bdd) {
    _bw_lb_bdd |= newBwLb;
  } else {
    _bw_lb_bdd = newBwLb;
  }
} // RchAttachment::setBackwardBddLowerBound


BDD RchAttachment::literalVectorToBdd(
  vector<ID> const & cube) const
{
  BddAttachment const * const bat = 
    (BddAttachment const *) _model.constAttachment(Key::BDD);
  assert(bat != 0 && bat->hasBdds());
  int n = cube.size();
#if 0
  // This could be sped up if necessary by bypassing the C++
  // interface to CUDD.
  BDD *vars = new BDD[n];
  for (vector<ID>::size_type i = 0; i != n; ++i) {
    ID literal = cube[i];
    bool complement = _view->op(literal) != Expr::Var;
    assert((complement && _view->op(literal) == Expr::Not)
           || (!complement && _view->op(literal) == Expr::Var));
    ID var = complement ? _view->apply(Expr::Not, literal) : literal;
    assert(bat->hasBdd(var));
    BDD b = bat->bdd(var);
    vars[i] = complement ? !b : b;
  }
  BDD cubeBdd = bddManager().bddComputeCube(vars, 0, n);
  delete[] vars;
#else
  Cudd const & bddMgr = bddManager();
  DdManager *mgr = bddMgr.getManager();
  DdNode *conj = Cudd_ReadOne(mgr);
  Cudd_Ref(conj);
  for (int i = n - 1; i >= 0; i--) {
    ID literal = cube[i];
    bool complement = _view->op(literal) != Expr::Var;
    assert((complement && _view->op(literal) == Expr::Not)
           || (!complement && _view->op(literal) == Expr::Var));
    ID var = complement ? _view->apply(Expr::Not, literal) : literal;
    assert(bat->hasBdd(var));
    BDD b = bat->bdd(var);
    DdNode *bvar = b.getNode();
    DdNode *fn = Cudd_bddAnd(mgr, Cudd_NotCond(bvar,complement), conj);
    Cudd_Ref(fn);
    Cudd_IterDerefBdd(mgr, conj);
    conj = fn;
  }
  Cudd_Deref(conj);
  BDD cubeBdd(bddMgr, conj);
#endif
  _model.constRelease(bat);
  return cubeBdd;

} // RchAttachment::literalVectorToBdd


void RchAttachment::bddToLiteralVector(
  const BDD b,
  vector<ID>& v) const
{
  v.clear();
  BddAttachment const * const bat = 
    (BddAttachment const *) _model.constAttachment(Key::BDD);
  assert(bat != 0 && bat->hasBdds());
  DdManager *mgr = b.manager();
  DdNode *node = b.getNode();
  int nvars = Cudd_ReadSize(mgr);
  int *array = new int[nvars];
  Cudd_BddToCubeArray(mgr, node, array);
  for (int index = 0; index != nvars; ++index) {
    if (array[index] == 2)
      continue;
    ID var = bat->ithVar(index);
    ID literal = (array[index] == 1) ? var : _view->apply(Expr::Not, var);
    v.push_back(literal);
  }
  delete[] array;
  _model.constRelease(bat);

} // RchAttachment::bddToLiteralVector

void RchAttachment::bddToCnf(
  const BDD b,
  vector< vector<ID> >& v) const
{
  v.clear();  // leak?
  BddAttachment const * const bat = 
    (BddAttachment const *) _model.constAttachment(Key::BDD);
  DdManager *mgr = b.manager();
  DdNode *node = b.getNode();
  int nvars = Cudd_ReadSize(mgr);
  int *array = new int[nvars];
  DdNode *lb = Cudd_Not(node);
  Cudd_Ref(lb);
  while (lb != Cudd_ReadLogicZero(mgr)) {
    int length;
    DdNode *implicant = Cudd_LargestCube(mgr,lb,&length);
    Cudd_Ref(implicant);
    DdNode *prime = Cudd_bddMakePrime(mgr,implicant,Cudd_Not(node));
    Cudd_Ref(prime);
    Cudd_RecursiveDeref(mgr,implicant);
    DdNode *tmp = Cudd_bddAnd(mgr,lb,Cudd_Not(prime));
    Cudd_Ref(tmp);
    Cudd_RecursiveDeref(mgr,lb);
    lb = tmp;
    (void) Cudd_BddToCubeArray(mgr,prime,array);
    vector<ID> clause;
    for (int index = 0; index != nvars; ++index) {
      if (array[index] == 2)
        continue;
      ID var = bat->ithVar(index);
      ID literal = (array[index] == 0) ? var : _view->apply(Expr::Not, var);
      clause.push_back(literal);
    }
    v.push_back(clause);
  }
  delete[] array;
  _model.constRelease(bat);

} // RchAttachment::bddToCnf

bool RchAttachment::disjointFromBdd(
  vector<ID> const & cube,
  const BDD& bound,
  vector<ID>* prime) const
{
  assert(bound);
#if 1
  if (prime == 0) {
    BDD cubeBdd = literalVectorToBdd(cube);
    return cubeBdd <= !bound;
  } else {
    vector<ID> one;
    return disjointFromBddExpand(cube, one, bound, prime);
  }
#else
  BDD const cubeBdd = literalVectorToBdd(cube);
  bool ret = cubeBdd <= !bound;
  if (ret && prime != 0) {
    BDD primeBdd = cubeBdd.MakePrime(!bound);
    bddToLiteralVector(primeBdd, *prime);
  }
  return ret;
#endif

} // RchAttachment::disjointFromBdd


bool RchAttachment::disjointFromFwBdd(
  vector<ID> const & cube,
  vector<ID>* prime) const
{
  return disjointFromBdd(cube, _fw_lb_bdd, prime);

} // RchAttachment::disjointFromFwBdd


bool RchAttachment::disjointFromBwBdd(
  vector<ID> const & cube,
  vector<ID>* prime) const
{
  return disjointFromBdd(cube, _bw_lb_bdd, prime);

} // RchAttachment::disjointFromBwBdd


bool RchAttachment::disjointFromBddExpand(
  vector<ID> const & lb,
  vector<ID> const & ub,
  const BDD& bound,
  vector<ID>* expansion) const
{
  assert(bound);
  BDD lbBdd = literalVectorToBdd(lb);
  BDD ubBdd = literalVectorToBdd(ub);
  assert(lbBdd <= ubBdd);
  BDD allPrimes = lbBdd.MaximallyExpand(ubBdd,!bound);
  if (allPrimes == _model.bddManager().bddZero()) {
    assert(!(lbBdd <= !bound));
    return false;
  }
  assert(lbBdd <= allPrimes);
  assert(allPrimes <= ubBdd);
  BDD expBdd = allPrimes.LargestPrimeUnate(lbBdd);
  bddToLiteralVector(expBdd, *expansion);
  assert(lb.size() >= expansion->size());
  assert(ub.size() <= expansion->size());
  return true;

} // RchAttachment::disjointFromBddExpand


bool RchAttachment::disjointFromFwBddExpand(
  vector<ID> const & lb,
  vector<ID> const & ub,
  vector<ID>* expansion) const
{
  return disjointFromBddExpand(lb, ub, _fw_lb_bdd, expansion);

} // RchAttachment::disjointFromFwBddExpand


bool RchAttachment::disjointFromBwBddExpand(
  vector<ID> const & lb,
  vector<ID> const & ub,
  vector<ID>* expansion) const
{
  return disjointFromBddExpand(lb, ub, _bw_lb_bdd, expansion);

} // RchAttachment::disjointFromBwBddExpand


void RchAttachment::filterDroppedPersistentSignals()
{
  SeqAttachment const * const seat =
    (SeqAttachment const *) model().constAttachment(Key::SEQ);
  unordered_map<ID, ID> const & missingLatches = seat->optimized;
  for (unordered_map< ID, std::pair<bool, bool> >::iterator pit =
         _persSignals.begin(); pit != _persSignals.end();) {
    ID signal = pit->first;
    ID var = _view->op(signal) == Expr::Not ? _view->apply(Expr::Not, signal) :
                                              signal;
    assert(_view->op(var) == Expr::Var);
    unordered_map<ID, ID>::const_iterator dit = missingLatches.find(var);
    if (dit != missingLatches.end()) {
      // This latch was dropped: remove it from the persistent signal map.
      pit = _persSignals.erase(pit);
    }
    else {
      ++pit;
    }
  }
  model().constRelease(seat);
} // RchAttachment::filterDroppedPersistentSignals


void RchAttachment::filterDroppedPeriodicSignals()
{
  SeqAttachment const * const seat =
    (SeqAttachment const *) model().constAttachment(Key::SEQ);
  unordered_map<ID, ID> const & missingLatches = seat->optimized;
  for (PeriodicCardMap::iterator pit = _periodicMap->begin();
       pit != _periodicMap->end();) {
    ID signal = pit->first;
    ID var = _view->op(signal) == Expr::Not ? _view->apply(Expr::Not, signal) :
                                              signal;
    assert(_view->op(var) == Expr::Var);
    unordered_map<ID, ID>::const_iterator dit = missingLatches.find(var);
    if (dit != missingLatches.end()) {
      // This latch was dropped: remove it from the persistent signal map.
      pit = _periodicMap->erase(pit);
    }
    else {
      ++pit;
    }
  }
  model().constRelease(seat);

} // RchAttachment::filterDroppedPeriodicSignals


bool RchAttachment::isPersistent(ID signal) const
{
  return _persSignals.find(signal) != _persSignals.end();
}


bool RchAttachment::isEventuallyTrue(ID signal) const
{
  unordered_map< ID, std::pair<bool, bool> >::const_iterator pit = _persSignals.find(signal);
  if (pit == _persSignals.end())
    return false;
  std::pair<bool, bool> const flags = pit->second;
  return flags.first;
}


SAT::Manager::View * RchAttachment::persistentSatView()
{
  if (!_persSatView)
    createPersistentSignalsSatInstance();
  return _persSatView;
}

bool RchAttachment::addPersistentSignal(ID signal,
  bool eventuallyTrue,
  bool contradictsFair)
{
  if (!_persSatView)
    createPersistentSignalsSatInstance();
  _persUpToDate = false;
  _persSignals[signal] = make_pair(eventuallyTrue, contradictsFair);
  if (eventuallyTrue && contradictsFair)
    return true;
  SAT::Clause cls1, cls2;
  if (eventuallyTrue) {
    cls1.push_back(signal);
    cls2.push_back(Expr::primeFormula(*_view, signal));
  }
  else if (contradictsFair) {
    cls1.push_back(_view->apply(Expr::Not, signal));
    cls2.push_back((Expr::primeFormula(*_view, _view->apply(Expr::Not, signal))));
  }
  else {
    //signal <-> signal'
    cls1.push_back(_view->apply(Expr::Not, signal));
    cls1.push_back(Expr::primeFormula(*_view, signal));
    cls2.push_back(signal);
    cls2.push_back(Expr::primeFormula(*_view, _view->apply(Expr::Not, signal)));
  }
  _persSatView->add(cls1);
  _persSatView->add(cls2);
  return false;
}

bool RchAttachment::addReach(vector< vector<ID> > & reach)
{
  if (!_persSatView)
    createPersistentSignalsSatInstance();
  _persUpToDate = false;
  try {
    _persSatView->add(reach);
  }
  catch (SAT::Trivial tv) {
    assert(!tv.value());
    return false;
  }
  return true;
}

bool RchAttachment::kUpperBound(unsigned int k, 
                                vector< vector<ID> > & rv,
                                const vector< vector< vector<ID> > > & _ub) const 
{
  if (k >= _ub.size()) 
    return false;
  rv.insert(rv.end(), _ub[k].begin(), _ub[k].end());
  return true;
}
bool RchAttachment::kForwardUpperBound(unsigned int k, vector< vector<ID> > & rv) const {
  return kUpperBound(k, rv, _k_fw_ub);
}
bool RchAttachment::kBackwardUpperBound(unsigned int k, vector< vector<ID> > & rv) const {
  return kUpperBound(k, rv, _k_bw_ub);
}

void RchAttachment::setKUpperBound(unsigned int k, 
                                   const vector< vector<ID> > & ub,
                                   vector< vector< vector<ID> > > & _ub)
{
  while (_ub.size() <= k)
    _ub.push_back(vector< vector<ID> >());
  _ub[k] = ub;
}
void RchAttachment::setKForwardUpperBound(unsigned int k, const vector< vector<ID> > & ub) {
  setKUpperBound(k, ub, _k_fw_ub);
}
void RchAttachment::setKBackwardUpperBound(unsigned int k, const vector< vector<ID> > & ub) {
  setKUpperBound(k, ub, _k_bw_ub);
}

void RchAttachment::createPersistentSignalsSatInstance()
{
  assert(!_persSatMan);
  _persSatMan = model().newSATManager();
  _persSatView = _persSatMan->newView(*_view);
}
