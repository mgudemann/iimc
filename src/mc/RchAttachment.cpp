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

#include "RchAttachment.h"

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


std::string RchAttachment::string(bool includeDetails) const
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


unsigned int RchAttachment::updateCexLowerBound(unsigned int newLb) {
  return (_cex_lb = std::max(_cex_lb, newLb));

} // RchAttachment::updateCexLowerBound


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
  BddAttachment const *bat = 
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
  BddAttachment const *bat = 
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
  BddAttachment const *bat = 
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
