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

#include "Error.h"
#include "ExprAttachment.h"
#include "BddAttachment.h"
#include "BddTrAttachment.h"

#include <queue>
#include <algorithm>

using namespace std;

namespace {
  /** Utility functions. */
  void reportBDD(string title, BDD bdd, int nvars,
                 Options::Verbosity verbosity, Options::Verbosity threshold);
  template <class T> void printVector(const string& s, const vector<T>& v);
}


/**
 * Make string out of attachment.
 */
string BddTrAttachment::string(bool includeDetails) const {
  if (includeDetails) {
    ostringstream ret;
    ret << "BDD_TR (Timestamp = " << _ts 
	<< "):\n  manager, transition relation, and initial condition\n  "
	<< _tr.size() << " cluster(s) in the transition relation";
    return ret.str();
  } else {
    return "BDD_TR: manager, transition relation, and initial condition";
  }
}


/**
 * Compose auxiliary functions recursively into a BDD.
 */
void BddTrAttachment::composeAuxiliaryFunctions(
  BddAttachment const * bat,
  BDD & f,
  unordered_map<int, ID> const & index2id)
{
  vector<unsigned int> support = f.SupportIndices();
  queue< vector<unsigned int> > q;
  q.push(support);
  while (!q.empty()) {
    vector<unsigned int> supp = q.front();
    q.pop();
    for (vector<unsigned int>::const_iterator j = supp.begin();
         j != supp.end(); ++j) {
      unordered_map<int,ID>::const_iterator cit = index2id.find(*j);
      if (cit != index2id.end()) {
        BDD g = bat->bdd(cit->second);
        BDD a = bddManager().bddVar(*j);
        f = f.AndAbstract(a.Xnor(g),a);
        vector<unsigned int> addSupp = g.SupportIndices();
        q.push(addSupp);
      }
    }
  }
}


/**
 * Build BDDs for the transition relation of the model.
 */
void BddTrAttachment::build()
{
  Options::Verbosity verbosity = _model.verbosity();
  if (verbosity > Options::Silent)
    cout << "Computing transition relation for model " << _model.name() << endl;
  BddAttachment const * bat = 
    (BddAttachment const *) _model.constAttachment(Key::BDD);
  assert(bat != 0);
  // The BDD attachment may not have BDDs because of a timeout.
  if (bat->hasBdds() == false) {
    _model.constRelease(bat);
    return;
  }
  if (hasBdds())
    return;
  ExprAttachment const * eat =
    (ExprAttachment *) _model.constAttachment(Key::EXPR);
  Expr::Manager::View *v = _model.newView();
  resetBddManager("bdd_tr_timeout");

  try {
    // Gather the conjuncts of the transition relation and initial condition.
    const vector<ID> sv = eat->stateVars();
    const vector<ID> iv = eat->inputs();
    const unordered_map<ID, int>& auxVar = bat->auxiliaryVars();
    int nvars = 2 * sv.size() + iv.size() + auxVar.size();
    if (verbosity > Options::Terse)
      cout << "number of variables = " << nvars << endl;
    BDD inputCube = bddManager().bddOne();
    for (vector<ID>::const_iterator i = iv.begin(); i != iv.end(); ++i) {
      BDD w = bat->bdd(*i);
      inputCube &= w;
    }
    BDD fwAbsCube = bddManager().bddOne();
    BDD bwAbsCube = bddManager().bddOne();
    vector<BDD> conjuncts;
    for (vector<ID>::const_iterator i = sv.begin(); i != sv.end(); ++i) {
      BDD x = bat->bdd(*i);
      _xvars.push_back(x);
      fwAbsCube &= x;
      ID nsv = v->prime(*i);
      BDD y = bat->bdd(nsv);
      _yvars.push_back(y);
      bwAbsCube &= y;
      ID nsf = eat->nextStateFnOf(*i);
      BDD f = bat->bdd(nsf);
      if (verbosity > Options::Informative)
        if (f.IsVar())
          cout << "Found a variable next-state function" << endl; 
      BDD t = y.Xnor(f);
      if (verbosity > Options::Verbose)
        reportBDD(stringOf(*v, nsv) + " <-> " + stringOf(*v, nsf),
                  t, nvars, verbosity, Options::Verbose);
      conjuncts.push_back(t);
    }

    // Process auxiliary variables.
    vector<BDD> conjAux;
    for (unordered_map<ID, int>::const_iterator it = auxVar.begin();
         it != auxVar.end(); ++it) {
      BDD f = bat->bdd(it->first);
      BDD v = bddManager().bddVar(it->second);
      BDD t = v.Xnor(f);
      conjAux.push_back(t);
      inputCube &= v;
    }
    conjuncts.insert(conjuncts.end(), conjAux.begin(), conjAux.end());
    // Build map from BDD variable indices to expression IDs.
    unordered_map<int, ID> index2id;
    for (unordered_map<ID, int>::const_iterator it = auxVar.begin();
         it != auxVar.end(); ++it) {
      index2id[it->second] = it->first;
    }

    // Add invariant constraints.
    const vector<ID> constr = eat->constraintFns();
    for (vector<ID>::const_iterator i = constr.begin(); 
         i != constr.end(); ++i) {
      BDD cn = bat->bdd(*i);
      composeAuxiliaryFunctions(bat, cn, index2id);
      _constr.push_back(cn);
      BDD cny = cn.ExistAbstract(inputCube);
      cny = cny.SwapVariables(_yvars, _xvars);
      reportBDD("Invariant constraint", cn, nvars, verbosity, Options::Terse);
      conjuncts.push_back(cn);
      conjuncts.push_back(cny);
    }

    unsigned int clusterLimit = 2500;
    if (_model.options().count("bdd_tr_cluster")) {
      clusterLimit = _model.options()["bdd_tr_cluster"].as<unsigned int>();
    }

    // Collect output functions applying invariant constraints and substituting
    // auxiliary variables.
    const vector<ID> outf = eat->outputs();
    for (vector<ID>::const_iterator i = outf.begin(); i != outf.end(); ++i) {
      BDD of = bat->bdd(eat->outputFnOf(*i));
      // Apply invariant constraints.
      for (vector<BDD>::iterator i = _constr.begin(); i != _constr.end(); ++i)
        of &= *i;
      composeAuxiliaryFunctions(bat, of, index2id);
      // Finally, remove primary inputs.
      if (_model.defaultMode() != Model::mFAIR) {
        of = of.ExistAbstract(inputCube);
      }
      _inv.push_back(of);
      reportBDD("Output function", of, _xvars.size(), verbosity,
                Options::Terse);
    }

    // Build the transition relation from the conjuncts.
    vector<BDD> sortedConjuncts = linearArrangement(conjuncts);
    assert(sortedConjuncts.size() == conjuncts.size());
    conjuncts.clear();
    vector<BDD> clusteredConjuncts =
      clusterConjuncts(sortedConjuncts, inputCube, clusterLimit, verbosity);
    assert(sortedConjuncts.size() == 0);
    inputCube = quantifyLocalInputs(clusteredConjuncts, inputCube,
                                    clusterLimit, verbosity);
    computeSchedule(clusteredConjuncts, inputCube);

    // Build initial condition.
    const vector<ID> ini = eat->initialConditions();
    _init = bddManager().bddOne();
    for (vector<ID>::const_iterator i = ini.begin(); i != ini.end(); ++i) {
      BDD ic = bat->bdd(*i);
      _init &= ic;
    }
    reportBDD("Initial condition", _init, _xvars.size(), verbosity,
              Options::Terse);
  } catch (Timeout& e) {
    bddManager().ClearErrorCode();
    bddManager().UnsetTimeLimit();
    bddManager().ResetStartTime();
    if (verbosity > Options::Silent)
      std::cout << e.what() << std::endl;
    _tr.clear();
    _xvars.clear();
    _yvars.clear();
    _inv.clear();
    _prequantx = bddManager().bddOne();
    _prequanty = bddManager().bddOne();
    _init = bddManager().bddZero();
  }
  delete v;
  _model.constRelease(eat);
  _model.constRelease(bat);

  bddManager().UpdateTimeLimit();

} // BddTrAttachment::build


/**
 * Compute the image of a set of states.
 */
BDD BddTrAttachment::img(const BDD& from) const
{
  BDD imgy = from.ExistAbstract(_prequantx);
  for (vector< RelPart >::const_iterator it = _tr.begin();
       it != _tr.end(); ++it) {
    imgy = imgy.AndAbstract(it->part(), it->fwQuantCube());
  }
  BDD imgx = imgy.SwapVariables(_xvars,_yvars);
  return imgx;

} // BddTrAttachment::img


/**
 * Compute the preimage of a set of states.
 */
BDD BddTrAttachment::preimg(const BDD& from) const
{
  BDD preimgx = from.SwapVariables(_yvars,_xvars);
  preimgx = preimgx.ExistAbstract(_prequanty);
  for (vector< RelPart >::const_iterator it = _tr.begin();
       it != _tr.end(); ++it) {
    preimgx = preimgx.AndAbstract(it->part(), it->bwQuantCube());
  }
  return preimgx;

} // BddTrAttachment::preimg


/**
 * Cluster conjuncts to produce a partitioned transition relation.
 *
 * Conjuncts larger than limit are rejected (unless they are
 * singletons).
 */
vector<BDD> BddTrAttachment::clusterConjunctsOld(
  vector<BDD>& conjuncts,
  unsigned int limit,
  Options::Verbosity verbosity,
  int nvars) const
{
  vector<BDD> clusters;
  if (conjuncts.size() == 0) {
    clusters.push_back(bddManager().bddOne());
    return clusters;
  }
  vector<BDD>::const_reverse_iterator it = conjuncts.rbegin();
  BDD cluster = *it++;
  conjuncts.pop_back();
  while (it != conjuncts.rend()) {
    reportBDD("conjunct", *it, nvars, verbosity, Options::Informative);
    BDD tmp = cluster.And(*it,limit);
    if (tmp && (unsigned int) tmp.nodeCount() <= 2*limit) {
      cluster = tmp;
    } else {
      reportBDD("Cluster", cluster, nvars, verbosity, Options::Informative);
      clusters.push_back(cluster);
      cluster = *it;
    }
    ++it;
    conjuncts.pop_back();
  }
  reportBDD("Cluster", cluster, nvars, verbosity, Options::Informative);
  clusters.push_back(cluster);
  return clusters;

} // BddTrAttachment::clusterConjunctsOld


namespace {
  class VarRec {
  public:
    VarRec(unsigned int index, int early, int late) 
      : _index(index), _earliest(early), _latest(late) {}
    bool operator<(const VarRec & other) const {
      return _latest > other._latest ||
        (_latest == other._latest && _earliest > other._earliest);
    }
    unsigned int index() const { return _index; }
    int earliest() const { return _earliest; }
    int latest() const { return _latest; }
    void setEarliest(int early) { _earliest = early; }
    void setLatest(int late) { _latest = late; }
  private:
    unsigned int _index;
    int _earliest;
    int _latest;
  };
}


vector<BDD> BddTrAttachment::clusterConjuncts(
  vector<BDD>& conjuncts,
  const BDD& qcube,
  unsigned int limit,
  Options::Verbosity verbosity) const
{
  vector<BDD> clusters;
  if (conjuncts.size() == 0) {
    clusters.push_back(bddManager().bddOne());
    return clusters;
  }
  // Create records of occurrence of all variables in the conjuncts.
  // The variables that occur in no conjuncts end up with
  // earliest > latest.  For the others, we know the first and last
  // conjunct in which they occur.
  unsigned int numvars = bddManager().ReadSize();
  unsigned int nconjuncts = conjuncts.size();
  vector<VarRec> occurrence;
  occurrence.reserve(numvars);
  for (unsigned int i = 0; i != numvars; ++i) {
    occurrence.push_back(VarRec(i,nconjuncts,-1));
  }
  for (vector<BDD>::size_type i = 0; i != nconjuncts; ++i) {
    vector<unsigned int> support = conjuncts[i].SupportIndices();
    for (vector<unsigned int>::const_iterator j = support.begin();
         j != support.end(); ++j) {
      if (occurrence[*j].earliest() > (int) i)
        occurrence[*j].setEarliest((int) i);
      if (occurrence[*j].latest() < (int) i)
        occurrence[*j].setLatest((int) i);
    }
  }

  // Filter variables that are not candidates for quantification
  // and are not present in the conjuncts.
  vector<unsigned int> qvars = qcube.SupportIndices();
  unordered_set<unsigned int> qset(qvars.begin(), qvars.end());
  vector<VarRec> candidate;
  candidate.reserve(qvars.size());
  for (vector<VarRec>::const_iterator i = occurrence.begin();
       i != occurrence.end(); ++i) {
    if (qset.find(i->index()) != qset.end() &&
        i->earliest() <= i->latest())
      candidate.push_back(*i);
  }
  // Sort occurrence records according to latest occurrence
  // using earliest occurrence as tie breaker.
  stable_sort(candidate.begin(), candidate.end());
#if 0
  // Diagnostic printout.
  for (vector<VarRec>::const_iterator i = candidate.begin();
       i != candidate.end(); ++i) {
    cout << "Variable: " << i->index() << " ("
         << i->earliest() << "," << i->latest() << ")\n";
  }
#endif

  // We are now ready for clustering having collected the
  // information of which variables may be quantified when.
  // In the following, i points to the first conjunct in the cluster.
  // (Conjunct of highest index since we go backwards.)
  int i = conjuncts.size() - 1;
  BDD cluster = conjuncts[i];
  conjuncts.pop_back();
  // j points to the conjuncts that is being added to the cluster.
  int j = i - 1;
  // k points to the candidates for quantification
  vector<VarRec>::size_type k = 0;
  while (j >= 0) {
    reportBDD("conjunct", conjuncts[j], numvars, verbosity, Options::Informative);
    // Find variables that are local to cluster.  A variable is local to
    // the current cluster if its lifespan is entirely contained between
    // i and j.
    BDD qcube = bddManager().bddOne();
    while (k < candidate.size() && candidate[k].latest() > (int) i)
      k++;
    while (k < candidate.size() && candidate[k].earliest() >= (int) j) {
      qcube &= bddManager().bddVar(candidate[k].index());
      k++;
    }
    BDD tmp = cluster.AndAbstract(conjuncts[j], qcube, limit);
    if (tmp && (unsigned int) tmp.nodeCount() <= 2*limit) {
      cluster = tmp;
    } else {
      reportBDD("Cluster", cluster, numvars, verbosity, Options::Informative);
      clusters.push_back(cluster);
      i = j;
      cluster = conjuncts[i];
    }
    j--;
    conjuncts.pop_back();
  }
  reportBDD("Cluster", cluster, numvars, verbosity, Options::Informative);
  clusters.push_back(cluster);
  return clusters;

} // BddTrAttachment::clusterConjuncts


/**
 * Quantify local primary input and auxiliary variables.
 */
BDD BddTrAttachment::quantifyLocalInputs(
  vector<BDD>& conjuncts,
  const BDD& qcube,
  unsigned int limit,
  Options::Verbosity verbosity) const
{
  // A -1 means "not yet seen."
  // A -2 means "seen in more than one conjunct."
  vector<int> whereSeen(bddManager().ReadSize(),-1);
  for (vector<BDD>::size_type i = 0; i != conjuncts.size(); ++i) {
    vector<unsigned int> support = conjuncts[i].SupportIndices();
    for (vector<unsigned int>::const_iterator j = support.begin();
         j != support.end(); ++j) {
      if (whereSeen[*j] == -1)
        whereSeen[*j] = i;
      else
        whereSeen[*j] = -2;
    }
  }

  // Attempt quantification of variables seen exactly once, but
  // back off if this blows up the conjunct.
  vector<unsigned int> qvars = qcube.SupportIndices();
  BDD ret = bddManager().bddOne();
  for (vector<unsigned int>::size_type i = 0; i != qvars.size(); ++i) {
    unsigned int index = qvars[i];
    BDD bvar = bddManager().bddVar(qvars[i]);
    int ws = whereSeen[index];
    if (ws >= 0) {
      int currentLimit = conjuncts[ws].nodeCount();
      BDD tmp = conjuncts[ws].ExistAbstract(bvar, currentLimit);
      if (tmp && tmp.nodeCount() <= currentLimit) {
        conjuncts[ws] = tmp;
#if 0
        cout << "Eliminated local variable " << index 
             << " from conjunct " << ws << endl;
#endif
      } else {
#if 0
        cout << "Failed to eliminate local variable " << index 
             << " from conjunct " << ws << endl;
#endif
        ret &= bvar;
      }
    } else {
      ret &= bvar;
    }
  }
  assert(qcube <= ret);
  if (verbosity > Options::Terse)
    cout << "Number of clusters/nodes = " << conjuncts.size()
         << "/" << bddManager().SharingSize(conjuncts) << endl;

  return ret;

} // BddTrAttachment::quantifyLocalInputs


/**
 * Compute the quantification schedule for the primary inputs and the
 * auxiliary variables.
 */
void BddTrAttachment::computeSchedule(
  const vector<BDD>& conjuncts,
  const BDD& wCube)
{
  vector<BDD> fwSchedule, bwSchedule;
  for (vector<BDD>::size_type i = 0; i != conjuncts.size(); ++i) {
    fwSchedule.push_back(bddManager().bddOne());
    bwSchedule.push_back(bddManager().bddOne());
  }
  _prequantx = bddManager().bddOne();
  _prequanty = bddManager().bddOne();

  // For each variable appearing in the conjuncts find the last
  // conjunct in which it appears.
  vector<int> lastSeen(bddManager().ReadSize(),-1);
  for (vector<BDD>::size_type i = 0; i != conjuncts.size(); ++i) {
    vector<unsigned int> support = conjuncts[i].SupportIndices();
    for (vector<unsigned int>::const_iterator j = support.begin();
         j != support.end(); ++j) {
      lastSeen[*j] = i;
    }
  }

  vector<unsigned int> wVars = wCube.SupportIndices();
#if 0
  printVector("wVars", wVars); // Diagnostic printout.
#endif
  for (vector<unsigned int>::size_type i = 0; i != wVars.size(); ++i) {
    unsigned int index = wVars[i];
    int ls = lastSeen[index];
    if (ls >= 0) {
      BDD var = bddManager().bddVar(index);
      fwSchedule[ls] &= var;
      bwSchedule[ls] &= var;
    }
  }

  for (vector<BDD>::size_type i = 0; i != _xvars.size(); ++i) {
    unsigned int index = _xvars[i].NodeReadIndex();
    int ls = lastSeen[index];
    if (ls >= 0) {
      fwSchedule[ls] &= _xvars[i];
    } else {
      _prequantx &= _xvars[i];
    }
  }

  for (vector<BDD>::size_type i = 0; i != _yvars.size(); ++i) {
    unsigned int index = _yvars[i].NodeReadIndex();
    int ls = lastSeen[index];
    if (ls >= 0) {
      bwSchedule[ls] &= _yvars[i];
    } else {
      _prequanty &= _yvars[i];
    }
  }

  for (vector<BDD>::size_type i = 0; i != conjuncts.size(); ++i) {
    _tr.push_back(RelPart(conjuncts[i], fwSchedule[i], bwSchedule[i]));
  }

} // BddTrAttachment::computeSchedule


/**
 * Eliminate auxiliary variables from output function.
 */
BDD BddTrAttachment::flattenOutput(
  const vector<BDD>& conjuncts,
  const BDD& wCube)
{
  vector<BDD> schedule;
  for (vector<BDD>::size_type i = 0; i != conjuncts.size(); ++i) {
    schedule.push_back(bddManager().bddOne());
  }

  // For each variable appearing in the conjuncts find the last
  // conjunct in which it appears.
  vector<int> lastSeen(bddManager().ReadSize(),-1);
  for (vector<BDD>::size_type i = 0; i != conjuncts.size(); ++i) {
    vector<unsigned int> support = conjuncts[i].SupportIndices();
    for (vector<unsigned int>::const_iterator j = support.begin();
         j != support.end(); ++j) {
      lastSeen[*j] = i;
    }
  }

  vector<unsigned int> wVars = wCube.SupportIndices();
#if 0
  printVector("wVars", wVars); // Diagnostic printout.
#endif
  for (vector<unsigned int>::size_type i = 0; i != wVars.size(); ++i) {
    unsigned int index = wVars[i];
    int ls = lastSeen[index];
    if (ls >= 0) {
      BDD var = bddManager().bddVar(index);
      schedule[ls] &= var;
    }
  }

  BDD ret = bddManager().bddOne();
  for (vector<BDD>::size_type i = 0; i != conjuncts.size(); ++i) {
    ret = ret.AndAbstract(conjuncts[i], schedule[i]);
  }
  return ret;

} // BddTrAttachment::flattenOutput


/**
 * Compute a linear arrangement of the conjuncts of the transition relation.
 */
vector<BDD> BddTrAttachment::linearArrangement(const vector<BDD>& conjuncts) const
{
  // Build dependence matrix.
  vector< vector<unsigned int> > depMat = dependenceMatrix(conjuncts);
  // Run force directed placement.
  vector<unsigned int> arrangement = forceDirectedArrangement(depMat);
  assert(conjuncts.size() == arrangement.size());
#if 0
  printVector("Chosen arrangement", arrangement); // Diagnostic printout.
#endif
  vector<BDD> ret;
  ret.resize(arrangement.size());
  for (vector<unsigned int>::size_type i = 0; i != arrangement.size(); ++i) {
    unsigned int posn = arrangement.size() - 1 - arrangement[i];
    ret[posn] = conjuncts[i];
  }
  assert(ret.size() == arrangement.size());
  return ret;

} // BddTrAttachment::linearArrangement


/**
 * Build the dependence matrix of the conjuncts.
 *
 * This is a sparse matrix.  Each row is a vector holding the variables
 * in the support of a conjunct.  Another way to look at this is that each
 * row is the list of hyperedges incident on a vertex of the hypergraph.
 */
vector< vector<unsigned int> > 
BddTrAttachment::dependenceMatrix(const vector<BDD>& conjuncts) const
{
  vector<vector<unsigned int>> mat;
  mat.reserve(conjuncts.size());
  for (vector<BDD>::const_iterator it = conjuncts.begin();
       it != conjuncts.end(); ++it) {
    mat.push_back(it->SupportIndices());
  }
#if 0
  // Diagnostic printout.
  for (vector< vector<unsigned int> >::const_iterator i = mat.begin();
       i != mat.end(); ++i) {
    const vector<unsigned int>& row = *i;
    printVector("Conjunct:", row);
  }
#endif
  return mat;

} // BddTrAttachment::dependenceMatrix


namespace {
  /**
   * Class of hypergraph vertices used by linear arrangement functions.
   */
  class Vertex {
  public:
    Vertex(unsigned int posn, double com = 0.0) : _posn(posn), _com(com) {}
    bool operator<(const Vertex& other) const { return _com < other._com; }
    unsigned int position() const {return _posn; }
    unsigned int com() const {return _com; }
    void setPosition(unsigned int posn) { _posn = posn; }
    void setCom(double com) { _com = com; }
  private:
    unsigned int _posn;
    double _com;
  };
}


/**
 * Force directed linear arrangement.
 */
vector<unsigned int> 
BddTrAttachment::forceDirectedArrangement(
  const vector< vector<unsigned int> >& depMat) const
{
  vector<unsigned int> arrangement;
  for (vector<unsigned int>::size_type i = 0; i != depMat.size(); ++i) {
    arrangement.push_back(i);
  }

  map<unsigned int, vector<unsigned int> > transpose = buildTranspose(depMat);

  unsigned int bestCost = computeCost(transpose, arrangement);
  vector<unsigned int> bestArrangement = arrangement;
  for (int iteration = 0; iteration < 30; ++iteration) {

    // Compute center of mass of each hyperedge.
    map<unsigned int, double> comHyper;
    for (map<unsigned int, vector<unsigned int> >::const_iterator it =
           transpose.begin(); it != transpose.end(); ++it) {
      unsigned int index = it->first;
      const vector<unsigned int>& hyperedge = it->second;
      double sum = 0.0;
      for (vector<unsigned int>::const_iterator i = hyperedge.begin();
           i != hyperedge.end(); ++i) {
        sum += (double) arrangement[*i];
      }
      double com = sum / (double) hyperedge.size();
      comHyper[index] = com;
    }
      
    // Compute center of mass of each vertex.
    vector<Vertex> sortVector;
    for (vector<double>::size_type i = 0; i != depMat.size(); ++i) {
      const vector<unsigned int>& vertex = depMat[i];
      double sum = 0.0;
      for (vector<unsigned int>::const_iterator it = vertex.begin();
           it != vertex.end(); ++it) {
        sum += comHyper[*it];
      }
      double com = sum / (double)vertex.size();
      sortVector.push_back(Vertex(i,com));
    }

    // Update arrangement.  
    // For partitioned transition relations, we should add the two fake
    // fixed conjuncts.
    sort(sortVector.begin(), sortVector.end());
    for (vector<Vertex>::size_type i = 0; i != sortVector.size(); ++i) {
      unsigned int posn = sortVector[i].position();
      arrangement[posn] = i;
    }
    unsigned int cost = computeCost(transpose, arrangement);
    if (cost < bestCost) {
      bestCost = cost;
      bestArrangement = arrangement;
    }
#if 0
    // Diagnostic printout.
    cout << "Iteration " << iteration << ": cost = " << cost << endl;
    cout << "Arrangement:";
    for (vector<unsigned int>::const_iterator it = arrangement.begin();
         it != arrangement.end(); ++it) {
      cout << " " << *it;
    }
    cout << endl;
#endif
  }

  return bestArrangement;

} // BddTrAttachment::forceDirectedArrangement


/**
 * Transpose the dependence matrix.
 *
 * Each hyperedge (variable index) is mapped to a vector holding the indices
 * of the vertices (conjuncts) adjeacent to the hyperedge.
 */
map<unsigned int, vector<unsigned int> > 
BddTrAttachment::buildTranspose(
  const vector< vector<unsigned int> >& depMat) const
{
  map<unsigned int, vector<unsigned int> > transpose;
  for (vector< vector<unsigned int> >::size_type i = 0;
       i != depMat.size(); ++i) {
    const vector< unsigned int>& row = depMat[i];
    for (vector<unsigned int>::const_iterator iter = row.begin();
         iter != row.end(); ++iter) {
      transpose[*iter].push_back((unsigned int) i);
    }
  }
#if 0
  // Diagnostic printout.
  for (map<unsigned int, vector<unsigned int> >::const_iterator it = 
         transpose.begin(); it != transpose.end(); ++it) {
    unsigned int index = it->first;
    const vector<unsigned int>& hyperedge = it->second;
    cout << "Hyperedge " << index << ":";
    printVector("", hyperedge);
  }
#endif
  return transpose;

} // BddTrAttachment::buildTranspose


/**
 * Compute the cost of a linear arrangement.
 *
 * The cost is the sum of the spans of all the hyperedges.
 */
unsigned int 
BddTrAttachment::computeCost(
  const map< unsigned int, vector<unsigned int> >& transpose,
  const vector<unsigned int>& arrangement) const
{
  unsigned int cost = 0;

  for (map< unsigned int, vector<unsigned int> >::const_iterator it =
         transpose.begin(); it != transpose.end(); ++it) {
    const vector<unsigned int>& hyperedge = it->second;
    unsigned int minposn = arrangement.size();
    unsigned int maxposn = 0;
    for (vector<unsigned int>:: const_iterator i = hyperedge.begin();
         i != hyperedge.end(); ++i) {
      if (arrangement[*i] < minposn)
        minposn = arrangement[*i];
      if (arrangement[*i] > maxposn)
        maxposn = arrangement[*i];
    }
    cost += (maxposn - minposn);
  }

  return cost;

} // BddTrAttachment::computeCost


/**
 * Prepare the BDD manager for a new phase.
 */
void BddTrAttachment::resetBddManager(const std::string bdd_to) const
{
  // Reset the maximum number of reorderings, but keep the reordering method.
  if (_model.options().count("bdd_reorderings")) {
    unsigned int numReorderings =
      _model.options()["bdd_reorderings"].as<unsigned int>();
    if (numReorderings > 0) {
      bddManager().SetMaxReorderings(numReorderings);
      bddManager().AutodynEnable(CUDD_REORDER_SAME);
    }
  } else {
    bddManager().AutodynEnable(CUDD_REORDER_SAME);
  }
  // Update timeout and reset start time.
  if (_model.options().count("bdd_timeout") &&
      _model.options().count(bdd_to)) {
    unsigned long timeout = 1000 * 
      _model.options()[bdd_to].as<unsigned long>();
    bddManager().IncreaseTimeLimit(timeout);
  }
  bddManager().ResetStartTime();

} // BddTrAttachment::resetBddManager


namespace {

  /**
   * Write a BDD to cout according to verbosity settings.
   */
  void reportBDD(
    string title, 
    BDD bdd,
    int nvars,
    Options::Verbosity verbosity,
    Options::Verbosity threshold)
  {
    // Map iimc verbosity to CUDD verbosity.
    int bddVerbosity = 0;
    if (verbosity == Options::Logorrheic) bddVerbosity = 2;
    else if (verbosity > Options::Terse) bddVerbosity = 1;
    if (verbosity > threshold) {
      cout << title;
      bdd.print(nvars,bddVerbosity);
    }
  } // reportBDD


  /**
   * Write a vector of T to cout.
   */
  template <class T>
  void printVector(const string& s, const vector<T>& v)
  {
    cout << s;
    typedef typename vector<T>::const_iterator vci;
    for (vci it = v.begin(); it != v.end(); ++it) {
      cout << " " << *it;
    }
    cout << endl;

  } // printVector

}
