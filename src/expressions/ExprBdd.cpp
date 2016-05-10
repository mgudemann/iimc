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
#include "ExprUtil.h"
#include "ExprBdd.h"
#include "CombAttachment.h"

#include <list>
#include <unordered_map>
#include <algorithm>

using namespace std;

namespace {

void updateCombAttachment(
  Model const & model,
  bool timedOut,
  unordered_map<ID, int>::size_type numAuxVar,
  unsigned int limit,
  unsigned int numPairs)
{
  CombAttachment *cat = 
    (CombAttachment *) model.attachment(Key::COMB);
  assert(cat != 0);
  CombAttachment::Effort currentEffort;
  if (timedOut)
    currentEffort = CombAttachment::Cursory;
  else if (numAuxVar == 0)
    currentEffort = CombAttachment::Complete;
  else if (limit > 1000) // somewhat arbitrary
    currentEffort = CombAttachment::Thorough;
  else if (limit > 500) // somewhat arbitrary
    currentEffort = CombAttachment::Medium;
  else
    currentEffort = CombAttachment::Cursory;
  CombAttachment::Effort previousEffort =
    cat->simplificationEffort();
  if (currentEffort > previousEffort)
    cat->simplificationEffort() = currentEffort;
  cat->numEquivalences() += numPairs;
  if(!timedOut) {
    //Update unusedTime
    if(model.options().count("bdd_sw_timeout")) {
      unsigned long timeout = 1000 * 
        model.options()["bdd_sw_timeout"].as<unsigned long>();
      unsigned long elapsed = model.bddManager().ReadElapsedTime();
      cat->unusedTime() += (timeout - elapsed) * 1000;
    }
  }
  else
    cat->unusedTime() = 0;

  model.release(cat);

} // updateCombAttachment

} // namespace


namespace Expr {

/**
 * Class for BDD sweeping.
 */
class bdd_sweep : public Manager::View::Folder {
public:
  /**
   * Constructor.
   */
  bdd_sweep(Manager::View& v, vector<ID>& ids,
            unordered_map<ID,int>& auxVarMap, IdBddMap& id2bdd,
            Cudd const & bddMgr, Options::Verbosity verb) :
    Manager::View::Folder(v), roots(ids), av2index(auxVarMap),
    i2b(id2bdd), bddMgr(bddMgr), nequiv(0), verbosity(verb) {
    BDD bdd_true = bddMgr.bddOne();
    ID id_true = v.btrue();
    DdNode *one = bdd_true.getNode();
    b2i[one] = id_true;
    i2b[id_true] = bdd_true;
  }

  ID fold(ID id, int n, const ID * const args) {
    // Check if this is the first element of its equivalence class.
    // If so, it becomes the representative.
    DdNode *tag = tags(id);
    DdNode *regtag = Cudd_Regular(tag);
    assert(regtag != 0);
    DdIdMap::const_iterator irep = b2i.find(regtag);
    bool replace = irep != b2i.end();
    ID replacement;
    if (replace) {
      ID representative = irep->second;
      DdNode *reptag = tags(representative);
      if (reptag == tag) {
        replacement = representative;
      } else {
        replacement = view().apply(Not, representative);
      }
      if (replacement != id && view().op(id) != Not) {
        nequiv++;
        if (verbosity > Options::Verbose)
          cout << id << (reptag == tag ? " is equivalent to " :
                         " is the negation of ") << representative << endl;
      }
    } else {
      replacement = Manager::View::Folder::fold(id, n, args);
      // If the function of id is an auxiliary variable,
      // the replacement may have a different BDD.
      DdNode *reptag = tags(replacement);
      if (i2b.find(replacement) != i2b.end() && reptag != tag) {
        assert(b2i.find(Cudd_Regular(reptag)) != b2i.end());
        replace = true;
        nequiv++;
        if (verbosity > Options::Verbose)
          cout << id << " is equivalent to " << replacement << endl;
      } else {
        b2i[regtag] = replacement;
      }
    }
    if (replacement != id) {
      // Adjust the auxiliary variable map if this ID is in it.
      unordered_map<ID,int>::iterator iav = av2index.find(id);
      if (iav != av2index.end()) {
        int index = iav->second;
        av2index.erase(iav);
        av2index[replacement] = index;
      }
      // Adjust the map from IDs to BDDs.
      IdBddMap::iterator iter = i2b.find(id);
      assert(iter != i2b.end());
      if (!replace) {
        BDD bdd = iter->second;
        i2b[replacement] = bdd;
      }
      i2b.erase(iter);
    }
    return replacement;
  }

  /**
   * Dispose of BDDs that are neither for the roots nor for the
   * nodes associated to auxiliary variables.  A root's BDD may have
   * been removed if it is an inverter.  Here we restore it before the
   * representative's BDD is lost to cleanup.
   */
  void cleanup() {
    unordered_set<ID> rootset;
    for (vector<ID>::const_iterator it = roots.begin();
         it != roots.end(); ++it) {
      rootset.insert(*it);
      if (i2b.find(*it) == i2b.end()) {
        ID negation = view().apply(Not, *it);
        if (negation == view().btrue()) {
          i2b[*it] = bddMgr.bddZero();
        } else {
          IdBddMap::const_iterator bit = i2b.find(negation);
          assert(bit != i2b.end());
          i2b[*it] = !(bit->second);
        }
      }
    }
    for (unordered_map<ID,int>::const_iterator it = av2index.begin();
         it != av2index.end(); ++it) {
      rootset.insert(it->first);
      if (i2b.find(it->first) == i2b.end()) {
        ID negation = view().apply(Not, it->first);
        assert(i2b.find(negation) != i2b.end());
        i2b[it->first] = !i2b[negation];
      }
    }
    IdBddMap::iterator tmpIt;
    for (IdBddMap::iterator it = i2b.begin(); it != i2b.end(); it = tmpIt) {
      tmpIt = it;
      tmpIt++;
      if (rootset.find(it->first) == rootset.end())
        i2b.erase(it);
    }
  }

  /** Return the number of equivalent pairs. */
  unsigned int equivalentPairs() { return nequiv; }

private:
  typedef unordered_map<DdNode *, ID> DdIdMap;

  /** The unique DdNode address of the BDD is used as tag of
   *  an equivalence class. */
  DdNode* tags(ID id) {
    IdBddMap::const_iterator iter = i2b.find(id);
    if (iter == i2b.end())
      return 0;
    else
      return iter->second.getNode();
  }

  vector<ID>& roots;
  unordered_map<ID,int>& av2index;
  IdBddMap& i2b;
  Cudd const & bddMgr;
  DdIdMap b2i;
  unsigned int nequiv;
  Options::Verbosity verbosity;
};

/**
 * Class for fanout counting.  
 *
 * Used to find the number of parents backward-reachable from the roots.
 */
class node_fanout : public Manager::View::Folder {
public:
  /**
   * Constructor.
   */
  node_fanout(Manager::View& v, unordered_map<ID, unsigned int>& cnt) :
    Manager::View::Folder(v), count(cnt) {}
  /**
   * Count the fanouts of nodes that reach the roots.
   */
  ID fold(ID id, int n, const ID * const args) {
    for (int i = 0; i != n; ++i) {
      count[args[i]]++;
    }
    return id;
  }
private:
  unordered_map<ID, unsigned int>& count;
};


/**
 * Class for BDD folding.
 */
class bdd_folder : public Manager::View::Folder {
public:
  /**
   * Constructor.
   */
  bdd_folder(Manager::View& v, Cudd const & bddMgr, 
             unordered_map<ID, int>& orderMap, 
             unordered_map<ID, int>& auxVarMap, IdBddMap& id2bdd,
             unordered_map<ID, unsigned int>& count, 
             unsigned int limit, bool swp, Options::Verbosity verb) : 
    Manager::View::Folder(v), bddMgr(bddMgr), orderMap(orderMap),
    auxVarMap(auxVarMap), i2b(id2bdd), count(count),
    limit(limit), sweep(swp), verbosity(verb) {  /*id2bdd[0] = bddMgr.bddOne();*/ }
  /**
   * Build the BDD for an expression node given the BDDs of its arguments.
   *
   * If the order is complete, it is used, and otherwise BDD indices are
   * assigned to variables as they are encountered.
   */
  ID fold(ID id, int n, const ID * const args) {
    assert(i2b.find(id) == i2b.end());
    Op op = view().op(id);
    BDD f;
    switch(op) {
    case True:
      assert(n == 0);
      f = bddMgr.bddOne();
      break;
    case Var:
      assert(n == 0);
      if (orderMap.find(id) == orderMap.end()) {
        f = bddMgr.bddVar();
        orderMap[id] = f.NodeReadIndex();
      } else {
        f = bddMgr.bddVar(orderMap[id]);
      }
      break;
    case Not:
      assert(n == 1);
      f = ~bdd(args[0]);
      break;
    case And:
      assert(n>1);
      f = bdd(args[0]) & bdd(args[1]);
      for (int i = 2; i != n; ++i) {
        f &= bdd(args[i]);
      }
      break;
    case Or:
      assert(n>1);
      f = bdd(args[0]) | bdd(args[1]);
      for (int i = 2; i != n; ++i) {
        f |= bdd(args[i]);
      }
      break;
    case Equiv:
      assert(n == 2);
      f = bdd(args[0]).Xnor(bdd(args[1]));
      break;
    case ITE:
      assert(n == 3);
      f = bdd(args[0]).Ite(bdd(args[1]), bdd(args[2]));
      break;
    default:
      assert(false);
    }
    i2b[id] = f;
    // Check if an auxiliary variable should be inserted.
    if (limit > 0 && f.nodeCount() > (int) limit) {
      unordered_map<DdNode *, int>::const_iterator ait = nodeToVarIndex.find(f.getNode());
      if (ait == nodeToVarIndex.end()) {
        if (verbosity > Options::Verbose)
          cout << "Auxiliary variable for " << id << endl;
        int newIndex = bddMgr.bddVar().NodeReadIndex();
        auxVarMap[id] = newIndex;
        nodeToVarIndex[f.getNode()] = newIndex;
      } else {
        if (verbosity > Options::Verbose)
          cout << "Shared auxiliary variable for " << id << endl;
        auxVarMap[id] = ait->second;
      }
      if (!sweep)
        count[id]++;
    }
    // Update fanout counters and dispose of BDDs that are no longer needed.
    if (!sweep) {
      for (int i = 0; i != n; ++i) {
        ID arg = args[i];
        int cnt = --count[arg];
        if (cnt == 0) {
          b_iter it = i2b.find(arg);
          assert(it != i2b.end());
          i2b.erase(it);
        }
      }
    }
    return id;
  }
private:
  typedef IdBddMap::iterator b_iter;
  /** Find the BDD for an ID.  First check whether an auxiliary variable
   *  has been created for this ID or its negation.  If not, then the
   *  ID must have an entry in the index-to-BDD map. */
  BDD bdd(ID argId) {
    unordered_map<ID, int>::const_iterator it = auxVarMap.find(argId);
    if (it == auxVarMap.end()) {
      ID negation = view().apply(Not, argId);
      unordered_map<ID, int>::const_iterator nit = auxVarMap.find(negation);
      if (nit == auxVarMap.end())
        return i2b[argId];
      else
        return !(bddMgr.bddVar(nit->second));
    } else {
      return bddMgr.bddVar(it->second);
    }
  }
  Cudd const & bddMgr;
  unordered_map<ID, int>& orderMap;
  unordered_map<ID, int>& auxVarMap;
  unordered_map<DdNode *, int> nodeToVarIndex;
  IdBddMap& i2b;
  unordered_map<ID, unsigned int>& count;
  unsigned int limit;
  bool sweep;
  Options::Verbosity verbosity;
};


BDD bddOf(Manager::View & v, ID id, Model const & model,
          unordered_map<ID, int>& orderMap, 
          unordered_map<ID, int>& auxVarMap, unsigned int limit,
          bool sweep, Options::Verbosity verbosity)
{
  vector<ID> ids(1,id);
  IdBddMap id2bdd = bddOf(v, ids, model, orderMap, auxVarMap,
                          limit, sweep, verbosity);
  // In case of timeout, we may not have a BDD for id.
  IdBddMap::iterator it = id2bdd.find(id);
  if (it == id2bdd.end())
    return BDD();
  else
    return it->second;
}


IdBddMap bddOf(Manager::View & v, vector<ID> & ids, Model const & model, 
               unordered_map<ID, int>& orderMap,
               unordered_map<ID, int>& auxVarMap, unsigned int limit,
               bool sweep, Options::Verbosity verbosity)
{
  Cudd const & bddMgr = model.bddManager();
  unordered_map<ID, unsigned int> count;
  if (!sweep) {
    // Protect roots.
    for (vector<ID>::const_iterator i = ids.begin(); i != ids.end(); ++i)
      count[*i] = 1;
    node_fanout nfo(v, count);
    v.fold(nfo, ids);
  } else {
    if (verbosity > Options::Terse)
      cout << "Initial node count = " << sizeOf(v, ids) << endl;
  }
  IdBddMap id2bdd;
  bdd_folder bddf(v, bddMgr, orderMap, auxVarMap, id2bdd,
                  count, limit, sweep, verbosity);
  bool timedOut = false;
  try {
    v.fold(bddf, ids);
  } catch (Timeout& e) {
    if (verbosity > Options::Silent)
      cout << e.what() << endl;
    timedOut = true;
    bddMgr.ClearErrorCode();
    bddMgr.UnsetTimeLimit();
    bddMgr.ResetStartTime();
  }
  if (sweep) {
    bdd_sweep bdds(v, ids, auxVarMap, id2bdd, bddMgr, verbosity);
    v.fold(bdds, ids);
    if (verbosity > Options::Silent) {
      cout << "Found " << bdds.equivalentPairs()
           << " equivalent node pairs" << endl;
      if (verbosity > Options::Terse)
        cout << "Final node count = " << sizeOf(v, ids) << endl;
    }
    if (!timedOut)
      bdds.cleanup();
    updateCombAttachment(model, timedOut, auxVarMap.size(), limit,
                         bdds.equivalentPairs());
  }
  if (timedOut) {
    id2bdd.clear();
    auxVarMap.clear();
  }
  assert(id2bdd.size() <= ids.size() + auxVarMap.size());
  return id2bdd;

} // bddOf


BDD bddOf(Manager::View & v, ID id, Cudd const & bddMgr,
          unordered_map<ID, int>& orderMap,
          unordered_map<ID, int>& auxVarMap, unsigned int limit,
          Options::Verbosity verbosity)
{
  vector<ID> ids(1,id);
  IdBddMap id2bdd = bddOf(v, ids, bddMgr, orderMap, auxVarMap,
                          limit, verbosity);
  // In case of timeout, we may not have a BDD for id.
  IdBddMap::iterator it = id2bdd.find(id);
  if (it == id2bdd.end())
    return BDD();
  else
    return it->second;
}


IdBddMap bddOf(Manager::View & v, vector<ID> & ids,
               Cudd const & bddMgr, unordered_map<ID, int>& orderMap,
               unordered_map<ID, int>& auxVarMap, unsigned int limit,
               Options::Verbosity verbosity)
{
  unordered_map<ID, unsigned int> count;
  for (vector<ID>::const_iterator i = ids.begin(); i != ids.end(); ++i)
    count[*i] = 1;
  node_fanout nfo(v, count);
  v.fold(nfo, ids);
  IdBddMap id2bdd;
  bdd_folder bddf(v, bddMgr, orderMap, auxVarMap, id2bdd,
                  count, limit, false, verbosity);
  try {
    v.fold(bddf, ids);
  } catch (Timeout& e) {
    if (verbosity > Options::Silent)
      cout << e.what() << endl;
    bddMgr.ClearErrorCode();
    bddMgr.UnsetTimeLimit();
    bddMgr.ResetStartTime();
    id2bdd.clear();
    auxVarMap.clear();
  }
  assert(id2bdd.size() <= ids.size() + auxVarMap.size());
  return id2bdd;

} // bddOf


  /**
   * Class to compare nodes according to two prioritized criteria.
   */
template <class First, class Second>
class lexPair {
public:
  lexPair(const First f, const Second s) : first(f), second(s) {}
  bool operator<(const lexPair<First, Second> other) const {
    if (first < other.first)
      return true;
    else 
      return first == other.first && second < other.second;
  }
  bool operator>(const lexPair<First, Second> other) const {
    if (first > other.first)
      return true;
    else 
      return first == other.first && second > other.second;
  }
private:
  First first;
  Second second;
};


/**
 * Class to compare items for sorting.
 *
 * Used when the ranking function is given as an unordered_map and
 * the values support the greater than operator.
 */
template <class Key, class Val>
class compareByRank {
public:
  compareByRank(unordered_map<Key, Val> const & rnk) : rank(rnk) {}
  bool operator()(const Key x, const Key y) const {
    typedef typename unordered_map<Key, Val>::const_iterator rci;
    rci ix = rank.find(x);
    assert(ix != rank.end());
    rci iy = rank.find(y);
    assert(iy != rank.end());
    return ix->second > iy->second;
  }
private:
  unordered_map<Key, Val> const & rank;
};


/**
 * Class to compute the height of nodes.
 *
 * The height of a node is the maximum distance from the leaves of
 * the expression DAG.
 */
class node_height : public Manager::View::Folder {
public:
  node_height(Manager::View& v, unordered_map<ID, unsigned int>& h) 
    : Manager::View::Folder(v), height(h) {
    assert(height.size() == 0);
  }
  ID fold(ID id, int n, const ID * const args) {
    assert(height.find(id) == height.end());
    if (n == 0) {
      height[id] = 0;
    } else if (n == 1 && view().op(id) == Not) {
      height[id] = height[args[0]];
    } else {
      unsigned int dfi = 0;
      for (int i = 0; i != n; ++i) {
        dfi = max(dfi, height[args[i]]);
      }
      height[id] = dfi + 1;
    }
    return id;
  }
private:
  unordered_map<ID, unsigned int>& height;
};


/**
 * Algorithm 2 of Fujii et al. (ICCAD-93).
 *
 * The second argument to the constructor is the ranking function to decide
 * the order in which to visit the fanins of a node.
 */
template <class Rank>
class Interleaver {
public:
  Interleaver(Manager::View& view, unordered_map<ID, Rank> const & rnk)
    : v(view), rank(rnk) {}
  void resetLast() { last = glist.end(); }
  list<ID> const & gateList() const { return glist; }
  void order(ID gate, ID output)
  {
    unordered_map<ID, list<ID>::iterator>::iterator m = mark.find(gate);
    if (m != mark.end()) {
      assert(from.find(gate) != from.end());
      if (from[gate] != output) {
        last = m->second;
        from[gate] = output;
      }
      return;
    }
    from[gate] = output;
    int nfi;
    ID const *fanins = v.arguments(gate, &nfi);
    ID *sfa = new ID[nfi];
    copy(fanins, fanins+nfi, sfa);
    stable_sort(sfa, sfa+nfi, compareByRank<ID, Rank>(rank));
#if 0
    int f2up = 0;
    int f1 = nfi - 1;
    int ii = 0;
    while (ii < f1) {
      ID fanin = sfa[ii];
      if (v.op(fanin) == Var) {
        unordered_map<ID, unsigned int>::const_iterator iter = rank.find(fanin);
        if (iter->second > 1) {
          sfa[ii] = sfa[f2up];
          sfa[f2up] = fanin;
          f2up++;
          ii++;
        } else {
          sfa[ii] = sfa[f1];
          sfa[f1] = fanin;
          f1--;
        }
      } else {
        ii++;
      }
    }
#endif
    for (int i = 0; i != nfi; ++i)
      order(sfa[i],output);
    delete[] sfa;
    if (last != glist.end())
      ++last;
    last = glist.insert(last,gate);
    mark[gate] = last;
  }
private:
  Manager::View& v;
  unordered_map<ID, Rank> const & rank;
  list<ID>::iterator last;
  list<ID> glist;
  unordered_map<ID, ID> from;
  unordered_map<ID, list<ID>::iterator > mark;
};


vector<ID> bddOrderOf(Manager::View& v, ID root) {
  vector<ID> roots(1,root);
  return bddOrderOf(v, roots);
}


vector<ID> bddOrderOf(Manager::View& v, vector<ID>& roots)
{
  // Find heights of all nodes and sort roots accordingly.
  unordered_map<ID, unsigned int> height;
  node_height nd(v, height);
  v.fold(nd, roots);
  stable_sort(roots.begin(), roots.end(), compareByRank<ID, unsigned int>(height));
#if 0
  for (vector<ID>::const_iterator it = roots.begin(); it != roots.end(); ++it)
    cout << *it << ": " << height[*it] << " ";
  cout << endl;
#endif

  // Compute number of fanouts.
  unordered_map<ID, unsigned int> count;
  node_fanout nfo(v, count);
  v.fold(nfo, roots);
#if 0
  vector<ID> allNodes;
  for (unordered_map<ID, unsigned int>::const_iterator it = count.begin();
       it != count.end(); ++it)
    allNodes.push_back(it->first);
  stable_sort(allNodes.begin(), allNodes.end(), 
              compareByRank<ID, unsigned int>(count));
  for (vector<ID>::const_iterator it = allNodes.begin(); 
       it != allNodes.end(); ++it) {
    if (count[*it] > 1)
      cout << *it << ": " << count[*it] << " ";
  }
  cout << endl;
#endif
  // Create ranking function.
  unsigned int maxHeight = roots.empty() ? 0 : height[roots[0]];
  unordered_map<ID, lexPair<unsigned int, unsigned int> > ranking;
  for (unordered_map<ID, unsigned int>::const_iterator i = count.begin();
       i !=  count.end(); ++i) {
    ID id = i->first;
    unsigned int cnt = i->second;
    ID neg = v.apply(Not, id);
    unordered_map<ID, unsigned int>::iterator nit = count.find(neg);
    if (nit != count.end()) {
      cnt += nit->second - 1;
    }
    unordered_map<ID, unsigned int>::iterator hit = height.find(id);
    assert(hit != height.end());
    assert(maxHeight >= hit->second);
    unsigned int ht = maxHeight - hit->second;
    ranking.insert(pair<ID, lexPair<unsigned int, unsigned int> >
                   (id, lexPair<unsigned int, unsigned int>(cnt, ht)));
  }

  // Now run the interleaving algorithm.
  Interleaver< lexPair<unsigned int, unsigned int> > ilv(v, ranking);
  for (vector<ID>::const_iterator i = roots.begin(); 
       i != roots.end(); ++i) {
    ilv.resetLast();
    ilv.order(*i, *i);
  }

  // Copy (local) list to vector to be returned.
  vector<ID> gateList;
  copy(ilv.gateList().begin(), ilv.gateList().end(), back_inserter(gateList));

  return gateList;
}


/**
 * Class to collect all the nodes reachable from a set of roots.
 */
class collect : public Manager::View::Folder {
public:
  collect(Manager::View& v, vector<ID> & all)
    :  Manager::View::Folder(v), nodes(all) {}
  ID fold(ID id, int n, const ID * const args) {
    nodes.push_back(id);
    return id;
  }
private:
  vector<ID>& nodes;
};

/**
 * Class to compute the center of mass of nodes for linear ordering.
 */
class node_com : public Manager::View::Folder {
public:
  node_com(Manager::View& v, unordered_map<ID, int>& vcom,
           unordered_map<ID, unsigned int> & position,
           unordered_map<ID, unsigned int> & cnt)
    :  Manager::View::Folder(v), vercom(vcom), posn(position), count(cnt) {}
  ID fold(ID id, int n, const ID * const args) {
    if (view().op(id) == Var) {
      vercom[id] = - (int) posn[id];
    } else {
      for (int i = 0; i != n; ++i) {
        ID fi = args[i];
        vercom[fi] += (int) posn[id] - (int) posn[fi];
      }
    }
    return id;
  }
private:
  unordered_map<ID, int>& vercom;
  unordered_map<ID, unsigned int> & posn;
  unordered_map<ID, unsigned int> & count;
};


vector<ID> linearOrderOf(Manager::View& v, ID root) {
  vector<ID> roots(1,root);
  return linearOrderOf(v, roots);
}


vector<ID> linearOrderOf(Manager::View& v, vector<ID>& roots)
{
  // Compute number of fanouts.
  unordered_map<ID, unsigned int> count;
  node_fanout nfo(v, count);
  v.fold(nfo, roots);

  // Build initial arrangement.
  vector<ID> arrangement;
  collect coll(v, arrangement);
  v.fold(coll, roots);
  unsigned int nnodes = arrangement.size();

  for (int i = 0; i < 50; ++i) {
    unordered_map<ID, unsigned int> posn;
    for (vector<ID>::size_type i = 0; i != nnodes; ++i) {
      posn[arrangement[i]] = i;
    }

    unordered_map<ID, int> vercom;
    node_com nc(v, vercom, posn, count);
    v.fold(nc, roots);

    for (vector<ID>::const_iterator it = roots.begin();
         it != roots.end(); ++it) {
      vercom[*it] += (int) nnodes - (int) posn[*it];
    }

    stable_sort(arrangement.begin(), arrangement.end(), compareByRank<ID, int>(vercom));

  }
  return arrangement;
}

} // namespace Expr
