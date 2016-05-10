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

#include "Util.h"
#include "ExprUtil.h"
#include "Simplifier.h"
#include "BddAttachment.h"
#include "Decode.h"
#include <queue>

using namespace std;

/** Class of exceptions to throw when we are lost.
 */
class DecodeException: public runtime_error
{
public:
  DecodeException(string const & message)
  : runtime_error(message) {}
};


/** Class to perform union-find on a set of IDs.  It is used to
 *  partition a set of nodes into subsets with disjoint support.
 */
class UF {
public:
  UF(vector<ID> const & v);
  size_t count(void) const { return cnt; }
  bool connected(ID p, ID q) { return find(p) == find(q); }
  ID find(ID p);
  void unite(ID p, ID q);
private:
  unordered_map<ID,ID> id;
  unordered_map<ID,size_t> sz;
  size_t cnt;
};


UF::UF(vector<ID> const & v)
{
  for (vector<ID>::const_iterator it = v.begin(); it != v.end(); ++it) {
    id.insert(unordered_map<ID,ID>::value_type(*it, *it));
    sz.insert(unordered_map<ID,size_t>::value_type(*it, 1));
  }
  cnt = v.size();
}


ID UF::find(ID p)
{
  unordered_map<ID,ID>::iterator it = id.find(p);
  assert(it != id.end());
  ID rep = it->second;
  // Apply path compression.
  if (p != rep) {
    rep = find(rep);
    id[p] = rep;
  }
  return rep;
}


void UF::unite(ID p, ID q)
{
  // Give p and q the same root.
  ID i = find(p);
  ID j = find(q);

  // Nothing to do if p and q are already in the same component.
  if (i == j)
    return;

  // Make smaller root point to larger one.
  if (sz[i] <= sz[j]) {
    id[i] = j;
    sz[j] += sz[i];
  } else {
    id[j] = i;
    sz[i] += sz[j];
  }
  --cnt;
}


/** Class to perform union-find with negation on a set of IDs.  It is used to
 *  find sets of variables that are either equivalent or complementary.  This
 *  class uses negation of the representative to deal with complementarity.
 *  Every class is divided into two phases: positive and negative.
 *  The first class is for constants, with "true" as its representative.
 */
class UFN {
public:
  UFN(Expr::Manager::View & view, vector<ID> const & v);
  size_t count(void) const { return cnt; }
  /** Returns true iff two variables are in the same phase of the same class. */
  bool equivalent(ID p, ID q) { return find(p) == find(q); }
  /** Returns true iff two variables are in opposite phases of the same class. */
  bool complementary(ID p, ID q) { return find(p) == ev.apply(Expr::Not, find(q)); }
  /** Returns the representative of a variable. */
  ID find(ID p);
  /** Prints the list of variables, each with its representative. */
  void print(void) const;
  /** Enforce equivalence between two variables. */
  void makeEquivalent(ID p, ID q);
  /** Enforce complementarity of two variables. */
  void makeComplementary(ID p, ID q);
private:
  ID neg(ID p) { return ev.apply(Expr::Not, p); }
  ID regular(ID p) { return ev.op(p) == Expr::Not ? ev.apply(Expr::Not, p) : p; }
  bool isNot(ID p) { return ev.op(p) == Expr::Not; }
  bool isVar(ID p) { return ev.op(p) == Expr::Var; }
  bool isConst(ID p) { return p == ev.btrue() || p == ev.bfalse(); }

  Expr::Manager::View & ev;
  unordered_map<ID,ID> id;
  unordered_map<ID,size_t> sz;
  size_t cnt;
};


UFN::UFN(Expr::Manager::View & view, vector<ID> const & v) : ev(view)
{
  id.insert(unordered_map<ID,ID>::value_type(ev.btrue(), ev.btrue()));
  sz.insert(unordered_map<ID,size_t>::value_type(ev.btrue(), 1));
  for (vector<ID>::const_iterator it = v.begin(); it != v.end(); ++it) {
    id.insert(unordered_map<ID,ID>::value_type(*it, *it));
    sz.insert(unordered_map<ID,size_t>::value_type(*it, 1));
  }
  cnt = v.size() + 1;
}


ID UFN::find(ID p)
{
  assert(isVar(p) || isConst(p));
  unordered_map<ID,ID>::iterator it = id.find(p);
  assert(it != id.end());
  ID rep = it->second;
  assert(p != neg(rep));
  // Apply path compression.
  if (p != rep) {
    bool complement = isNot(rep);
    rep = find(regular(rep));
    if (complement)
      rep = neg(rep);
    id[p] = rep;
  }
  return rep;
}


void UFN::makeEquivalent(ID p, ID q)
{
  assert(isVar(p));
  assert(isVar(q) || isConst(q));
  // Give p and q the same root.
  ID i = find(p);
  ID j = find(q);

  // Nothing to do if p and q are already in the same phase of the same class.
  if (i == j)
    return;

  // If they are already complementary we have contradictory requirements.
  if (i == neg(j))
    throw DecodeException("contradiction");

  // Make smaller root point to larger one except for the constant,
  // which we always want as root of its group.
  if ((sz[regular(i)] <= sz[regular(j)] && !isConst(i)) || isConst(j)) {
    id[regular(i)] = isNot(i) ? neg(j) : j;
    sz[regular(j)] += sz[regular(i)];
  } else {
    id[regular(j)] = isNot(j) ? neg(i) : i;
    sz[regular(i)] += sz[regular(j)];
  }
  --cnt;
}


void UFN::makeComplementary(ID p, ID q)
{
  assert(isVar(p));
  assert(isVar(q) || isConst(q));
  // Give p and q the same root.
  ID i = find(p);
  ID j = find(q);

  // Nothing to do if p and q are already in opposite phases of the same class.
  if (i == neg(j))
    return;

  // If they are already equivalent, we have contradictory requirements.
  if (i == j)
    throw DecodeException("contradiction");

  // Make smaller root point to larger one except for the constant,
  // which we always want as root of its group.
  if ((sz[regular(i)] <= sz[regular(j)] && !isConst(i)) || isConst(j)) {
    id[regular(i)] = isNot(i) ? j : neg(j);
    sz[regular(j)] += sz[regular(i)];
  } else {
    id[regular(j)] = isNot(j) ? i : neg(i);
    sz[regular(i)] += sz[regular(j)];
  }
  --cnt;
}


void UFN::print(void) const
{
  cout << "Current map (" << cnt << ") classes" << endl;
  for (unordered_map<ID,ID>::const_iterator it = id.begin();
       it != id.end(); ++it)
    cout << stringOf(ev, it->first) << " -> "
         << stringOf(ev, it-> second) << endl;
}


namespace Expr {

  /** Class to convert BDDs to expressions.
   */
  class BddToExpr {
  public:
    BddToExpr(Manager::View & v, unordered_map<int,ID> const & itv) : ev(v), indexToVarID(itv) {}
    ID convert(BDD const & F);
  private:
    ID convert(DdManager *mgr, DdNode * f);
    Manager::View & ev;
    unordered_map<int, ID> indexToVarID;
    unordered_map<DdNode*,ID> computedTable;
  };


  ID BddToExpr::convert(BDD const & F)
  {
    DdManager *mgr = F.manager();
    DdNode *node = F.getNode();
    return convert(mgr, node);
  }


  ID BddToExpr::convert(DdManager *mgr, DdNode * f)
  {
    if (f == Cudd_ReadOne(mgr))
      return ev.btrue();
    if (f == Cudd_ReadLogicZero(mgr))
      return ev.bfalse();

    unordered_map<DdNode*,ID>::const_iterator mit = computedTable.find(f);
    if (mit != computedTable.end())
      return mit->second;

    bool complement = Cudd_IsComplement(f);
    int index = Cudd_NodeReadIndex(f);
    ID var = indexToVarID[index];
    DdNode *T = Cudd_T(f);
    DdNode *E = Cudd_E(f);
    ID Tid = convert(mgr, T);
    ID Eid = convert(mgr, E);
    ID andT = ev.apply(And, var, Tid);
    ID andE = ev.apply(And, ev.apply(Not, var), Eid);
    ID result = ev.apply(And, ev.apply(Not, andT), ev.apply(Not, andE));
    if (!complement)
      result = ev.apply(Not, result);
    computedTable.insert(unordered_map<DdNode*,ID>::value_type(f, result));
    return result;
  }


  /** Class used to analyze a model to decide whether it uses
   *  relational encoding.  If so, to find the direction
   *  and collect information useful to decoding. */
  class PatternMatch : public Manager::View::Folder {
  public:
    PatternMatch(Manager::View & v, vector<ID> const & ins,
                 vector<ID> const & sv, vector<ID> const & nsf,
                 ID out, Options::Verbosity verb) :
      Manager::View::Folder(v), inputs(ins), stateVars(sv),
      nextStateFns(nsf), output(out), verbosity(verb)
    {
      extract();
    }

    /** Check whether the model is encoded in the given direction.
     */
    bool isEncoded(bool forward);

    /** Check whether the model is encoded in forward fully relational style.
     */
    bool isRelEncoded(void);

    /** Check whether the model has init and valid bits.
     */
    bool hasInitAndValid(void);

#if 0
    /** Replace the extracted equalities with true in the AND tree
     * of the transition relation. */
    ID fold(ID id, int n, const ID * const args);
#endif

    /** Prepare for a new encoding check.
    */
    void reset(void) {
      tunit.clear(); nreq.clear(); exts.clear();
      equivs.clear(); initRel.clear(); ireq.clear(); initLits.clear();
      rblocks.clear(); iblocks.clear(); iunit.clear(); isubmap.clear();
      tsubmap.clear();
    }

    /** Accessors. */
    ID getValid(void) const { return valid; }
    ID getFirst(void) const { return first; }
    ID getLast(void) const { return last; }
    unordered_map<ID,ID> const & latchMap(void) const { return latchmap; }
    unordered_map<ID,ID> const & latchInputMap(void) const { return limap; }
    unordered_map<ID,ID> const & inputLatchMap(void) const { return ilmap; }
    unordered_map<ID,ID> const & equivalences(void) const { return equivs; }
    vector<ID> const & extras(void) const { return exts; }
    unordered_map<ID, vector<ID> > const & relBlocks(void) const {return rblocks; }
    unordered_map<ID, vector<ID> > const & initBlocks(void) const {return iblocks; }
    unordered_map<ID,ID> const & initSubMap(void) const {return isubmap; }
    unordered_map<ID,ID> const & trelSubMap(void) const {return tsubmap; }
    vector<ID> const & initLiterals(void) const { return initLits; }
    ID initialized(void) const { return init; }
    ID delayedInitialized(void) const { return delInit; }
    vector<ID>::size_type initializedPosition(void) const { return initPos; }

  private:

    /** Extract information from the model.
     */
    void extract(void);

    /** Check for essential features of encoded models.
     */
    bool isInteresting(void);

    /** Find the encoding primary input for each latch.
     *  Encoded latches are those directly fed by a primary input.
     *  valid and initialized are not encoded.  This function fills two
     *  maps that allow us to go back and forth between latches and their
     * encoding inputs.
     */
    void findEncondingPairs(void);

    /** Find the initialized latch by looking for a next-state function
     *  identically equal to 1.
     */
    void findInitialized(void);

    /** Find the delayed version of initialized (if there is one).
     */
    void findDelayedInitialized(void);

    /** Search for valid bit.  In the process find also the nodes
     * implementing the transition relation, the first-state constraint,
     * and the last-state constraint.  Depending on the direction of encoding
     * the first-state constraint describes initial states or bad states.
     * Similarly for the last-state constraint.
     */
    void findValid(void);

    /** Check whether a set of variables is contained in the set
     *  of the encoding primary inputs.
     */
    bool areMappedInputs(set<ID> const & vars);

    /** Check whether a set of variables is contained in the set
     *  of the encoded latches.
     */
    bool areMappedLatches(set<ID> const & vars);

    /** Check whether a set of variables is made up of primary inputs. */
    bool arePrimaryInputs(set<ID> const & vars);

    /** Check support of next-state functions and constraints. */
    bool checkSupports(bool forward);

    /** Check support of next-state functions and constraints
     *  for full relational models.  A model that qualifies for
     *  full relational decoding is such that:
     *  - The initial-state relation depends on primary inputs.
     *  - The transition relation depends on primary inputs and
     *    latches, but not on "valid."
     *  - The bad-state function depends on mapped latches or
     *    delayed init.
     */
    bool checkRelSupport(void);

    /** Check whether ID is the output of an equivalence function. */
    bool isEquivStruct(ID id, ID const * args, ID const ** args0,
                       ID const ** args1);

    /** Check whether id is the output gate of an equivalence gate
     *  whose inputs are a state variable and its next state function.
     *  The inputs of the And gate are in args.  The forward flag
     *  gives the encoding direction and determines whether one of the
     *  inputs should be the latch (backward encoding) or the encoding
     *  primary input (forward encoding).
     */
    bool isEquiv(ID id, ID const * const args, bool forward);

    /** Check whether id is the output gate of an equivalence gate
     *  whose inputs are two mapped inputs.
     */
    bool isEquivInit(ID id, ID const * const args);

    /** Check whether id is the output gate of an equivalence gate
     *  whose inputs are two mapped latches.
     */
    bool isEquivTran(ID id, ID const * const args);

    /** Explore the AND tree of the transition relation and extract
     *  equivalences and the rest.
     */
    void gather(ID id, bool forward);

    /** Explore the AND tree of the initial state relation and
     *  extract interesting conjuncts.
     */
    void gatherInit(ID id);

    /** Explore the AND tree of the transition relation and
     *  extract interesting conjuncts.
     */
    void gatherTran(ID id);

    /** Check whether the model contains an equivalence for every
     *  encoded latch.
     */
    bool foundAllEquivalences(void) const;

    /** Group conjuncts of the transition relation according to support.
     */
    void groupTrelConjuncts(void);

    /** Group conjuncts of the initial relation according to support.
     */
    void groupInitConjuncts(void);

    /** Check whether superset contains subset. */
    bool inSet(unordered_set<ID> const & superset, set<ID> const & subset);

    /** Extract from an AND tree of literals a vector of those literals.
     *  Return true if successful; false otherwise.
     */
    bool unravelInitialCube(ID cube, unordered_map<ID,ID> const & map);

    /** Extract the two variables from an expression that asserts
     *  their equivalence or complementarity and return true iff
     *  the variables are equivalent.
     */
    bool unpackEquiv(ID eq, ID & v1, ID & v2);

    /** Divide input variables into classes depending on whether they are
     *  constant, equivalent to other variables, or complementary to other
     *  variables in the initial-state relation.  The information is
     *  collected in "isubmap" and "first" is simplified accordingly.
     */
    void prepareInitRel(void);

    /** Divide input variables into classes depending on whether they are
     *  constant, equivalent to other variables, or complementary to other
     *  variables in the transition relation.  The information is
     *  collected in "tsubmap" and "trel" is simplified accordingly.
     *  Extract equivalences between encoding input and next-state functions.
     */
    void prepareTranRel(void);

    ID buildEquiv(ID a, ID b);

    vector<ID> const & inputs;
    vector<ID> const & stateVars;
    vector<ID> const & nextStateFns;
    ID output;
    Options::Verbosity verbosity;
    bool hasInit;
    ID init;
    vector<ID>::size_type initPos;
    bool hasDelInit;
    ID delInit;
    bool hasValid;
    ID valid;
    ID trel;
    ID first;
    ID last;
    bool worth_looking;
    // Maps state variables to their (encoded) next-state functions.
    unordered_map<ID,ID> latchmap;
    // Maps state variables to decoded next-state functions.
    unordered_map<ID,ID> equivs;
    // State variable equivalences in the next-state relation.
    unordered_set<ID> nreq;
    // Nodes conjoined to the equivalences that are not equivalences.
    vector<ID> exts;
    // Conjuncts of the initial state in full forward relational encoding.
    unordered_set<ID> initRel;
    // Variable equivalences in the initial-state relation.
    unordered_set<ID> ireq;
    // From encoding input to corresponding latch.
    unordered_map<ID,ID> ilmap;
    // From latch to corresponding encoding input.
    unordered_map<ID,ID> limap;
    // Literals in initial cube (if there is such a cube).
    vector<ID> initLits;
    // Conjuncts of the transition relation grouped so that each gruop
    // has support disjoint from all the others.
    unordered_map<ID,vector<ID> > rblocks;
    // Conjuncts of the initial relation grouped so that each gruop
    // has support disjoint from all the others.
    unordered_map<ID,vector<ID> > iblocks;
    // Substitution map for the initial-state relation.
    unordered_map<ID,ID> isubmap;
    // Unit literals in the initial-state relation.
    unordered_set<ID> iunit;
    // Substitution map for the transition relation.
    unordered_map<ID,ID> tsubmap;
    // Unit literals in the transition relation.
    unordered_set<ID> tunit;
  };


  void PatternMatch::extract(void)
  {
    for (vector<ID>::size_type i = 0; i < stateVars.size(); ++i) {
      latchmap[stateVars[i]] = nextStateFns[i];
    }
    findEncondingPairs();
    findInitialized();
    findDelayedInitialized();
    findValid();
    worth_looking = isInteresting();
  }


  bool PatternMatch::isInteresting(void)
  {
    // Look for initialized latch.
    if (!hasInit) {
      if (verbosity > Options::Terse)
        cout << "No initialized latch" << endl;
      return false;
    }
    if (verbosity > Options::Terse) {
      cout << "Initialized is " << stringOf(view(), init)
           << " in position " << initPos << endl;
    }
    if (hasDelInit) {
      if (verbosity > Options::Terse)
        cout << "Delayed initialized latch is "
             << stringOf(view(), delInit) << endl;
    }
    if (!hasValid) {
      if (verbosity > Options::Terse)
        cout << "Could not find valid latch" << endl;
      return false;
    }
    if (verbosity > Options::Terse) {
      cout << "Valid is " << stringOf(view(), valid) << endl;
    }
    if (verbosity > Options::Verbose)
      cout << "trel = " << stringOf(view(), trel) << endl;
    set<ID> first_variables;
    variables(view(), first, first_variables);
    //if (!areMappedInputs(first_variables)) {
    if (!arePrimaryInputs(first_variables)) {
      if (verbosity > Options::Terse)
        cout << "Unmapped variables in first" << endl;
      if (verbosity > Options::Verbose)
        cout << "first =" << stringOf(view(), first) << endl;
      return false;
    }
    set<ID> last_variables;
    variables(view(), last, last_variables);
    if (!areMappedLatches(last_variables)) {
      if (verbosity > Options::Terse)
        cout << "Unmapped variables in last" << endl;
      if (verbosity > Options::Verbose)
        cout << "last =" << stringOf(view(), last) << endl;
      return false;
    }
    return true;
  }


  bool PatternMatch::isEncoded(bool forward)
  {
    reset();
    if (!worth_looking)
      return false;
    gather(trel, forward);
    if (verbosity > Options::Terse)
      cout << "Found equivalences for " << equivs.size() << " out of "
           << limap.size() << " mapped latches" << endl;
    if (verbosity > Options::Informative) {
      for (unordered_map<ID,ID>::const_iterator it = equivs.begin();
           it != equivs.end(); ++it) {
        if (verbosity > Options::Informative)
          cout << "**** " << stringOf(view(), it->first) << " ****" << endl;
        if (verbosity > Options::Verbose)
          cout << stringOf(view(), it->second) << endl;
      }
    }
    if (exts.size() > 0) {
      if (verbosity > Options::Terse)
        cout << "Found " << exts.size() << " extras in trel" << endl;
      if (verbosity > Options::Verbose) {
        for (vector<ID>::const_iterator it = exts.begin();
             it != exts.end(); ++it) {
          cout << stringOf(view(), *it) << endl;
        }
      }
    }
    if (!checkSupports(forward))
      return false;
    if (!foundAllEquivalences()) {
      if (verbosity > Options::Terse)
        cout << "Not enough equivalences" << endl;
      return false;
    }
    return true;
  }


  bool PatternMatch::isRelEncoded(void)
  {
    reset();
    if (!worth_looking)
      return false;
    if (!hasDelInit) {
      if (verbosity > Options::Terse)
        cout << "No delayed init" << endl;
      return false;
    }
    if (!checkRelSupport())
      return false;
    // At this point decoding can be attempted.  Examine transition
    // relation and then initial state relation.  This order allows us
    // to rely on equivalences between latches that hold invariably
    // (coming from the transition relation) to be used for the determination
    // of the initial state.
    prepareTranRel();
    if (verbosity > Options::Terse)
      cout << "Found equivalences for " << equivs.size() << " out of "
           << limap.size() << " mapped latches" << endl;
    if (verbosity > Options::Informative) {
      for (unordered_map<ID,ID>::const_iterator it = equivs.begin();
           it != equivs.end(); ++it) {
        if (verbosity > Options::Informative)
          cout << "**** " << stringOf(view(), it->first) << " ****" << endl;
        if (verbosity > Options::Verbose)
          cout << stringOf(view(), it->second) << endl;
      }
    }
    if (exts.size() > 0) {
      if (verbosity > Options::Terse)
        cout << "Found " << exts.size() << " extras in trel" << endl;
      if (verbosity > Options::Verbose) {
        for (vector<ID>::const_iterator it = exts.begin();
             it != exts.end(); ++it) {
          cout << "exts: " << stringOf(view(), *it) << endl;
        }
      }
    }
    groupTrelConjuncts();

    prepareInitRel();
    if (initRel.size() > 0) {
      if (verbosity > Options::Terse)
        cout << "Found " << initRel.size() << " conjuncts in first" << endl;
      if (verbosity > Options::Verbose) {
        for (unordered_set<ID>::const_iterator it = initRel.begin();
             it != initRel.end(); ++it) {
          cout << "initRel: " << stringOf(view(), *it) << endl;
        }
      }
    }
    groupInitConjuncts();

    return true;
  }


  bool PatternMatch::checkRelSupport(void)
  {
    bool ok = true; // Inefficient, but informative.

    // The initial state relation should depend on primary inputs.
    unordered_set<ID> inputSet(inputs.begin(), inputs.end());
    set<ID> initial_variables;
    variables(view(), first, initial_variables);
    if (!inSet(inputSet, initial_variables)) {
      if (verbosity > Options::Terse)
        cout << "Non-input variable in initial state relation" << endl;
      ok = false;
    }

    // The transition relation should depend on primary inputs and
    // latches (except valid).
    unordered_set<ID> supportSet(inputSet);
    supportSet.insert(stateVars.begin(), stateVars.end());
    supportSet.erase(valid);
    set<ID> trel_variables;
    variables(view(), trel, trel_variables);
    if (!inSet(supportSet, trel_variables)) {
      if (verbosity > Options::Terse)
        cout << "Valid latch in transition relation" << endl;
      ok = false;
    }

    // The bad states should depend only on mapped latches or delayed init.
    unordered_set<ID> latchSet;
    for (unordered_map<ID,ID>::const_iterator it = limap.begin();
         it != limap.end(); ++it) {
      latchSet.insert(it->first);
    }
    latchSet.insert(delInit);
    set<ID> last_variables;
    variables(view(), last, last_variables);
    if (!inSet(latchSet, last_variables)) {
      if (verbosity > Options::Terse)
        cout << "Non-mapped latch or input in bad states" << endl;
      ok = false;
    }

    // All inputs should be mapped.
    // (This is too restrictive and only produces a warning.)
    if (ilmap.size() != inputs.size()) {
      assert(ilmap.size() < inputs.size());
      if (verbosity > Options::Terse) {
        cout << "Warning: unmapped inputs" << endl;
        for (vector<ID>::const_iterator it = inputs.begin();
             it != inputs.end(); ++it) {
          if (ilmap.find(*it) == ilmap.end())
            cout << "Unmapped: " << stringOf(view(), *it) << endl;
        }
      }
    }

    return ok;
  }


  void PatternMatch::findEncondingPairs(void)
  {
    // Allow efficient membership test for inputs.
    unordered_set<ID> inputset(inputs.begin(), inputs.end());
    // Find next-state functions that are primary inputs.
    for (vector<ID>::size_type i = 0; i < stateVars.size(); ++i) {
      ID f = nextStateFns[i];
      unordered_set<ID>::const_iterator iit = inputset.find(f);
      if (iit != inputset.end()) {
        // Build bi-directional map.
        ilmap.insert(unordered_map<ID,ID>::value_type(*iit, stateVars[i]));
        limap.insert(unordered_map<ID,ID>::value_type(stateVars[i], *iit));
        if (verbosity > Options::Informative) {
          cout << "Paired " << stringOf(view(), *iit) << " to "
               << stringOf(view(), stateVars[i]) << endl;
        }
      }
    }
  }

  bool PatternMatch::isEquivStruct(
    ID,
    ID const * args,
    ID const ** args0,
    ID const ** args1)
  {
    // Equivalence: and(or(a,!b),or(!a,b)) = and(!and(!a,b),!and(a,!b))
    // or         : or(and(a,b),and(!a,!b)) = !and(!and(a,b),!and(!a,!b))
    // Detect both forms: the first as XNOR and the second as XOR.
    ID id0 = args[0];
    ID id1 = args[1];
    if (view().op(id0) != Not || view().op(id1) != Not)
      return false;
    ID n0  = view().apply(Not, id0);
    ID n1  = view().apply(Not, id1);
    if (view().op(n0) != And || view().op(n1) != And)
      return false;
    int numArgs0;
    ID const * a0 = *args0 = view().arguments(n0, &numArgs0);
    if (numArgs0 != 2)
      return false;
    int numArgs1;
    ID const * a1 = *args1 = view().arguments(n1, &numArgs1);
    if (numArgs1 != 2)
      return false;
    return ((a0[0] == view().apply(Not, a1[0]) &&
             a0[1] == view().apply(Not, a1[1])) ||
            (a0[0] == view().apply(Not, a1[1]) &&
             a0[1] == view().apply(Not, a1[0])));
  }


  bool PatternMatch::isEquiv(ID id, ID const * args, bool forward)
  {
    ID const * args0, * args1;
    if (isEquivStruct(id, args, &args0, &args1)) {
      // We have found an equivalence.  Check if it involves an encoding
      // input (forward) or an encoded latch (backward).  Also, make sure
      // it's a new equivalence for that variable or the same equivalence
      // we already found; otherwise, we treat this equivalence like just
      // another relational constraint.
      unordered_map<ID,ID>::const_iterator it;
      if (forward) {
        ID func;
        if ((it = ilmap.find(args0[0])) != ilmap.end()) {
          func = view().apply(Not, args0[1]);
        } else if ((it = ilmap.find(args0[1])) != ilmap.end()) {
          func = view().apply(Not, args0[0]);
        } else if ((it = ilmap.find(args1[0])) != ilmap.end()) {
          func = view().apply(Not, args1[1]);
        } else if ((it = ilmap.find(args1[1])) != ilmap.end()) {
          func = view().apply(Not, args1[0]);
        } else {
          return false;
        }
        unordered_map<ID,ID>::const_iterator eit = equivs.find(it->second);
        if (eit == equivs.end()) {
          equivs.insert(unordered_map<ID,ID>::value_type(it->second, func));
        } else if (eit->second != func) {
          ID eqg = buildEquiv(eit->second, func);
          exts.push_back(eqg);
        }
        return true;
      } else {
        if ((it = limap.find(args0[0])) != limap.end()) {
          if (equivs.find(it->first) == equivs.end()) {
            equivs[it->first] = view().apply(Not, args0[1]);
            return true;
          } else {
            return false;
          }
        } else if ((it = limap.find(args0[1])) != limap.end()) {
          if (equivs.find(it->first) == equivs.end()) {
            equivs[it->first] = view().apply(Not, args0[0]);
            return true;
          } else {
            return false;
          }
        } else if ((it = limap.find(args1[0])) != limap.end()) {
          if (equivs.find(it->first) == equivs.end()) {
            equivs[it->first] = view().apply(Not, args1[1]);
            return true;
          } else {
            return false;
          }
        } else if ((it = limap.find(args1[1])) != limap.end()) {
          if (equivs.find(it->first) == equivs.end()) {
            equivs[it->first] = view().apply(Not, args1[0]);
            return true;
          } else {
            return false;
          }
        }
      }
    }
    return false;
  }


  bool PatternMatch::isEquivInit(ID id, ID const * args)
  {
    ID const * args0, * args1;
    if (isEquivStruct(id, args, &args0, &args1)) {
      // We have found an equivalence.  Check if it involves two encoding
      // inputs.
      unordered_map<ID,ID>::const_iterator it;
      if ((it = ilmap.find(args0[0])) != ilmap.end()) {
        ID otherId = view().op(args0[1]) == Not ? view().apply(Not, args0[1]) : args0[1];
        return ilmap.find(otherId) != ilmap.end();
      } else if ((it = ilmap.find(args0[1])) != ilmap.end()) {
        ID otherId = view().op(args0[0]) == Not ? view().apply(Not, args0[0]) : args0[0];
        return ilmap.find(otherId) != ilmap.end();
      } else if ((it = ilmap.find(args1[0])) != ilmap.end()) {
        ID otherId = view().op(args1[1]) == Not ? view().apply(Not, args1[1]) : args1[1];
        return ilmap.find(otherId) != ilmap.end();
      } else if ((it = ilmap.find(args1[1])) != ilmap.end()) {
        ID otherId = view().op(args1[0]) == Not ? view().apply(Not, args1[0]) : args1[0];
        return ilmap.find(otherId) != ilmap.end();
      }
    }
    return false;
  }


  bool PatternMatch::isEquivTran(ID id, ID const * args)
  {
    ID const * args0, * args1;
    if (isEquivStruct(id, args, &args0, &args1)) {
      // We have found an equivalence.  Check if it involves two encoded
      // latches.
      unordered_map<ID,ID>::const_iterator it;
      if ((it = limap.find(args0[0])) != limap.end()) {
        ID otherId = view().op(args0[1]) == Not ? view().apply(Not, args0[1]) : args0[1];
        return latchmap.find(otherId) != latchmap.end();
      } else if ((it = limap.find(args0[1])) != limap.end()) {
        ID otherId = view().op(args0[0]) == Not ? view().apply(Not, args0[0]) : args0[0];
        return latchmap.find(otherId) != latchmap.end();
      } else if ((it = limap.find(args1[0])) != limap.end()) {
        ID otherId = view().op(args1[1]) == Not ? view().apply(Not, args1[1]) : args1[1];
        return latchmap.find(otherId) != latchmap.end();
      } else if ((it = limap.find(args1[1])) != limap.end()) {
        ID otherId = view().op(args1[0]) == Not ? view().apply(Not, args1[0]) : args1[0];
        return latchmap.find(otherId) != latchmap.end();
      }
    }
    return false;
  }


  void PatternMatch::gather(ID id, bool forward)
  {
    if (view().op(id) == And) {
      int n;
      ID const * args = view().arguments(id, &n);
      if (n != 2 || !isEquiv(id, args, forward)) {
        vector<ID> children(args, args+n);
        for (int i = 0; i < n; ++i) {
          gather(children[i], forward);
        }
      }
    } else {
      exts.push_back(id);
    }
  }


  void PatternMatch::gatherInit(ID id)
  {
    Op op = view().op(id);
    if (op == Var) {
      iunit.insert(id);
    } else if (op == Not) {
      ID nid = view().apply(Not, id);
      Op nop = view().op(nid);
      if (nop == Var) {
        iunit.insert(id);
      } else if (nop == And) {
        int n;
        ID const * args = view().arguments(nid, &n);
        if (n == 2 && isEquivInit(nid, args)) {
          ireq.insert(id);
        } else {
          initRel.insert(id);
        }
      } else {
        initRel.insert(id);
      }
    } else if (op == And) {
      int n;
      ID const * args = view().arguments(id, &n);
      if (n == 2 && isEquivInit(id, args)) {
        ireq.insert(id);
      } else {
        vector<ID> children(args, args+n);
        for (int i = 0; i < n; ++i) {
          gatherInit(children[i]);
        }
      }
    } else {
      initRel.insert(id);
    }
  }


  void PatternMatch::gatherTran(ID id)
  {
    Op op = view().op(id);
    if (op == Var) {
      tunit.insert(id);
    } else if (op == Not) {
      ID nid = view().apply(Not, id);
      Op nop = view().op(nid);
      if (nop == Var) {
        tunit.insert(id);
      } else if (nop == And) {
        int n;
        ID const * args = view().arguments(nid, &n);
        if (n == 2 && isEquivTran(nid, args)) {
          nreq.insert(id);
        }
      }
    } else if (op == And) {
      int n;
      ID const * args = view().arguments(id, &n);
      if (n == 2 && isEquivTran(id, args)) {
        nreq.insert(id);
      } else {
        vector<ID> children(args, args+n);
        for (int i = 0; i < n; ++i) {
          gatherTran(children[i]);
        }
      }
    }
  }


  bool PatternMatch::areMappedInputs(set<ID> const & vars)
  {
    for (set<ID>::const_iterator it = vars.begin(); it != vars.end(); ++it) {
      if (ilmap.find(*it) == ilmap.end()) {
        if (verbosity > Options::Terse)
          cout << "Not a mapped input: " << stringOf(view(), *it) << endl;
        return false;
      }
    }
    return true;
  }

  bool PatternMatch::areMappedLatches(set<ID> const & vars)
  {
    for (set<ID>::const_iterator it = vars.begin(); it != vars.end(); ++it) {
      if (*it != delInit)
        if (limap.find(*it) == limap.end()) {
          if (verbosity > Options::Terse)
            cout << "Not a mapped latch: " << stringOf(view(), *it) << endl;
          return false;
        }
    }
    return true;
  }

  bool PatternMatch::arePrimaryInputs(set<ID> const & vars)
  {
    unordered_set<ID> piset(inputs.begin(), inputs.end());
    for (set<ID>::const_iterator it = vars.begin(); it != vars.end(); ++it) {
      if (piset.find(*it) == piset.end()) {
        if (verbosity > Options::Terse)
          cout << "Not a primary input: " << stringOf(view(), *it) << endl;
        return false;
      }
    }
    return true;
  }

  bool PatternMatch::checkSupports(bool forward)
  {
    if (forward) {
      // In case of forward encoding, next-state functions and invariant
      // constraints should depend on mapped latches and unmapped inputs.
      unordered_set<ID> supportSet;
      for (unordered_map<ID,ID>::const_iterator it = limap.begin();
           it != limap.end(); ++it) {
        supportSet.insert(it->first);
      }
      for (vector<ID>::const_iterator it = inputs.begin();
           it != inputs.end(); ++it) {
        unordered_map<ID,ID>::const_iterator fit = ilmap.find(*it);
        if (fit == ilmap.end())
          supportSet.insert(*it);
      }
      for (unordered_map<ID,ID>::const_iterator it = equivs.begin();
           it != equivs.end(); ++it) {
        set<ID> equivalences_variables;
        variables(view(), it->second, equivalences_variables);
        if (!inSet(supportSet, equivalences_variables)) {
          if (verbosity > Options::Terse)
            cout << "Illegal variable in next state function for "
                 << stringOf(view(), it->first) << endl;
          return false;
        }
      }
      for (vector<ID>::const_iterator it = exts.begin();
           it != exts.end(); ++it) {
        set<ID> extra_variables;
        variables(view(), *it, extra_variables);
        if (!inSet(supportSet, extra_variables)) {
          if (verbosity > Options::Terse)
            cout << "Illegal variable in constraint" << endl;
          return false;
        }
      }
      if (!unravelInitialCube(first, ilmap)) {
        if (verbosity > Options::Terse)
          cout << "Initial condition is not a conjunction of state literals"
               << endl;
        return false;
      }
    } else {
      // In case of backward encoding, next-state functions and invariant
      // constraints should depend on (mapped and unmapped) inputs.
      unordered_set<ID> inputSet(inputs.begin(), inputs.end());
      for (unordered_map<ID,ID>::const_iterator it = equivs.begin();
         it != equivs.end(); ++it) {
        set<ID> equivalences_variables;
        variables(view(), it->second, equivalences_variables);
        if (!inSet(inputSet, equivalences_variables)) {
          if (verbosity > Options::Terse)
            cout << "Illegal variable in next state function for "
                 << stringOf(view(), it->first) << endl;
          return false;
        }
      }
      for (vector<ID>::const_iterator it = exts.begin();
           it != exts.end(); ++it) {
        set<ID> extra_variables;
        variables(view(), *it, extra_variables);
        if (!inSet(inputSet, extra_variables)) {
          if (verbosity > Options::Terse)
            cout << "Illegal variable in constraint" << endl;
          return false;
        }
      }
      if (!unravelInitialCube(last, limap)) {
        if (verbosity > Options::Terse)
          cout << "Initial condition is not a conjunction of state literals"
               << endl;
        return false;
      }
    }
    return true;
  }


  bool PatternMatch::inSet(
    unordered_set<ID> const & superset,
    set<ID> const & subset)
  {
    for (set<ID>::const_iterator it = subset.begin(); it != subset.end(); ++it) {
      unordered_set<ID>::const_iterator fit = superset.find(*it);
      if (fit == superset.end()) {
        if (verbosity > Options::Terse)
          cout << "Not present: " << stringOf(view(), *it) << endl;
        return false;
      }
    }
    return true;
  }


  bool PatternMatch::foundAllEquivalences(void) const
  {
    for (unordered_map<ID,ID>::const_iterator it = limap.begin();
         it != limap.end(); ++it) {
      if (equivs.find(it->first) == equivs.end())
        return false;
    }
    return true;
  }

  void PatternMatch::findInitialized(void)
  {
    for (vector<ID>::size_type i = 0; i < nextStateFns.size(); ++i) {
      if (nextStateFns[i] == view().btrue()) {
        initPos = i;
        init = stateVars[i];
        hasInit = true;
        return;
      }
    }
    hasInit = false;
    return;
  }

  void PatternMatch::findDelayedInitialized(void)
  {
    hasDelInit = false;
    if (!hasInit)
      return;
    for (vector<ID>::size_type i = 0; i < nextStateFns.size(); ++i) {
      if (nextStateFns[i] == init) {
        delInit = stateVars[i];
        hasDelInit = true;
        return;
      }
    }
    return;
  }


  /** Find the valid latch and its inputs.  This pattern matcher is quite
   *  inflexible.
   */
  void PatternMatch::findValid(void)
  {
    hasValid = false;
    if (!hasInit)
      return;
    // The output should be the AND of valid and something else (lst).
    if (view().op(output) != And)
      return;
    int numArgs;
    ID const * args = view().arguments(output, &numArgs);
    if (numArgs != 2)
      return;
    // Find which of the two inputs is valid.  We initially assume that valid
    // is the first input; if this fails, we check the other input.
    ID candidate, lst;
    bool second = false;
    if (view().op(args[0]) == Var) {
      candidate = args[0];
      lst = args[1];
    } else if (view().op(args[1]) == Var) {
      candidate = args[1];
      lst = args[0];
      second = true;
    } else {
      return;
    }
    // candidate is a var: is it a latch or an input?
    unordered_map<ID,ID>::const_iterator lit = latchmap.find(candidate);
    if (lit == latchmap.end()) {
      if (second || view().op(args[1]) != Var)
        return;
      // try the other candidate
      candidate = args[1];
      lst = args[0];
      second = true;
      lit = latchmap.find(candidate);
      if (lit == latchmap.end())
        return;
    }
    // Is it really valid or some other latch?  Examine the next-state function.
    ID ncandidate = lit->second;
    // Match multiplexer controlled by initialized.
    if (view().op(ncandidate) != And) {
      if (second || view().op(args[1]) != Var)
        return;
      // try the other candidate
      candidate = args[1];
      lst = args[0];
      second = true;
      lit = latchmap.find(candidate);
      if (lit == latchmap.end())
        return;
      ncandidate = lit->second;
      if (view().op(ncandidate) != And)
        return;
    }
    args = view().arguments(ncandidate, &numArgs);
    if (numArgs != 2)
      return;
    if (view().op(args[0]) != Not || view().op(args[1]) != Not)
      return;
    ID g0 = view().apply(Not, args[0]);
    ID g1 = view().apply(Not, args[1]);
    if (view().op(g0) != And || view().op(g1) != And)
      return;
    int numArgs0;
    ID const * args0 = view().arguments(g0, &numArgs0);
    if (numArgs0 != 2)
      return;
    int numArgs1;
    ID const * args1 = view().arguments(g1, &numArgs1);
    if (numArgs1 != 2)
      return;
    ID h0, h1;
    if (args0[0] == init) {
      h0 = args0[1];
      if (args1[0] == view().apply(Not, init)) {
        h1 = args1[1];
      } else if (args1[1] == view().apply(Not, init)) {
        h1 = args1[0];
      } else {
        return;
      }
    } else if (args0[1] == init) {
      h0 = args0[0];
      if (args1[0] == view().apply(Not, init)) {
        h1 = args1[1];
      } else if (args1[1] == view().apply(Not, init)) {
        h1 = args1[0];
      } else {
        return;
      }
    } else if (args1[0] == init) {
      h0 = args1[1];
      if (args0[0] == view().apply(Not, init)) {
        h1 = args0[1];
      } else if (args0[1] == view().apply(Not, init)) {
        h1 = args0[0];
      } else {
        return;
      }
    } else if (args1[1] == init) {
      h0 = args1[0];
      if (args0[0] == view().apply(Not, init)) {
        h1 = args0[1];
      } else if (args0[1] == view().apply(Not, init)) {
        h1 = args0[0];
      } else {
        return;
      }
    } else {
      return;
    }
    if (view().op(h0) != Not)
      return;
    ID h2 = view().apply(Not, h0);
    if (view().op(h2) != And)
      return;
    int numArgs2;
    ID const * args2 = view().arguments(h2, &numArgs2);
    if (numArgs2 != 2)
      return;
    ID tr;
    if (args2[0] == candidate) {
      tr = args2[1];
    } else if (args2[1] == candidate) {
      tr = args2[0];
    } else {
      return;
    }
    valid = candidate;
    trel = tr;
    first = view().apply(Not, h1);
    last = lst;
    hasValid = true;
    return;
  }


  /** Extract from an AND tree of literals a vector of those literals.
   *  Return true if successful; false otherwise.
   */
  bool PatternMatch::unravelInitialCube(ID cube, unordered_map<ID,ID> const & map)
  {
    Op op = view().op(cube);
    if (op == Var) {
      unordered_map<ID,ID>::const_iterator it = map.find(cube);
      if (it == map.end()) {
        return false;
      } else {
        initLits.push_back(cube);
        return true;
      }
    } else if (op == Not) {
      ID ncube = view().apply(Not, cube);
      if (view().op(ncube) == Var) {
        unordered_map<ID,ID>::const_iterator it = map.find(ncube);
        if (it == map.end()) {
          return false;
        } else {
          initLits.push_back(cube);
          return true;
        }
      } else {
        return false;
      }
    } else if (op == And) {
      int n;
      ID const * args = view().arguments(cube, &n);
      for (int i = 0; i < n; ++i) {
        if (!unravelInitialCube(args[i], map))
          return false;
      }
      return true;
    } else {
      return false;
    }
  }


  void PatternMatch::groupTrelConjuncts(void)
  {
    // Partition transition relation constraints into subsets with disjoint
    // support.  No constraint is an individual variable because unit literals are
    // treated separately.  Hence, the two sets of vertices are disjoint.
    vector<ID> ids(exts.begin(), exts.end());
    set<ID> trel_variables;
    variables(view(), exts, trel_variables);
    ids.insert(ids.end(), trel_variables.begin(), trel_variables.end());
    UF unionfind(ids);
    for (vector<ID>::const_iterator it = exts.begin(); it != exts.end(); ++it) {
      ID ext = *it;
      assert(ext != view().btrue());
      set<ID> evars;
      variables(view(), ext, evars);
      if (verbosity > Options::Verbose) {
        cout << "Support of " << ext << ": ";
        for (set<ID>::const_iterator sit = evars.begin(); sit != evars.end(); ++sit)
          cout << " " << stringOf(view(), *sit);
        cout << endl;
      }
      for (set<ID>::const_iterator eit = evars.begin(); eit != evars.end(); ++eit) {
        unionfind.unite(ext, *eit);
      }
    }

    // Create blocks of "extras" with connected supports.
    for (vector<ID>::const_iterator it = exts.begin(); it != exts.end(); ++it) {
      ID rep = unionfind.find(*it);
      unordered_map<ID, vector<ID> >::iterator mit = rblocks.find(rep);
      if (mit == rblocks.end())
        rblocks.insert(unordered_map<ID, vector<ID> >::value_type(rep,vector<ID>(1,*it)));
      else 
        mit->second.push_back(*it);
    }
    if (verbosity > Options::Informative) {
      // print constraint blocks and their support.
      cout << "Next-state relation blocks (" << rblocks.size() << ")"  << endl;
      for (unordered_map<ID, vector<ID> >::const_iterator bit = rblocks.begin();
           bit != rblocks.end(); ++bit) {
        cout << bit->first << ":";
        vector<ID> v = bit->second;
        for (vector<ID>::const_iterator vit = v.begin(); vit != v.end(); ++vit)
          cout << " " << *vit;
        cout << endl;
        set<ID> bvars;
        variables(view(), v, bvars);
        for (set<ID>::const_iterator sit = bvars.begin(); sit != bvars.end(); ++sit)
          cout << " " << stringOf(view(), *sit);
        cout << endl;
      }
    }
  }


  void PatternMatch::groupInitConjuncts(void)
  {
    // Partition initial constraints into subsets with disjoint support.
    // No constraint is an individual variable because unit literals are
    // treated separately.  Hence, the two sets of vertices are disjoint.
    vector<ID> ids(initRel.begin(), initRel.end());
    set<ID> init_variables;
    variables(view(), first, init_variables);
    ids.insert(ids.end(), init_variables.begin(), init_variables.end());
    UF unionfind(ids);
    for (unordered_set<ID>::const_iterator it = initRel.begin(); it != initRel.end(); ++it) {
      ID conj = *it;
      set<ID> cvars;
      variables(view(), conj, cvars);
      if (verbosity > Options::Verbose) {
        cout << "Support of " << conj << ": ";
        for (set<ID>::const_iterator sit = cvars.begin(); sit != cvars.end(); ++sit)
          cout << " " << stringOf(view(), *sit);
        cout << endl;
      }
      for (set<ID>::const_iterator cit = cvars.begin(); cit != cvars.end(); ++cit) {
        unionfind.unite(conj, *cit);
      }
    }
    // Create blocks of "initRels" with connected supports.
    for (unordered_set<ID>::const_iterator it = initRel.begin(); it != initRel.end(); ++it) {
      ID rep = unionfind.find(*it);
      unordered_map<ID, vector<ID> >::iterator mit = iblocks.find(rep);
      if (mit == iblocks.end())
        iblocks.insert(unordered_map<ID, vector<ID> >::value_type(rep,vector<ID>(1,*it)));
      else 
        mit->second.push_back(*it);
    }
    if (verbosity > Options::Informative) {
      // print initial blocks and their support.
      cout << "Initial state relation blocks (" << iblocks.size() << ")" << endl;
      for (unordered_map<ID, vector<ID> >::const_iterator bit = iblocks.begin();
           bit != iblocks.end(); ++bit) {
        cout << bit->first << ":";
        vector<ID> v = bit->second;
        for (vector<ID>::const_iterator vit = v.begin(); vit != v.end(); ++vit)
          cout << " " << *vit;
        cout << endl;
        set<ID> bvars;
        variables(view(), v, bvars);
        for (set<ID>::const_iterator sit = bvars.begin(); sit != bvars.end(); ++sit)
          cout << " " << stringOf(view(), *sit);
        cout << endl;
      }
    }
  }


  /** Returns true if the two variables are equivalent; otherwise
   *  it returns false to signal that they are complementary.  The
   *  two variables are extracted from the expression of their
   *  equivalence (or complementarity) and returned as side effects.
   *  At least one of the variables (either inputs or latches) has to
   *  be matched.  If only one is matched, it is returned in v1.
   */
  bool PatternMatch::unpackEquiv(ID eq, ID & v1, ID & v2)
  {
    set<ID> evars;
    variables(view(), eq, evars);
    assert(evars.size() == 2);
    set<ID>::const_iterator eit = evars.begin();
    v1 = *eit;
    assert(view().op(v1) == Var);
    unordered_map<ID,ID> submap;
    submap.insert(unordered_map<ID,ID>::value_type(v1, view().btrue()));
    ID b = varSub(view(), submap, eq);
    Op opb = view().op(b);
    bool bvar = opb == Var;
    assert(bvar || opb == Not);
    v2 = bvar ? b : view().apply(Not, b);
    assert(v2 == *(++eit));
    if (limap.find(v1) == limap.end() && ilmap.find(v1) == ilmap.end()) {
      assert(limap.find(v2) != limap.end());
      ID tmp = v1;
      v1 = v2;
      v2 = tmp;
    }
    return bvar;
  }


  void PatternMatch::prepareInitRel(void)
  {
    UFN ufn(view(), inputs);

    if (verbosity > Options::Informative) {
      cout << "current limap: " << limap.size() << " entries" << endl;
      if (verbosity > Options::Verbose) {
        for (unordered_map<ID,ID>::const_iterator cit = limap.begin();
             cit != limap.end(); ++cit) {
          cout << stringOf(view(), cit->first) << " -> "
               << stringOf(view(), cit->second) << endl;
        }
      }
    }
    // Import equivalences from transition relation.
    for (unordered_map<ID,ID>::const_iterator cit = tsubmap.begin();
         cit != tsubmap.end(); ++cit) {
      unordered_map<ID,ID>::const_iterator fit = limap.find(cit->first);
      assert(fit != limap.end());
      ID rep = cit->second;
      bool equivalent = view().op(rep) != Not;
      if (!equivalent)
        rep = view().apply(Not, rep);
      if (rep != view().btrue()) {
        unordered_map<ID,ID>::const_iterator sit = limap.find(rep);
        if (sit == limap.end())
          continue;
        rep = sit->second;
      }
      if (verbosity > Options::Informative)
        cout << "Importing " << (equivalent ? "equivalence" : "complementarity")
             << " of " << stringOf(view(), fit->second)
             << " to " << stringOf(view(), rep) << endl;
      if (equivalent) {
        ufn.makeEquivalent(fit->second, rep);
      } else {
        ufn.makeComplementary(fit->second, rep);
      }
    }

    // Look for unit literals and equivalences.  Substitute into first.
    // Iterate to a fixpoint.
    while (true) {
      iunit.clear();
      ireq.clear();
      initRel.clear();
      // Find unit literals and equivalences in the initial-state relation.
      gatherInit(first);
      if (iunit.size() + ireq.size() == 0)
        break;

      // Update user on progress.
      if (iunit.size() > 0) {
        if (verbosity > Options::Terse)
          cout << "Found " << iunit.size() << " unit literals in first" << endl;
        if (verbosity > Options::Verbose) {
          for (unordered_set<ID>::const_iterator it = iunit.begin();
               it != iunit.end(); ++it) {
            cout << stringOf(view(), *it) << endl;
          }
        }
      }
      if (ireq.size() > 0) {
        if (verbosity > Options::Terse)
          cout << "Found " << ireq.size() << " equivalences in first" << endl;
        if (verbosity > Options::Verbose) {
          for (unordered_set<ID>::const_iterator it = ireq.begin();
               it != ireq.end(); ++it) {
            cout << stringOf(view(), *it) << endl;
          }
        }
      }

      // Make unit literals equivalent to the constant with the proper phase.
      for (unordered_set<ID>::const_iterator iit = iunit.begin();
           iit != iunit.end(); ++iit) {
        ID uLit = *iit;
        bool equivalent = view().op(uLit) == Var;
        assert(equivalent || view().op(uLit) == Not);
        ID var = equivalent ? uLit : view().apply(Not, uLit);
        if (verbosity > Options::Informative)
          cout << "Making " << stringOf(view(), var)
               << (equivalent ? " equivalent to " : " complementary to ")
               << stringOf(view(), view().btrue()) << endl;
        if (equivalent)
          ufn.makeEquivalent(var, view().btrue());
        else
          ufn.makeComplementary(var, view().btrue());
      }
      // Process equivalences between inputs.
      for (unordered_set<ID>::const_iterator iit = ireq.begin();
           iit != ireq.end(); ++iit) {
        ID v1, v2;
        bool equivalent = unpackEquiv(*iit, v1, v2);
        if (verbosity > Options::Informative)
          cout << "Making " << stringOf(view(), v1)
               << (equivalent ? " equivalent to " : " complementary to ")
               << stringOf(view(), v2) << endl;
        if (equivalent)
          ufn.makeEquivalent(v1, v2);
        else
          ufn.makeComplementary(v1, v2);
      }
      // Substitute inputs with their representatives.
      isubmap.clear();
      for (vector<ID>::const_iterator iit = inputs.begin();
           iit != inputs.end(); ++iit) {
        ID var = *iit;
        ID rep = ufn.find(var);
        if (var != rep)
          isubmap.insert(unordered_map<ID,ID>::value_type(var, rep));
      }
#if 0
      // More powerful simplification.  Does not seem to help.
      implSet implications;
      vector<ID> vfirst(1, first);
      Simplifier simp(view(), implications, isubmap, verbosity);
      simp.simplify(vfirst);
      first = vfirst[0];
#endif
      first = varSub(view(), isubmap, first);
    }
    // Summary stats.
    if (verbosity > Options::Terse) {
      cout << "Found " << ufn.count() << " input equivalence classes" << endl;
      if (verbosity > Options::Informative) {
        for (unordered_map<ID,ID>::const_iterator it = isubmap.begin();
             it != isubmap.end(); ++it) {
          ID var = it->first;
          ID rep = it->second;
          cout << "Isubmap: " << stringOf(view(), var) << " -> "
               << stringOf(view(), rep) << endl;
        }
        if (verbosity > Options::Verbose) {
          cout << "Residual initial relation: "
               << stringOf(view(), first) << endl;
        }
      }
    }
  }


  void PatternMatch::prepareTranRel(void)
  {
    // We can assume that init is true because otherwise trel does
    // not affect the output.
    {
      unordered_map<ID,ID> smap;
      smap.insert(unordered_map<ID,ID>::value_type(init, view().btrue()));
      trel = varSub(view(), smap, trel);
    }

    // Gather initial information on next state functions.
    gather(trel, true /* forward */);
    if (verbosity > Options::Terse)
      cout << "Found " << equivs.size() << " next-state functions in trel" << endl;
    if (verbosity > Options::Informative) {
      for (unordered_map<ID,ID>::const_iterator eit = equivs.begin();
           eit != equivs.end(); ++eit) {
        cout << "Next-state function for " << stringOf(view(), eit->first) << endl;
        if (verbosity > Options::Verbose)
          cout << stringOf(view(), eit->second) << endl;
      }
    }
    // Create vectors from equivs so that we can do vectorized variable substitutions.
    vector<ID> svars;
    vector<ID> nsfuncs;
    for (unordered_map<ID,ID>::const_iterator eit = equivs.begin();
         eit != equivs.end(); ++eit) {
      svars.push_back(eit->first);
      nsfuncs.push_back(eit->second);
    }

    UFN ufn(view(), stateVars);
    // Iterate to a fixpoint.
    while (true) {
      tunit.clear();
      nreq.clear();
      // Find unit literals and equivalences among latches
      // in the next-state relation.
      gatherTran(trel);
      if (tunit.size() + nreq.size() == 0)
        break;

      // Update user on progress.
      if (tunit.size() > 0) {
        if (verbosity > Options::Terse)
          cout << "Found " << tunit.size() << " unit literals in trel" << endl;
        if (verbosity > Options::Verbose) {
          for (unordered_set<ID>::const_iterator it = tunit.begin();
               it != tunit.end(); ++it) {
            cout << stringOf(view(), *it) << endl;
          }
        }
      }
      if (nreq.size() > 0) {
        if (verbosity > Options::Terse)
          cout << "Found " << nreq.size() << " equivalences in trel" << endl;
        if (verbosity > Options::Verbose) {
          for (unordered_set<ID>::const_iterator it = nreq.begin();
               it != nreq.end(); ++it) {
            cout << stringOf(view(), *it) << endl;
          }
        }
      }

      // Make unit literals equivalent to the constant with the proper phase.
      for (unordered_set<ID>::const_iterator iit = tunit.begin();
           iit != tunit.end(); ++iit) {
        ID uLit = *iit;
        bool equivalent = view().op(uLit) == Var;
        assert(equivalent || view().op(uLit) == Not);
        ID var = equivalent ? uLit : view().apply(Not, uLit);
        if (verbosity > Options::Informative)
          cout << "Making " << stringOf(view(), var)
               << (equivalent ? " equivalent to " : " complementary to ")
               << stringOf(view(), view().btrue()) << endl;
        if (equivalent)
          ufn.makeEquivalent(var, view().btrue());
        else
          ufn.makeComplementary(var, view().btrue());
      }
      // Process equivalences between latches.
      for (unordered_set<ID>::const_iterator iit = nreq.begin();
           iit != nreq.end(); ++iit) {
        ID v1, v2;
        bool equivalent = unpackEquiv(*iit, v1, v2);
        if (verbosity > Options::Informative)
          cout << "Making " << stringOf(view(), v1)
               << (equivalent ? " equivalent to " : " complementary to ")
               << stringOf(view(), v2) << endl;
        if (equivalent)
          ufn.makeEquivalent(v1, v2);
        else
          ufn.makeComplementary(v1, v2);
      }
      // Substitute latches and matched inputs with their representatives
      // in trel.
      unordered_map<ID,ID> submap;
      // Make sure the constant is still its own representative.
      assert(ufn.find(view().btrue()) == view().btrue());
      for (vector<ID>::const_iterator iit = stateVars.begin();
           iit != stateVars.end(); ++iit) {
        ID var = *iit;
        ID rep = ufn.find(var);
        if (var != rep) {
          // Identify latches.
          submap.insert(unordered_map<ID,ID>::value_type(var, rep));
          // Identify corresponding inputs.
          unordered_map<ID,ID>::const_iterator mit = limap.find(var);
          assert(mit != limap.end());
          ID varInp = mit->second;
          if (view().op(rep) == Not) {
            ID repNot = view().apply(Not, rep);
            if (repNot == view().btrue()) {
              submap.insert(unordered_map<ID,ID>::value_type(varInp, rep));
            } else {
              unordered_map<ID,ID>::const_iterator rit = limap.find(repNot);
              if (rit != limap.end()) {
                ID repInp = view().apply(Not, rit->second);
                submap.insert(unordered_map<ID,ID>::value_type(varInp, repInp));
              }
            }
          } else {
            if (rep == view().btrue()) {
              submap.insert(unordered_map<ID,ID>::value_type(varInp, rep));
            } else {
              unordered_map<ID,ID>::const_iterator rit = limap.find(rep);
              if (rit != limap.end()) {
                ID repInp = rit->second;
                submap.insert(unordered_map<ID,ID>::value_type(varInp, repInp));
              }
            }
          }
        }
      }
      trel = varSub(view(), submap, trel);
      varSub(view(), submap, nsfuncs);
      varSub(view(), submap, exts);
    }

    // Create latch substitution map for decoding.
    tsubmap.clear();
    assert(ufn.find(view().btrue()) == view().btrue());
    equivs.clear();
    for (vector<ID>::size_type i = 0; i != svars.size(); ++i) {
      equivs.insert(unordered_map<ID,ID>::value_type(svars[i], nsfuncs[i]));
    }
    for (vector<ID>::const_iterator iit = stateVars.begin();
         iit != stateVars.end(); ++iit) {
      ID var = *iit;
      ID rep = ufn.find(var);
      if (var != rep) {
        unordered_map<ID,ID>::const_iterator vit = equivs.find(var);
        if (vit != equivs.end()) {
          ID trueRep = view().op(rep) == Not ? view().apply(Not, rep) : rep;
          unordered_map<ID,ID>::const_iterator rit = equivs.find(trueRep);
          if (rit != equivs.end()) {
            ID func = trueRep == rep ? rit->second : view().apply(Not, rit->second);
            if (vit->second != func) {
              cout << "HERE! " << stringOf(view(), var) << " "
                   << stringOf(view(), rep) << endl;
              exts.push_back(buildEquiv(var,rep));
              continue;
            } else {
              equivs.erase(var);
            }
          }
        }
        tsubmap.insert(unordered_map<ID,ID>::value_type(var, rep));
      }
    }

    exts.erase(remove(exts.begin(), exts.end(), view().btrue()), exts.end());

    // Compute equivalences between encoding input and next-state function.
    // Also, accumulate recalcitrant bits of relation in "exts."
    equivs.clear();
    exts.clear();
    gather(trel, /* forward */ true);

    // Summary stats.
    if (verbosity > Options::Terse) {
      cout << "Found " << ufn.count() << " latch equivalence classes" << endl;
      if (verbosity > Options::Informative) {
        for (unordered_map<ID,ID>::const_iterator it = tsubmap.begin();
             it != tsubmap.end(); ++it) {
          ID var = it->first;
          ID rep = it->second;
          cout << "Tsubmap: " << stringOf(view(), var) << " -> "
               << stringOf(view(), rep) << endl;
        }
        if (verbosity > Options::Verbose) {
          cout << "Residual transition relation: "
               << stringOf(view(), trel) << endl;
        }
      }
    }
  }


  ID PatternMatch::buildEquiv(ID a, ID b)
  {
    ID a0 = view().apply(And, a, view().apply(Not, b));
    ID a1 = view().apply(And, view().apply(Not, a), b);
    return view().apply(And, view().apply(Not, a0), view().apply(Not, a1));
  }

  bool PatternMatch::hasInitAndValid(void)
  {
    return hasInit && hasValid;
  }

} // namespace Expr


void decode(
  Expr::Manager::View & ev,
  ExprAttachment * eat,
  Expr::PatternMatch & pm,
  bool forward,
  Options::Verbosity verbosity)
{
#if 0
  unordered_map<ID,ID> const & lmap = pm.latchMap();
  unordered_map<ID,ID>::const_iterator cit = lmap.find(pm.getValid());
  ID root = cit->second;
  if (verbosity > Options::Verbose)
    cout << "Original valid: " << stringOf(ev, root) << endl;
  root = ev.fold(pm, root);
  if (verbosity > Options::Verbose)
    cout << "Simplified valid: " << stringOf(ev, root) << endl;
#endif

  if (verbosity > Options::Terse)
    cout << (forward ? "Forward" : "Backward")
         << " relational encoding" << endl;

  // Make next state functions the inputs to the corresponding latches
  // and remove initialization from latches. (Make sure they are all
  // initialized to 0.)

  unordered_map<ID,ID> const & ilmap = pm.inputLatchMap();

  ID final;
  if (forward) {
    final = pm.getLast();
  } else {
    // Substitute state variables for corresponding encoding inputs
    // in first.
    final = Expr::varSub(ev, ilmap, pm.getFirst());
    if (verbosity > Options::Verbose) {
      cout << "New first = " << stringOf(ev, final) << endl;
      cout << "Last = " << stringOf(ev, pm.getLast()) << endl;
    }
  }

  // Create new next-state function excluding initialized and valid.
  unordered_map<ID,ID> const & equivalences = pm.equivalences();
  vector<ID> sv(eat->stateVars());
  eat->clearNextStateFns();
  vector<ID> newsv, newnsf;
  for (vector<ID>::size_type i = 0; i < sv.size(); ++i) {
    ID var = sv[i];
    unordered_map<ID,ID>::const_iterator it = equivalences.find(var);
    if (it != equivalences.end()) {
      newsv.push_back(var);
      newnsf.push_back(it->second);
    }
  }
  Expr::varSub(ev, ilmap, newnsf);
  eat->setNextStateFns(newsv, newnsf);

  // Keep only non-encoding inputs.
  vector<ID> inputs(eat->inputs());
  eat->clearInputs();
  for (vector<ID>::size_type i = 0; i < inputs.size(); ++i) {
    ID inp = inputs[i];
    unordered_map<ID,ID>::const_iterator it = ilmap.find(inp);
    if (it == ilmap.end()) {
      eat->addInput(inp);
    }
  }

  // The bad states are in final.
  vector<ID> outputs(eat->outputs());
  eat->clearOutputFns();
  eat->setOutputFn(outputs[0], final);

  // Put the initial states in AIGER format.
  eat->clearInitialConditions();
  vector<ID> initLits(pm.initLiterals());
  if (forward)
    Expr::varSub(ev, ilmap, initLits);
  eat->addInitialConditions(initLits);

  vector<ID> extras(pm.extras().begin(), pm.extras().end());
  ID cand = ev.btrue();
  for (vector<ID>::const_iterator it = extras.begin(); it != extras.end(); ++it) {
    cand = ev.apply(Expr::And, cand, *it);
  }
  cand = Expr::varSub(ev, ilmap, cand);
  //cand = cand | final
  cand = ev.apply(Expr::Not, ev.apply(Expr::And, 
            ev.apply(Expr::Not, cand),
            ev.apply(Expr::Not, final)));
  ID var = ev.newVar("c0");
  eat->addConstraint(var, cand);
}


ID makeMux(
  Expr::Manager::View & ev,
  ID control,
  ID data1,
  ID data0)
{
  // These three special cases could be skipped, but without them,
  // we get redundant expressions.
  if (data0 == data1)
    return data0;
  if (data0 == ev.bfalse())
    return ev.apply(Expr::And, control, data1);
  if (data0 == ev.btrue())
    return ev.apply(Expr::Not, ev.apply(Expr::And, control,
                                        ev.apply(Expr::Not, data1)));
  ID and1 = ev.apply(Expr::And, control, data1);
  ID ncontrol = ev.apply(Expr::Not, control);
  ID and0 = ev.apply(Expr::And, ncontrol, data0);
  ID nand1 = ev.apply(Expr::Not, and1);
  ID nand0 = ev.apply(Expr::Not, and0);
  return ev.apply(Expr::Not, ev.apply(Expr::And, nand1, nand0));
}


void solveInitEqns(
  Expr::Manager::View & ev,
  ExprAttachment *,
  Expr::PatternMatch & pm,
  vector<ID> & initRel,
  unordered_map<ID,ID> & ismap,
  Options::Verbosity verbosity)
{
  unordered_map<ID, vector<ID> > const & iblocks = pm.initBlocks();
  // Collect the roots and build their BDDs in one go.
  vector<ID> roots;
  // Add roots for initial state blocks.  Only small blocks are solved
  // with BDDs.  The others are added as constraints to the decoded model.
  for (unordered_map<ID, vector<ID> >::const_iterator bit = iblocks.begin();
       bit != iblocks.end(); ++bit) {
    vector<ID> block = bit->second;
    if (block.size() < 10) {
      set<ID> bvars;
      variables(ev, block, bvars);
      if (bvars.size() < 20) {
        for (vector<ID>::const_iterator vit = block.begin();
             vit != block.end(); ++vit)
          roots.push_back(*vit);
      } else {
        for (vector<ID>::const_iterator vit = block.begin();
             vit != block.end(); ++vit)
          initRel.push_back(*vit);
      }
    } else {
      for (vector<ID>::const_iterator vit = block.begin();
           vit != block.end(); ++vit)
        initRel.push_back(*vit);
    }
  }
  if (verbosity > Options::Verbose)
    for (vector<ID>::const_iterator it = roots.begin(); it != roots.end(); ++it)
      cout << "Root: " << stringOf(ev, *it) << endl;

  // Make sure we have BDDs for the variables because BDDs for intermediate
  // nodes are not otherwise kept by bddOf.
  set<ID> root_vars;
  variables(ev, roots, root_vars);
  roots.insert(roots.end(), root_vars.begin(), root_vars.end());

  // Build BDDs for the relational terms.
  Cudd bddMgr = Cudd();
  bddMgr.Reserve(root_vars.size());
#if 1
  bddMgr.AutodynEnable(CUDD_REORDER_SIFT);
  if (verbosity > Options::Terse)
    bddMgr.EnableReorderingReporting();
#endif
  // We allow auxiliary variables.  Later we build expressions for them.
  unsigned int auxLimit = 250;
  unordered_map<ID,int> auxVar;
  // We rely on the variable depth-first order produced by the expression
  // folder that builds the BDDs.
  unordered_map<ID,int> orderMap;
  Expr::IdBddMap map = bddOf(ev, roots, bddMgr, orderMap, auxVar,
                             auxLimit, verbosity);
  if (verbosity > Options::Informative) {
    // Print variable order.  Auxiliary variables are printed as "true."
    vector<ID> orderVec(orderMap.size() + auxVar.size(), 0);
    for (unordered_map<ID,int>::const_iterator mit = orderMap.begin();
         mit != orderMap.end(); ++mit) {
      assert((size_t) mit->second < orderVec.size());
      orderVec[mit->second] = mit->first;
    }
    ostringstream os;
    os << "Order: ";
    shortStringOfID(ev, orderVec, os);
    os << endl;
    cout << os.str();
  }
  if (verbosity > Options::Terse) {
    // Print stats.
    vector<BDD> bv;
    for (Expr::IdBddMap::const_iterator i = map.begin(); i != map.end(); ++i)
      bv.push_back(i->second);
    cout << bddMgr.SharingSize(bv) << " BDD nodes" << endl;
    cout << auxVar.size() << " auxiliary variable" 
         << (auxVar.size() != 1 ? "s" : "") << endl;
  }
  vector<BDD> conjAux;
  for (unordered_map<ID, int>::const_iterator it = auxVar.begin();
       it != auxVar.end(); ++it) {
    BDD f = map[it->first];
    BDD v = bddMgr.bddVar(it->second);
    BDD t = v.Xnor(f);
    conjAux.push_back(t);
  }
  // Build map from BDD variable indices to expression IDs for the
  // auxiliary variables.
  unordered_map<int, ID> index2id;
  for (unordered_map<ID, int>::const_iterator it = auxVar.begin();
       it != auxVar.end(); ++it) {
    index2id[it->second] = it->first;
  }

  // Prepare BDD to expression converter.
  unordered_map<int, ID> indexToVarID;
  for (unordered_map<ID, int>::const_iterator it = orderMap.begin();
       it != orderMap.end(); ++it) {
    indexToVarID.insert(unordered_map<int,ID>::value_type(it->second, it->first));
  }
  Expr::BddToExpr bdd2expr(ev, indexToVarID);

  unordered_map<ID,ID> ilmap = pm.inputLatchMap();

  // Solve equations for initial state relation.
  // The unknowns are the inputs matched to a latch.
  if (verbosity > Options::Terse)
    cout << "Solving the initial state relation (" << iblocks.size()
         << " blocks)" << endl;
  for (unordered_map<ID, vector<ID> >::const_iterator bit = iblocks.begin();
       bit != iblocks.end(); ++bit) {
    vector<ID> block = bit->second;
    set<ID> bvars;
    variables(ev, block, bvars);
    vector<ID> unknowns;
    BDD bddUnknowns = bddMgr.bddOne();
    for (set<ID>::const_iterator vit = bvars.begin();
         vit != bvars.end(); ++vit) {
      if (ilmap.find(*vit) != ilmap.end()) {
        if (map.find(*vit) != map.end()) {
          unknowns.push_back(*vit);
          bddUnknowns &= map[*vit];
        }
      }
    }
    BDD F = bddMgr.bddOne();
    for (vector<ID>::const_iterator fit = block.begin();
         fit != block.end(); ++ fit) {
      if (map.find(*fit) != map.end()) {
        F &= map[*fit];
        if (verbosity > Options::Informative) {
          cout << "F"; F.print(orderMap.size(), 1);
        }
      }
    }
    vector<unsigned int> support = F.SupportIndices();
    queue< vector<unsigned int> > q;
    q.push(support);
    while (!q.empty()) {
      vector<unsigned int> supp = q.front();
      q.pop();
      for (vector<unsigned int>::const_iterator j = supp.begin();
           j != supp.end(); ++j) {
        unordered_map<int,ID>::const_iterator cit = index2id.find(*j);
        if (cit != index2id.end()) {
          BDD g = map[cit->second];
          BDD a = bddMgr.bddVar(*j);
          F = F.AndAbstract(a.Xnor(g),a);
          vector<unsigned int> addSupp = g.SupportIndices();
          q.push(addSupp);
        }
      }
    }

    int * yIndex;
    vector<BDD> G;
    if (verbosity > Options::Terse) {
      cout << "F";
      F.print(orderMap.size(), 1);
      cout << "Solving for " << unknowns.size() << " unknowns" << endl;
    }
    BDD consCond = (!F).SolveEqn(bddUnknowns, G, &yIndex, unknowns.size());
    if (!consCond.IsZero()) {
      if (verbosity > Options::Terse) {
        cout << "Adding consistency condition as initial constraint."
             << endl;
        if (verbosity > Options::Verbose)
          (!consCond).print(orderMap.size(), 1);
      }
      ID expression = bdd2expr.convert(!consCond);
      initRel.push_back(expression);
    }
    for (vector<BDD>::size_type i = 0; i != G.size(); ++i) {
      ID ivar = indexToVarID[yIndex[i]];
      BDD const & sol = G[i];
      ID expression = bdd2expr.convert(sol);
      assert(ilmap.find(ivar) != ilmap.end());
      ID latch = ilmap[ivar];
      ismap[latch] = expression;
      if (verbosity > Options::Terse) {
        cout << "G[" << i << "]";
        sol.print(orderMap.size(), 1);
      }
      if (verbosity > Options::Informative) {
        cout << stringOf(ev, latch) << " <- "
             << stringOf(ev, expression) << endl;
      }
    }
    free(yIndex);
  }
}


void solveTrelEqns(
  Expr::Manager::View & ev,
  ExprAttachment *,
  Expr::PatternMatch & pm,
  vector<ID> & trueRel,
  unordered_map<ID,ID> & nsmap,
  Options::Verbosity verbosity)
{
  unordered_map<ID, vector<ID> > const & rblocks = pm.relBlocks();
  // Collect the roots and build their BDDs in one go.
  vector<ID> roots;
  // Add roots for transition relation blocks.  Only small blocks are solved
  // with BDDs.  The others are added as constraints to the decoded model.
  for (unordered_map<ID, vector<ID> >::const_iterator bit = rblocks.begin();
       bit != rblocks.end(); ++bit) {
    vector<ID> block = bit->second;
    if (block.size() < 10) {
      set<ID> bvars;
      variables(ev, block, bvars);
      if (bvars.size() < 20) {
        for (vector<ID>::const_iterator vit = block.begin();
             vit != block.end(); ++vit)
          roots.push_back(*vit);
      } else {
        for (vector<ID>::const_iterator vit = block.begin();
             vit != block.end(); ++vit)
          trueRel.push_back(*vit);
      }
    } else {
      for (vector<ID>::const_iterator vit = block.begin();
           vit != block.end(); ++vit)
        trueRel.push_back(*vit);
    }
  }
  if (verbosity > Options::Verbose)
    for (vector<ID>::const_iterator it = roots.begin(); it != roots.end(); ++it)
      cout << "Root: " << stringOf(ev, *it) << endl;

  // Make sure we have BDDs for the variables because BDDs for intermediate
  // nodes are not otherwise kept by bddOf.
  set<ID> root_vars;
  variables(ev, roots, root_vars);
  roots.insert(roots.end(), root_vars.begin(), root_vars.end());

  // Build BDDs for the relational terms.
  Cudd bddMgr = Cudd();
  bddMgr.Reserve(root_vars.size());
#if 1
  bddMgr.AutodynEnable(CUDD_REORDER_SIFT);
  if (verbosity > Options::Terse)
    bddMgr.EnableReorderingReporting();
#endif
  // We allow auxiliary variables.  Later we build expressions for them.
  unsigned int auxLimit = 250;
  unordered_map<ID,int> auxVar;
  // We rely on the variable depth-first order produced by the expression
  // folder that builds the BDDs.
  unordered_map<ID,int> orderMap;
  Expr::IdBddMap map = bddOf(ev, roots, bddMgr, orderMap, auxVar,
                             auxLimit, verbosity);
  if (verbosity > Options::Informative) {
    // Print variable order.  Auxiliary variables are printed as "true."
    vector<ID> orderVec(orderMap.size() + auxVar.size(), 0);
    for (unordered_map<ID,int>::const_iterator mit = orderMap.begin();
         mit != orderMap.end(); ++mit) {
      assert((size_t) mit->second < orderVec.size());
      orderVec[mit->second] = mit->first;
    }
    ostringstream os;
    os << "Order: ";
    shortStringOfID(ev, orderVec, os);
    os << endl;
    cout << os.str();
  }
  if (verbosity > Options::Terse) {
    // Print stats.
    vector<BDD> bv;
    for (Expr::IdBddMap::const_iterator i = map.begin(); i != map.end(); ++i)
      bv.push_back(i->second);
    cout << bddMgr.SharingSize(bv) << " BDD nodes" << endl;
    cout << auxVar.size() << " auxiliary variable" 
         << (auxVar.size() != 1 ? "s" : "") << endl;
  }
  vector<BDD> conjAux;
  for (unordered_map<ID, int>::const_iterator it = auxVar.begin();
       it != auxVar.end(); ++it) {
    BDD f = map[it->first];
    BDD v = bddMgr.bddVar(it->second);
    BDD t = v.Xnor(f);
    conjAux.push_back(t);
  }
  // Build map from BDD variable indices to expression IDs for the
  // auxiliary variables.
  unordered_map<int, ID> index2id;
  for (unordered_map<ID, int>::const_iterator it = auxVar.begin();
       it != auxVar.end(); ++it) {
    index2id[it->second] = it->first;
  }

  // Prepare BDD to expression converter.
  unordered_map<int, ID> indexToVarID;
  for (unordered_map<ID, int>::const_iterator it = orderMap.begin();
       it != orderMap.end(); ++it) {
    indexToVarID.insert(unordered_map<int,ID>::value_type(it->second, it->first));
  }
  Expr::BddToExpr bdd2expr(ev, indexToVarID);

  unordered_map<ID,ID> ilmap = pm.inputLatchMap();

  // Solve equations for next state relation.
  // The unknowns are the inputs matched to latches that do not have
  // a next-state function assigned to them.
  if (verbosity > Options::Terse)
    cout << "Solving the next state relation (" << rblocks.size()
         << " blocks)" << endl;
  for (unordered_map<ID, vector<ID> >::const_iterator bit = rblocks.begin();
       bit != rblocks.end(); ++bit) {
    vector<ID> block = bit->second;
    set<ID> bvars;
    variables(ev, block, bvars);
    vector<ID> unknowns;
    BDD bddUnknowns = bddMgr.bddOne();
    for (set<ID>::const_iterator vit = bvars.begin();
         vit != bvars.end(); ++vit) {
      unordered_map<ID,ID>::const_iterator iit = ilmap.find(*vit);
      if (iit != ilmap.end()) {
        if (nsmap.find(iit->second) == nsmap.end()) {
          if (map.find(*vit) != map.end()) {
            unknowns.push_back(*vit);
            bddUnknowns &= map[*vit];
          }
        }
      }
    }
    BDD F = bddMgr.bddOne();
    for (vector<ID>::const_iterator fit = block.begin();
         fit != block.end(); ++ fit) {
      if (map.find(*fit) != map.end()) {
        F &= map[*fit];
        if (verbosity > Options::Informative) {
          cout << "F"; F.print(orderMap.size(), 1);
        }
      }
    }

    vector<unsigned int> support = F.SupportIndices();
    queue< vector<unsigned int> > q;
    q.push(support);
    while (!q.empty()) {
      vector<unsigned int> supp = q.front();
      q.pop();
      for (vector<unsigned int>::const_iterator j = supp.begin();
           j != supp.end(); ++j) {
        unordered_map<int,ID>::const_iterator cit = index2id.find(*j);
        if (cit != index2id.end()) {
          BDD g = map[cit->second];
          BDD a = bddMgr.bddVar(*j);
          F = F.AndAbstract(a.Xnor(g),a);
          vector<unsigned int> addSupp = g.SupportIndices();
          q.push(addSupp);
        }
      }
    }

    int * yIndex;
    vector<BDD> G;
    if (verbosity > Options::Terse) {
      cout << "F";
      F.print(orderMap.size(), 1);
      cout << "Solving for " << unknowns.size() << " unknowns" << endl;
    }
    BDD consCond = (!F).SolveEqn(bddUnknowns, G, &yIndex, unknowns.size());
    if (!consCond.IsZero()) {
      if (verbosity > Options::Terse) {
        cout << "Adding consistency condition as transition constraint."
             << endl;
        if (verbosity > Options::Verbose)
          (!consCond).print(orderMap.size(), 1);
      }
      if (unknowns.size() > 0) {
        ID expression = bdd2expr.convert(!consCond);
        trueRel.push_back(expression);
      } else {
        for (vector<ID>::const_iterator fit = block.begin();
             fit != block.end(); ++ fit)
          trueRel.push_back(*fit);
      }
    }
    for (vector<BDD>::size_type i = 0; i != G.size(); ++i) {
      ID ivar = indexToVarID[yIndex[i]];
      BDD const & sol = G[i];
      ID expression = bdd2expr.convert(sol);
      assert(ilmap.find(ivar) != ilmap.end());
      ID latch = ilmap[ivar];
      assert(nsmap.find(latch) == nsmap.end());
      nsmap[latch] = expression;
      if (verbosity > Options::Informative) {
        cout << "From equations to nsmap " << stringOf(ev, latch) << " <- "
             << stringOf(ev, expression) << endl;
        if (verbosity > Options::Verbose) {
          cout << "G[" << i << "]";
          sol.print(orderMap.size(), 1);
        }
      }
    }
    free(yIndex);
  }
}


void decodeRel(
  Expr::Manager::View & ev,
  ExprAttachment * eat,
  Expr::PatternMatch & pm,
  Options::Verbosity verbosity)
{
  // For every latch that is directly fed by a primary input,
  // derive an initial function and a next-state function.
  // Connect them to the latch via a multiplexer controlled by
  // the initialized bit.  Replace the valid bit by btrue().

  vector<ID> trueRel;
  vector<ID> initRel;
  // Map from latch to initial condition.
  unordered_map<ID,ID> ismap;

  solveInitEqns(ev, eat, pm, initRel, ismap, verbosity);
  unordered_map<ID,ID> const & limap = pm.latchInputMap();
  unordered_map<ID,ID> ilmap = pm.inputLatchMap();

  unordered_map<ID,ID> const & isubmap = pm.initSubMap();
  // Fill ismap with matched inputs for mapped latches that are not equivalent
  // to something else and have no entry due to equation solving.
  for (unordered_map<ID,ID>::const_iterator lit = limap.begin();
       lit != limap.end(); ++lit) {
    if (ismap.find(lit->first) == ismap.end() &&
        isubmap.find(lit->second) == isubmap.end()) {
      ismap.insert(unordered_map<ID,ID>::value_type(lit->first, lit->second));
      if (verbosity > Options::Informative) {
        cout << "Adding to ismap (m) " << stringOf(ev, lit->first) << " <- "
             << stringOf(ev, lit->second) << endl;
      }
    }
  }
  // Add entries to ismap for unit literals and equivalent variables.
  for (unordered_map<ID,ID>::const_iterator sit = isubmap.begin();
       sit != isubmap.end(); ++sit) {
    ID var = sit->first;
    ID rep = sit->second;
    assert(var != rep);
    // The input may be missing from the map if optimization is allowed
    // before decoding.
    if (ilmap.find(var) == ilmap.end())
      continue;
    ID latch = ilmap[var];
    if (rep == ev.btrue() || rep == ev.bfalse()) {
      ismap.insert(unordered_map<ID,ID>::value_type(latch, rep));
      if (verbosity > Options::Informative)
          cout << "Adding to ismap " << stringOf(ev, latch) << " <- "
               << stringOf(ev, rep) << endl;
    } else {
      bool complementary = ev.op(rep) == Expr::Not;
      if (complementary)
        rep = ev.apply(Expr::Not, rep);
      assert(ilmap.find(rep) != ilmap.end());
      ID rlatch = ilmap[rep];
      unordered_map<ID,ID>::const_iterator mit = ismap.find(rlatch);
      assert(mit != ismap.end());
      ID expression = complementary ?
        ev.apply(Expr::Not, mit->second) : mit->second;
      ismap.insert(unordered_map<ID,ID>::value_type(latch, expression));
      if (verbosity > Options::Informative)
        cout << "Adding to ismap (r) " << stringOf(ev, latch) << " <- "
             << stringOf(ev, expression) << endl;
    }
  }
  if (verbosity > Options::Terse)
    cout << "ismap has " << ismap.size() << " functions for "
         << ilmap.size() << " mapped latches" << endl;

  // Map of next-state functions.
  unordered_map<ID,ID> nsmap(pm.equivalences().begin(),
                             pm.equivalences().end());
  if (verbosity > Options::Verbose) {
    cout << "Equivalences in transition relation ("
         << nsmap.size() << ")" << endl;
    for (unordered_map<ID,ID>::const_iterator mit = nsmap.begin();
         mit != nsmap.end(); ++mit) {
      cout << stringOf(ev, mit->first) << " <- "
           << stringOf(ev, mit->second) << endl;
    }
  }

  solveTrelEqns(ev, eat, pm, trueRel, nsmap, verbosity);

  unordered_map<ID,ID> tsubmap = pm.trelSubMap();
  if (verbosity > Options::Terse)
    cout << "Tsubmap has " << tsubmap.size() << " entries" << endl;

  // Check whether equivalent latches agree on their initial values.
  for (unordered_map<ID,ID>::const_iterator mit = tsubmap.begin();
       mit != tsubmap.end(); ++mit) {
    ID latch = mit->first;
    ID replatch = mit->second;
    bool complement = ev.op(replatch) == Expr::Not;
    if (complement)
      replatch = ev.apply(Expr::Not, replatch);
    unordered_map<ID,ID>::const_iterator lit = ismap.find(latch);
    assert(lit != ismap.end());
    ID latchInit = lit->second;
    unordered_map<ID,ID>::const_iterator iit = ismap.find(replatch);
    if (iit != ismap.end()) {
      ID repInit = iit->second;
      assert(latchInit == complement ? ev.apply(Expr::Not, repInit) : repInit);
    } else if (replatch != ev.btrue() && replatch != ev.bfalse()) {
      if (verbosity > Options::Terse)
        cout << "Latch " << stringOf(ev, replatch)
             << " is uninitialized, but related to an initialized latch: "
             << stringOf(ev, latch) << endl;
    }
  }

  // Add matching input to nsmap for latches that have no explicit
  // next-state function and are not equivalent to something else.
  for (unordered_map<ID,ID>::const_iterator mit = limap.begin();
       mit != limap.end(); ++mit) {
    ID latch = mit->first;
    unordered_map<ID,ID>::const_iterator nit = nsmap.find(latch);
    if (nit != nsmap.end() || tsubmap.find(latch) != tsubmap.end())
      continue;
    // No next-state function for this latch.  Use paired input.
    nsmap.insert(*mit);
    if (verbosity > Options::Informative) {
      cout << "Paired input to nsmap " << stringOf(ev, latch) << " <- "
           << stringOf(ev, mit->second) << endl;
    }
  }

  // Add entries to nsmap for unit literals and equivalent variables.
  for (unordered_map<ID,ID>::const_iterator sit = tsubmap.begin();
       sit != tsubmap.end(); ++sit) {
    ID latch = sit->first;
    ID rep = sit->second;
    if (verbosity > Options::Verbose)
      cout << "Processing " << stringOf(ev, latch) << " "
           << stringOf(ev, rep) << endl;
    assert(latch != rep);
    assert(limap.find(latch) != limap.end());
    assert(nsmap.find(latch) == nsmap.end());
    if (rep == ev.btrue() || rep == ev.bfalse()) {
      nsmap.insert(unordered_map<ID,ID>::value_type(latch, rep));
      if (verbosity > Options::Informative)
          cout << "From submap to nsmap (1) " << stringOf(ev, latch) << " <- "
               << stringOf(ev, rep) << endl;
    } else {
      bool complementary = ev.op(rep) == Expr::Not;
      if (complementary)
        rep = ev.apply(Expr::Not, rep);
      unordered_map<ID,ID>::const_iterator mit = nsmap.find(rep);
      if (mit == nsmap.end()) {
        mit = pm.latchMap().find(rep);
        assert(mit != pm.latchMap().end());
      }
      ID expression = complementary ?
        ev.apply(Expr::Not, mit->second) : mit->second;
      nsmap.insert(unordered_map<ID,ID>::value_type(latch, expression));
      if (verbosity > Options::Informative) {
        cout << "From submap to nsmap (2) " << stringOf(ev, latch);
        if (verbosity > Options::Verbose)
          cout << " <- " << stringOf(ev, expression);
        cout << endl;
      }
    }
  }

  if (verbosity > Options::Terse)
    cout << "nsmap has " << nsmap.size() << " pairs for "
         << ilmap.size() << " mapped latches" << endl;

  // Create multiplexers to feed mapped latches.
  assert(limap.size() == ismap.size() && ismap.size() == nsmap.size());

  // Find which inputs are not free.  This is used in peripheral retiming.
  set<ID> offlim;
  // Find the support of the non-trivial next-state functions.  These
  // are the functions that are not just the encoding input.
  vector<ID> ntnsf;
  for (unordered_map<ID,ID>::const_iterator nit = nsmap.begin();
       nit != nsmap.end(); ++nit) {
    ID var = nit->first;
    ID func = nit->second;
    unordered_map<ID,ID>::const_iterator lit = limap.find(var);
    assert(lit != limap.end());
    if (func != lit->second)
      ntnsf.push_back(func);
  }
  for (vector<ID>::const_iterator nit = trueRel.begin();
       nit != trueRel.end(); ++nit) {
    ntnsf.push_back(*nit);
  }
  variables(ev, ntnsf, offlim);

  for (unordered_map<ID,ID>::const_iterator cit = isubmap.begin();
       cit != isubmap.end(); ++cit) {
    assert(ev.op(cit->first) == Expr::Var);
    ID rep = cit->second;
    if (ev.op(rep) == Expr::Not)
      rep = ev.apply(Expr::Not, rep);
    if (rep != ev.btrue() && rep != ev.bfalse()) {
      if (offlim.find(cit->first) == offlim.end())
        offlim.insert(cit->first);
      if (offlim.find(rep) == offlim.end())
        offlim.insert(rep);
    }
  }
  if (verbosity > Options::Informative)
    for (set<ID>::const_iterator cit = offlim.begin();
         cit != offlim.end(); ++cit)
      cout << "offlim: " << stringOf(ev, *cit) << endl;

  unordered_map<ID,ID> muxMap;
  unsigned int prcand = 0;
  for (unordered_map<ID,ID>::const_iterator mit = limap.begin();
       mit != limap.end(); ++mit) {
    ID latch = mit->first;
    unordered_map<ID,ID>::const_iterator nit = nsmap.find(latch);
    assert(nit != nsmap.end());
    unordered_map<ID,ID>::const_iterator iit = ismap.find(latch);
    assert(iit != ismap.end());
    bool retimed = false;
    if (offlim.find(nit->second) == offlim.end()) {
      if (nit->second == iit->second) {
        tsubmap.insert(unordered_map<ID,ID>::value_type(latch, nit->second));
        retimed = true;
      } else if (nit->second == mit->second) {
        if (iit->second == ev.btrue()) {
          ID repl = ev.apply(Expr::Not, ev.apply(Expr::And, pm.delayedInitialized(),
                                                 ev.apply(Expr::Not, nit->second)));
          tsubmap.insert(unordered_map<ID,ID>::value_type(latch, repl));
          retimed = true;
        } else if (iit->second == ev.bfalse()) {
          ID repl = ev.apply(Expr::And, pm.delayedInitialized(), nit->second);
          tsubmap.insert(unordered_map<ID,ID>::value_type(latch, repl));
          retimed = true;
        }
      }
    }
    if (retimed) {
      ++prcand;
    } else {
      ID mux = makeMux(ev, pm.initialized(), nit->second, iit->second);
      muxMap.insert(unordered_map<ID,ID>::value_type(latch, mux));
    }
  }
  if (verbosity > Options::Terse)
    cout << "Found " << prcand << " candidates to peripheral retiming" << endl;
  if (verbosity > Options::Verbose) {
    for (unordered_map<ID,ID>::const_iterator it = tsubmap.begin();
         it != tsubmap.end(); ++it) {
      ID var = it->first;
      ID rep = it->second;
      cout << "Tsubmap: " << stringOf(ev, var) << " -> "
           << stringOf(ev, rep) << endl;
    }
  }

  // Replace next-state functions of mapped latches and valid.
  vector<ID> sv(eat->stateVars());
  vector<ID> newsv;
  vector<ID> newnsf;
  for (vector<ID>::const_iterator it = sv.begin(); it != sv.end(); ++it) {
    if (*it != pm.getValid() && tsubmap.find(*it) == tsubmap.end()) {
      unordered_map<ID,ID>::const_iterator mit = muxMap.find(*it);
      ID func = mit == muxMap.end() ? eat->nextStateFnOf(*it) : mit->second;
      newnsf.push_back(func);
      newsv.push_back(*it);
    }
  }
  Expr::varSub(ev, tsubmap, newnsf);
  eat->clearNextStateFns();
  eat->setNextStateFns(newsv, newnsf);

  // Initial conditions for surviving latches only.
  vector<ID> newInit;
  vector<ID> const & oldInit(eat->initialConditions());
  for (vector<ID>::const_iterator cit = oldInit.begin();
       cit != oldInit.end(); ++cit) {
    ID latch = *cit;
    if (ev.op(latch) == Expr::Not)
      latch = ev.apply(Expr::Not, latch);
    if (latch != pm.getValid() && tsubmap.find(latch) == tsubmap.end()) {
      newInit.push_back(*cit);
    }
  }
  eat->clearInitialConditions();
  eat->addInitialConditions(newInit);

  // The bad states are in last.
  vector<ID> outputs(eat->outputs());
  eat->clearOutputFns();
  ID last = Expr::varSub(ev, tsubmap, pm.getLast());
  if (verbosity > Options::Verbose)
    cout << "bad: " << stringOf(ev, last) << endl;
  eat->setOutputFn(outputs[0], last);

  // Add primary input constraints.
  // Find support variables of the next-state functions.
  vector<ID> nsfunctions;
  for (unordered_map<ID,ID>::const_iterator nit = nsmap.begin();
       nit != nsmap.end(); ++nit) {
    nsfunctions.push_back(nit->second);
  }
  for (vector<ID>::const_iterator vit = trueRel.begin();
       vit != trueRel.end(); ++vit) {
    nsfunctions.push_back(*vit);
  }
  Expr::varSub(ev, tsubmap, nsfunctions);
  set<ID> nsvars;
  variables(ev, nsfunctions, nsvars);
  // If a mapped input is used in a next-state function, we add the constraint
  // that for valid transitions it must at all times equal the next-state
  // function of the corresponding latch.
  for (unordered_map<ID,ID>::const_iterator iit = ilmap.begin();
       iit != ilmap.end(); ++iit) {
    ID var = iit->first;
    ID latch = iit->second;
    if (nsvars.find(var) != nsvars.end()) {
      unordered_map<ID,ID>::const_iterator nit = nsmap.find(latch);
      assert(nit != nsmap.end());
      ID func = nit->second;
      if (func != var) {
        ID and1 = ev.apply(Expr::And, var, ev.apply(Expr::Not, func));
        ID and2 = ev.apply(Expr::And, ev.apply(Expr::Not, var), func);
        ID constraint = ev.apply(Expr::And, ev.apply(Expr::Not, and1),
                                 ev.apply(Expr::Not, and2));
        trueRel.push_back(constraint);
        if (verbosity > Options::Informative)
          cout << "Adding constraint for " << stringOf(ev, var) << endl;
      }
    }
  }
  Expr::varSub(ev, tsubmap, trueRel);

  int i = 0; // constraint counter
  // Relation constraints have the form: initialized implies function.
  if (verbosity > Options::Terse)
    cout << "Adding " << trueRel.size() << " relation constraints" << endl;
  for (vector<ID>::const_iterator sit = trueRel.begin();
       sit != trueRel.end(); ++sit) {
    stringstream ss;
    ss << "c" << i;
    ++i;
    string nm = ss.str();
    ID var = ev.newVar(nm);
    ID func = Expr::varSub(ev, tsubmap, *sit);
    ID actualConstraint = ev.apply(Expr::Not,
                                   ev.apply(Expr::And, pm.initialized(),
                                            ev.apply(Expr::Not, func)));
    if (verbosity > Options::Verbose)
      cout << "constraint " << ss.str() << " <- "
           << stringOf(ev, actualConstraint) << endl;
    eat->addConstraint(var, actualConstraint);
  }

  // Initial constraints have the form: initialized implies delayed
  // initialized or function.
  if (verbosity > Options::Terse)
    cout << "Adding " << initRel.size() << " initial constraints" << endl;
  for (vector<ID>::const_iterator sit = initRel.begin();
       sit != initRel.end(); ++sit) {
    stringstream ss;
    ss << "c" << i;
    ++i;
    string nm = ss.str();
    ID var = ev.newVar(nm);
    ID uninit = ev.apply(Expr::And, pm.initialized(),
                         ev.apply(Expr::Not, pm.delayedInitialized()));
    ID func = Expr::varSub(ev, tsubmap, *sit);
    ID actualConstraint = ev.apply(Expr::Not,
                                   ev.apply(Expr::And, uninit,
                                            ev.apply(Expr::Not, func)));
    eat->addConstraint(var, actualConstraint);
    if (verbosity > Options::Verbose)
      cout << "constraint " << ss.str() << " <- "
           << stringOf(ev, actualConstraint) << endl;
  }
}


void updateSeqAttachment(
  Expr::PatternMatch const & pm,
  SeqAttachment * seat,
  ExprAttachment const * const eat,
  Options::Verbosity verbosity)
{
  if (verbosity > Options::Verbose)
    cout << "Updating sequential attachment with decoding information" << endl;
  seat->decoded = true;
  seat->latchToInput = pm.latchInputMap();
  seat->decodedInputs = eat->inputs();
  seat->decodedStateVars = eat->stateVars();
  seat->decodedInitialConditions = eat->initialConditions();
  seat->decodedNextStateFns = eat->nextStateFns();
  seat->decodedConstraintFns = eat->constraintFns();
}


bool match(
  Expr::Manager::View & ev,
  ExprAttachment * eat,
  SeqAttachment * seat,
  Options::Verbosity verbosity)
{
  // Check for cases we don't deal with.
  if (eat->constraints().size() > 0) {
    if (verbosity > Options::Terse)
      cout << "Model has transition constraints" << endl;
    return false;
  }
  if (eat->justice().size() > 0) {
    if (verbosity > Options::Terse)
      cout << "Model has justice constraints" << endl;
    return false;
  }
  if (eat->fairness().size() > 0) {
    if (verbosity > Options::Terse)
      cout << "Model has fairness constraints" << endl;
    return false;
  }
  vector<ID> outputFns(eat->outputFns());
  if (outputFns.size() != 1) {
    if (verbosity > Options::Terse)
      cout << "Model does not have exactly one output" << endl;
    return false;
  }
  // Plain old model: we can give it a try.  Collect info.
  vector<ID> inputs(eat->inputs());
  vector<ID> stateVars(eat->stateVars());
  vector<ID> nextStateFns(eat->nextStateFns());
  Expr::PatternMatch pm(ev, inputs, stateVars, nextStateFns,
                        outputFns[0], verbosity);

  // Check for backward encoding.
  if (pm.isEncoded(/* backward */ false)) {
    decode(ev, eat, pm, false, verbosity);
    updateSeqAttachment(pm, seat, eat, verbosity);
    return true;
  }
#ifdef NOTCOMP
  if (verbosity > Options::Terse)
    cout << "Checking forward relational encoding" << endl;
  if (pm.isRelEncoded()) {
    if (verbosity > Options::Terse)
      cout << "Full relational encoding" << endl;
    decodeRel(ev, eat, pm, verbosity);
    return true;
  }
#endif
  return false;
}


bool minimalMatch(
  Expr::Manager::View & ev,
  ExprAttachment const * eat,
  RchAttachment * rat,
  Options::Verbosity verbosity)
{
  vector<ID> inputs(eat->inputs());
  vector<ID> stateVars(eat->stateVars());
  vector<ID> nextStateFns(eat->nextStateFns());
  vector<ID> outputFns(eat->outputFns());
  Expr::PatternMatch pm(ev, inputs, stateVars, nextStateFns,
                        outputFns[0], verbosity);

  // Check for minimal encoding.
  if (pm.hasInitAndValid()) {
    rat->addPersistentSignal(pm.initialized(), true, false);
    rat->addPersistentSignal(ev.apply(Expr::Not, pm.getValid()), false, true);
    if (verbosity > Options::Silent)
      cout << "Model is minimally encoded" << endl;
    return true;
  }
  return false;
}


void DecodeAction::exec(void)
{
  // Setup.  Get attachments and such stuff.
  int64_t startTime = Util::get_user_cpu_time();
  Options::Verbosity verbosity = _model.verbosity();
  if (verbosity > Options::Silent)
    cout << "Decoding of model " << _model.name() << endl;

  Model::Mode mode = _model.defaultMode();
  bool success;

  if (mode == Model::mIC3) {
    auto eat = _model.attachment<ExprAttachment>(Key::EXPR);
    auto seat = _model.attachment<SeqAttachment>(Key::SEQ);

    Expr::Manager::View * ev = _model.newView();

    success = match(*ev, eat.operator->(), seat.operator->(), verbosity);

    delete ev;
    _model.release(eat);
    _model.release(seat);
  } else if (mode == Model::mFAIR) {
    ExprAttachment const * const eat = (ExprAttachment const *) _model.constAttachment(Key::EXPR);
    Expr::Manager::View * ev = _model.newView();
    auto rat = _model.attachment<RchAttachment>(Key::RCH);
    success = minimalMatch(*ev, eat, rat.operator->(), verbosity);
    _model.release(rat);
    delete ev;
    _model.constRelease(eat);
  } else {
    success = false;
    if (verbosity > Options::Terse) {
      cout << "Unsupported type of property" << endl;
    }
  }
  if (verbosity > Options::Terse)
    cout << (success ? "" : "un") << "successful decoding" << endl;
  int64_t endTime = Util::get_user_cpu_time(); 
  if (verbosity > Options::Silent)
    cout << "Decoding completed in "
         << ((endTime - startTime) / 1000000.0) << " s" << endl;
}
