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

#include "NiceDAG.h"
#include<algorithm>
#include<set>
#include<unordered_map>
#include<sstream>
#include "ExprUtil.h"
#include "StringTR.h"
#include "Util.h"
#include <boost/foreach.hpp>
#define foreach BOOST_FOREACH

using namespace std;

namespace {

  struct NiceFolder : public Expr::Manager::View::Folder
  {
    int count;
    NiceFolder(Expr::Manager::View* v) : Expr::Manager::View::Folder(*v), count(0)
    {;}

    virtual ID fold(ID id, int n, const ID * const args)
    {
      // handle negation
      bool negation = false;
      ID posid = id;
      int posn = n;
      const ID * posargs = args;

      if(view().op(id) == Expr::Not) {
        negation = true;
        posid = view().apply(Expr::Not, id);
        posargs = view().arguments(posid, &posn);
      }

      ID result = 0;

      // FIXME: use fold properly.  Don't need to actually evaluate this twice
      if(matchNotITE(posid, posn, posargs, result)) {
        // matched not of an ITE
        //cout << id << "matched ITE" << endl;
        ++count;
      } else {
        // did not match
        return Expr::Manager::View::Folder::fold(id, n, args);
      }

      if(negation)
        result = view().apply(Expr::Not, result);

      return result;
    }


    /**
     * returns true if this node is equivalent to the negation of an ITE.  The
     * top level node should be an AND node.
     * @parameter id is the id to compare against !ITE.
     * @parameter n is the number of arguments to the AND.
     * @parameter args is the arguments to the AND.
     * @parameter result is where the equivalent to !ITE id is placed.
     */

    bool matchNotITE(ID id, int n, const ID * args, ID& result) {
      // make sure gate is an and
      if(view().op(id) != Expr::And)
        return false;

      // there should be 2 arguments to the and
      assert(n == 2);

      // both args should be a not of an and
      if(view().op(args[0]) != Expr::Not)
        return false;
      if(view().op(args[1]) != Expr::Not)
        return false;
      ID l = view().apply(Expr::Not, args[0]);
      if(view().op(l) != Expr::And)
        return false;
      ID r = view().apply(Expr::Not, args[1]);
      if(view().op(r) != Expr::And)
        return false;

      // get left and right arguments
      const ID * const argsl = view().arguments(l, &n);
      assert(n == 2);
      const ID * const argsr = view().arguments(r, &n);
      assert(n == 2);

      //TODO: check to see if I need all of these cases because of Expr
      ID cond, tval, fval;
      // find the negated literal
      if(argsl[0] == view().apply(Expr::Not, argsr[0])) {
        //cout << "Case 1" << endl;
        cond = argsl[0];
        tval = argsl[1];
        fval = argsr[1];
      }
      else if (argsl[0] == view().apply(Expr::Not, argsr[1])) {
        //cout << "Case 2" << endl;
        cond = argsl[0];
        tval = argsl[1];
        fval = argsr[0];
      }
      else if (argsl[1] == view().apply(Expr::Not, argsr[0])) {
        //cout << "Case 3" << endl;
        cond = argsl[1];
        tval = argsl[0];
        fval = argsr[1];
      }
      else if (argsl[1] == view().apply(Expr::Not, argsr[1])) {
        //cout << "Case 4" << endl;
        cond = argsl[1];
        tval = argsl[0];
        fval = argsr[0];
      }
      else
        return false;

      // make ITE
      std::vector<ID> ite_args;
      ite_args.push_back(cond);
      ite_args.push_back(tval);
      ite_args.push_back(fval);

      result = view().apply(Expr::ITE, ite_args);

      // negate the result
      result = view().apply(Expr::Not, result);
      
      return true;
    }
  };

  typedef vector<ID> clause;

  enum clause_set_t { UNION, CLAUSES };


  /**
   * clause_set represents a set of clauses using one of two forms:
   * 1) A vector of a vector of literals
   * 2) A vector of IDs and polarities that should be unioned to form the
   *    clause set.
   * The invariant is maintained that if a clause set is of type union, it is
   * not representable with a single literal.  That is to say that single
   * literal clauses are propagated as clauses
   */
  struct clause_set {
    clause_set_t type;
    vector<clause> clauses;
    vector<pair<bool, ID> > unioned;
  };


  /**
   * The implementation of the nice algorithm.  It is implemented as a class so
   * that I don't have to use global variables and I don't have to pass all
   * parameters around explicitly.
   * 
   * See NiceCNF below for how to use this class.
   */
  struct niceCNFImpl {

    typedef unordered_map<ID, clause_set> clause_map;
    typedef unordered_map<ID, pair<unsigned long, unsigned long> > countdb;

    clause_map clausesp;
    clause_map clausesn;
    countdb counts;

    countdb lc_countp;
    countdb lc_countn;

    vector<clause>& emit_target;

    unsigned k;
    Expr::Manager::View* v;

    unsigned long cl_count;

    /**
     * creates a new niceCNFImpl class, initializing all variables.
     */
    niceCNFImpl(Expr::Manager::View* v, vector<clause>& emit_target, unsigned k) : emit_target(emit_target), k(k), v(v), cl_count(0)
    { }

    /**
     * Emits clauses to the final CNF.  This typically happens immediately
     * before the clauses are replaced with a shorter representation.  This
     * version is meant to be used for the output node as it does not create
     * an equisatisfiability constraint along with it.
     *
     * @parameter id is the id of the node to emit
     * @parameter polarity is the polarity of the node to emit
     * @parameter visited is a set of nodes already emitted so nodes won't be
     *            emitted more than once.
     */
    void emit(ID id, bool polarity, set<pair<bool,ID> >& visited) {
      // handle not properly
      if(v->op(id) == Expr::Not) {
        emit(v->apply(Expr::Not, id), !polarity, visited);
        return;
      }
      // only emit for a node once
      if(visited.find(make_pair(polarity,id)) != visited.end())
        return;
      // add this id to the visited set
      visited.insert(make_pair(polarity,id));

      clause_map& sel_clause_map = polarity ? clausesp : clausesn;
      if(sel_clause_map.find(id) == sel_clause_map.end()) {
        cout << "error id " << id << endl;
      }
      assert(sel_clause_map.find(id) != sel_clause_map.end());

      clause_set& curr_clauses = sel_clause_map[id];

      switch(curr_clauses.type) {
        case UNION: {
            assert(curr_clauses.clauses.size() == 0);
            // recursive case, emit all sub-clauses
            typedef pair<bool, ID> respair;
            foreach(respair& i, curr_clauses.unioned) {
              emit(i.second, i.first, visited);
            }
            break;
          }
        case CLAUSES: {
            assert(curr_clauses.unioned.size() == 0);
            // base case insert clauses to emit
            emit_target.insert(emit_target.end(), curr_clauses.clauses.begin(), curr_clauses.clauses.end());
            break;
          }
        default:
            assert(false);
            break;
      }
    }

    /**
     * union_lit modifies a clause, adding a literal to it.
     * Since the first k elements of a clause are the smallest
     * sorted elements of the clause, a search is performed on
     * those elements to see if k exists.  If it does not, it
     * is added to the end.  This is a valid tactic since this
     * function will only be called once on a clause.
     */
    void union_lit(clause& result, ID x)
    {
      // if x is in first k lits of result, don't do anything
      if(binary_search(result.begin(), result.begin()+k, x))
        return;

      // otherwise add x to the end
      result.push_back(x);
    }

    /**
     * emit emits CNF for a given node in the circuit.  When
     * it does so, it also unions in a literal to each of the
     * clauses that is the unary clause that will replace
     * the emitted clauses.
     */
    void emit(ID id, bool polarity, ID to_union, set<pair<bool, ID> >& visited)
    {
      // handle not properly
      if(v->op(id) == Expr::Not) {
        emit(v->apply(Expr::Not, id), !polarity, to_union, visited);
        return;
      }
      
      // only emit for a node once
      if(visited.find(make_pair(polarity,id)) != visited.end())
        return;
      // add this id to the visited set
      visited.insert(make_pair(polarity,id));

      clause_map& sel_clause_map = polarity ? clausesp : clausesn;
      assert(sel_clause_map.find(id) != sel_clause_map.end());

      clause_set& curr_clauses = sel_clause_map[id];

      switch(curr_clauses.type) {
        case UNION: {
            assert(curr_clauses.clauses.size() == 0);
            // recursive case, emit all sub-clauses
            typedef pair<bool,ID> respair;
            foreach(respair& i, curr_clauses.unioned) {
              emit(i.second, i.first, to_union, visited);
            }
            break;
          }
        case CLAUSES: {
            //cout << "emit clauses " << polarity << " " << id << endl;
            assert(curr_clauses.unioned.size() == 0);
            // base case insert clauses to emit
            foreach(clause& c, curr_clauses.clauses) {
              emit_target.push_back(c);
              union_lit(emit_target[emit_target.size()-1], to_union);
            }
            break;
          }
      }
    }

    /**
     * create a new, hopefully uniquely named variable.
     * nndv is prepended to teh current name in hopes
     * that this will make the name unique
     */
    ID newVar(ID id)
    {
      std::stringstream s;
      s << "nndv" << id;
      return v->newVar(s.str());
    }

    /**
     * introduces a new variable that replaces all of the clauses used
     * to represent this node so far.  Since the clauses would be otherwise
     * lost, it emits the replaced clauses modified so that they are implied
     * by the variable
     */
    void var(bool positive, ID id)
    {
      // don't handle nots
      if(v->op(id) == Expr::Not) {
        id = v->apply(Expr::Not, id);
        positive = !positive;
      }

      // ensure there already exists some clauses where we're introducing a variable
      assert( (positive ? clausesp : clausesn).find(id) != (positive ? clausesp : clausesn).end());

      clause_map& oppositedb = positive ? clausesn : clausesp;
      clause_map::iterator oppositeit = oppositedb.find(id);

      ID x;
      if(oppositeit != oppositedb.end() &&
          oppositeit->second.type == CLAUSES &&
          oppositeit->second.clauses.size() == 1 &&
          oppositeit->second.clauses[0].size() == 1)
        x = v->apply(Expr::Not, oppositeit->second.clauses[0][0]);
      else
        x = newVar(id);

      set<pair<bool,ID> > visited;

      // emit clauses 
      emit(id, positive, v->apply(Expr::Not, x), visited);

      // replace the clause with the introduced variable
      clause_map& sel_map = positive ? clausesp : clausesn;

      sel_map[id].type = CLAUSES;
      sel_map[id].clauses.resize(1);
      sel_map[id].clauses[0].resize(1);
      sel_map[id].clauses[0][0] = x;
      sel_map[id].unioned.clear();
      assert(sel_map[id].type == CLAUSES);
      assert(sel_map[id].unioned.size() == 0);
      assert(sel_map[id].clauses.size() == 1);
      assert(sel_map[id].clauses[0].size() == 1);
    }

    /**
     * Count the number of literals in a raw clause (vector of vectors)
     */
    unsigned long count_lits(const vector<clause>& acc) const
    { 
      unsigned long lits = 0;
      for(vector<clause>::const_iterator i = acc.begin(); i != acc.end(); ++i) {
        lits += i->size();
      }
      return lits;
    }

    /**
     * Count the number of literals and clauses in a clause_set structure
     */
    pair<unsigned long, unsigned long> count_lits_clauses(bool positive, const ID id, set<pair<ID,bool> >& visited) 
    {
      // handle negations properly
      if(v->op(id) == Expr::Not)
        return count_lits_clauses(!positive, v->apply(Expr::Not, id), visited);

      // don't revisit nodes
      if(visited.find(make_pair(id, positive)) != visited.end())
        return make_pair(0UL, 0UL);
      visited.insert(make_pair(id,positive));

      cl_count++;
      // get nodes clause set
      const clause_map& sel_map = positive ? clausesp : clausesn;
      assert(sel_map.find(id) != sel_map.end());
      const clause_set& cs = (sel_map.find(id))->second;
      switch(cs.type) {
        case UNION:
          {
            // if it's a union count for all children
            pair<unsigned long, unsigned long> result = make_pair(0UL, 0UL);

            for(vector<pair<bool, ID> >::const_iterator i = cs.unioned.begin();
                  i != cs.unioned.end(); ++i) {
              pair<unsigned long, unsigned long> tres = count_lits_clauses(i->first, i->second, visited);
              result.first += tres.first;
              result.second += tres.second;
            }
            return result;
          }

        case CLAUSES:
          // if it's just clauses, count them
          return make_pair(count_lits(cs.clauses), static_cast<unsigned long>(cs.clauses.size()));

        default:
          assert(false);
      }

    }

    /**
     * Counts the number of literals and clauses used to represent a node.
     */
    pair<unsigned long, unsigned long> count_lits_clauses(bool positive, const ID id)
    {
      // FIXME: is this a non-linearity.
      countdb& sel = positive ? lc_countp : lc_countn;
      countdb::const_iterator it = sel.find(id);
      if(it == sel.end()) {
        set<pair<ID,bool> > s;
        pair<unsigned long, unsigned long> result = count_lits_clauses(positive, id, s);
        cl_count = 0;
        sel[id] = result;
        return result;
      } else {
        return it->second;
      }
    }


    /**
     * Returns true if a variable should be introduced at a disjunction
     */
    bool dis_var_heur(const vector<clause>& acc, const bool positive, const ID e) 
    {
      pair<unsigned long, unsigned long> rese = count_lits_clauses(positive, e);

      if(rese.second > 4)
        return true;

      unsigned long clausesacc = acc.size();
      unsigned long litsacc = count_lits(acc);

      return (rese.first * clausesacc + rese.second * litsacc) > (rese.first + clausesacc + rese.second + litsacc);
    }

    
    /**
     * Returns true if a variable should be introduced in CNF conversion.
     */
    bool var_heur(unsigned long count, const bool positive, const ID e) 
    {
      clause_map& seldb = positive ? clausesp : clausesn;
      assert(seldb.find(e) != seldb.end());
      clause_set& selclauses = seldb[e];
      // compute if the it is representable by a single clause
      bool single = selclauses.type == CLAUSES &&
        selclauses.clauses.size() == 1 &&
        selclauses.clauses[0].size() == 1;

      return count > 1 && !single;
    }

    ID impl(ID p, ID q)
    {
      // implication in aig form
      // ~(~a & ~b) = a | b
      // ~(a & ~b) = ~a | b
      return v->apply(Expr::Not, v->apply(Expr::And, p, v->apply(Expr::Not, q)));
    }

    void argsPseudo(bool positive, ID id, vector<ID>& res)
    {
      int nargs;
      const ID* args = v->arguments(id, &nargs);
      if(positive) {
        switch(v->op(id)) {
          case Expr::ITE:
            res.push_back(impl(args[0],args[1]));
            res.push_back(impl(v->apply(Expr::Not, args[0]),args[2]));
            break;
          case Expr::Equiv:
            res.push_back(impl(args[0], args[1]));
            res.push_back(impl(args[1], args[0]));
            break;
          default:
            assert(false);
        }
      } else { // negative
        switch(v->op(id)) {
          case Expr::ITE:
            res.push_back(impl(args[0], v->apply(Expr::Not, args[1])));
            res.push_back(impl(v->apply(Expr::Not, args[0]), v->apply(Expr::Not, args[2])));
            break;
          case Expr::Equiv:
            res.push_back(impl(args[0], v->apply(Expr::Not, args[1])));
            res.push_back(impl(v->apply(Expr::Not, args[1]), args[0]));
            break;
          case Expr::True:
            assert(false);
          case Expr::Var:
            assert(false);
          case Expr::Or:
            assert(false);
          case Expr::Not:
            assert(false);
          case Expr::TITE:
            assert(false);
          case Expr::BV:
            assert(false);
          case Expr::And:
            assert(false);
          default:
            assert(false);
        }
      }
    }

    /**
     * merge two clauses and add the resulting clause to result
     */
#if 0
    void kmerge(const clause& a, const clause& b, vector<clause>& result)
    {
      //TODO: k-limited merging
      set<ID> res;
      res.insert(a.begin(), a.end());
      res.insert(b.begin(), b.end());
      clause c(res.begin(), res.end());
      /*cout << "Kmerge1: ";
      foreach(ID id, c) {
        cout << id << " ";
      }
      cout << endl;*/
      result.push_back(c);
    }
#endif
    void kmerge(const clause& a, const clause& b, vector<clause>& result)
    {
      result.resize(result.size()+1);
      clause& tmp = result[result.size()-1];

      unsigned a_dist;
      if(a.size() < k)
        a_dist = a.size();
      else
        a_dist = k;

      unsigned b_dist;
      if(b.size() < k)
        b_dist = b.size();
      else
        b_dist = k;

      clause::const_iterator a_k_end = a.begin();
      advance(a_k_end, a_dist);
      clause::const_iterator b_k_end = b.begin();
      advance(b_k_end, b_dist);

      set_union(a.begin(), a_k_end, b.begin(), b_k_end, inserter(tmp, tmp.end()));

      copy(a_k_end, a.end(), inserter(tmp, tmp.end()));
      copy(b_k_end, b.end(), inserter(tmp, tmp.end()));
    }

    /**
     * merge two sets of clauses into a new set of clauses
     */
    void kmerge(const vector<clause>& a, const vector<clause>& b, vector<clause>& result)
    {
      //cout << "Kmerge 2" << endl;
      foreach(const clause& ac, a) {
        foreach(const clause& bc, b) {
          kmerge(ac, bc, result);
        }
      }
    }

    /**
     * Perform a k-limited merge of each clause of id with each clause
     * contained in c, placing the result in result.
     */
    void kmerge(vector<clause>& c, bool positive, ID id, set<pair<ID,bool> >& visited, vector<clause>& result)
    {
      if(v->op(id) == Expr::Not) {
        positive = !positive;
        id = v->apply(Expr::Not, id);
      }
      // if node is already visited, skip it
      if(visited.find(make_pair(id, positive)) != visited.end())
        return;

      // select the appropriate map
      clause_map& curr_db = positive ? clausesp : clausesn;

      // find the appropriate clause_set
      assert(curr_db.find(id) != curr_db.end());
      clause_set& cs = curr_db.find(id)->second;

      switch(cs.type) {
        case UNION:
          {
            // if it's a union, do the merge on all unioned elements
            typedef pair<bool, ID> refid;
            foreach(refid& si, cs.unioned) {
              kmerge(c, si.first, si.second, visited, result);
            }
            break;
          }
        case CLAUSES:
          {
            // if it's a clause, for each clause ci, in c, merge this clause with ci and
            // place the result in result
            kmerge(c, cs.clauses, result);
          }
      }
    }

    /**
     * Perform a k-limited merge of each clause of id with each clause
     * contained in c, placing the result back in c.
     */
    void kmerge(vector<clause>& c, bool positive, ID id) {
      // track visited nodes
      set<pair<ID, bool> > visited;
      // create a result location
      vector<clause> result;

      // do k-limited merge
      kmerge(c, positive, id, visited, result);

      // swap the result with the actual result
      // this prevents a copy.  Old c is destructed normally as part of result
      swap(result, c);
    }

    /**
     * handle disjunction/not and by doing the distribution until the size
     * crosses a threshold.  Then introduce variables and continue.  Result
     * is placed in the negative e clause database.
     */
    void dis(ID e)
    {

      //cout << "Dis: " << e << endl;
      clausesn[e].type = CLAUSES;
      vector<clause>& c = clausesn[e].clauses;
      c.resize(1);
      assert(c[0].size() == 0);
      int nargs;
      const ID* args = v->arguments(e, &nargs);

      // run cnf conversion on each of the arguments
      for(const ID* arg = args; arg != args+nargs; ++arg) {
        cnf(false, *arg);
      }

      // union clauses, introducing variables as appropriate
      for(const ID* idp = args; idp != args+nargs; ++idp) {
        const ID id = *idp;
        
        // if the disjunction is too big, introduce a variable
        if(dis_var_heur(c, false, id))
          var(false, id);

        // cross-product clauses
        kmerge(c, false, id);
      }

      //cout << "Dis exit: " << e << endl;
      // finished merge.  Result is already stored correctly
    }

    /**
     * conjoin all of the clauses generated by cnf+ of each of the
     * arguments from begin to end.  Place the result in the appropriate
     * clause database based on positive and e.  Preserve the invariant
     * unary clauses are automatically propagated.
     */
    template<typename T>
    void con(bool positive, ID e, T begin, T end)
    {
      if(v->op(e) == Expr::Not) {
        positive = !positive;
        e = v->apply(Expr::Not, e);
      }
      clause_map& curr_map = positive ? clausesp : clausesn;
      clause_set& cs = curr_map[e];
      cs.type = UNION;
      bool first = true;
      bool single_lit = true;
      ID lit = v->btrue();
      // FIXME:
      // Can we actually have reconvergence of single literal?

      // recursively call cnf conversion on each element
      for(T i = begin; i != end; ++i) {
        cnf(true, *i);
        // read result to find if it is a single literal
        bool rpol= true;
        ID selid = *i;
        if(v->op(selid) == Expr::Not) {
          selid = v->apply(Expr::Not, selid);
          rpol= false;
        }
        clause_set& r = rpol ? clausesp[selid] : clausesn[selid];
        //clause_set& r = clausesp[*i]; // FIXME: what if *i is a Not?
        if(single_lit) {
          if(r.type == UNION)
            single_lit = false;
          else if(r.clauses.size() == 1 && r.clauses[0].size() == 1) {
            if(first) {
              lit = r.clauses[0][0];
              first = false;
            } else {
              if(r.clauses[0][0] != lit)
                single_lit = false;
            }
          } else {
            single_lit = false;
          }
        }
        // compute the union just in case
        cs.unioned.push_back(make_pair(true,*i));
      }

      if(single_lit) {
        cs.type = CLAUSES;
        cs.unioned.clear();
        cs.clauses.resize(1);
        cs.clauses[0].resize(1);
        cs.clauses[0][0] = lit;
      } else {

        //TODO: use k-limited merging here
        // FIXME: use a set potentially
        sort(cs.unioned.begin(), cs.unioned.end());
        //unique(cs.unioned.begin(), cs.unioned.end());
        assert(cs.clauses.size() == 0);
      }

    }

    string stringOfClauseSet(ID id, bool positive)
    {
      if(v->op(id) == Expr::Not) {
        id = v->apply(Expr::Not, id);
        positive = !positive;
      }
      clause_map& cm = positive ? clausesp : clausesn;
      assert(cm.find(id) != cm.end());
      clause_set& cs = cm[id];
      stringstream ss;
      if(cs.type == UNION) {
        typedef pair<bool, ID> tmp;
        foreach(tmp& p, cs.unioned) {
          ss << stringOfClauseSet(p.second, p.first) << " ";
        }
      } else {
        foreach(clause& c, cs.clauses) {
          ss << "{";
          foreach(ID id, c) {
            ss << CNF::stringOfID(v, id) << " ";
          }
          ss << "} ";
        }
      }
      return ss.str();
    }

    void cnf(bool positive, ID e)
    {
      // only handle positive variables
      if(v->op(e) == Expr::Not) {
        positive = !positive;
        e = v->apply(Expr::Not, e);
      }

      // if cnf was already computed, skip it
      clause_map& sel_map = positive ? clausesp : clausesn;
      if(sel_map.find(e) != sel_map.end())
        return;

      // if we've reached a primary input or latch
      if(v->op(e) == Expr::Var) {
        clausesp[e].type = CLAUSES;
        clausesp[e].clauses.resize(1);
        clausesp[e].clauses[0].resize(1);
        clausesp[e].clauses[0][0] = e;

        clausesn[e].type = CLAUSES;
        clausesn[e].clauses.resize(1);
        clausesn[e].clauses[0].resize(1);
        clausesn[e].clauses[0][0] = v->apply(Expr::Not, e);
        return;
      }

      if(v->op(e) == Expr::And) {
        if(positive) {
          // always conjoin ands
          int nargs;
          const ID* args = v->arguments(e, &nargs);

          con(positive, e, args, args+nargs);

        } else {
          // handle an or/not and
          dis(e);
        }
      } else {
        // FIXME: add ITE/Equiv assertion
        vector<ID> pseudo_args;
        argsPseudo(positive, e, pseudo_args);

        con(positive, e, pseudo_args.begin(), pseudo_args.end());

      }

      // introduce variables sometimes
      if(var_heur(positive ? counts[e].first : counts[e].second, positive, e))
        var(positive, e);

    }


    // count the shared variables
    void countShares(bool positive, ID id)
    {
      // if node is a not, flip polarity and continue
      if(v->op(id) == Expr::Not) {
        id = v->apply(Expr::Not, id);
        positive = !positive;
      }

      typedef unordered_map<ID, pair<unsigned long, unsigned long> >::iterator miterator;

      miterator it = counts.find(id);

      if(it == counts.end()) { // no count exists
        // add a new element
        pair<miterator, bool> tmp = counts.insert(make_pair(id, make_pair(0U,0U)));
        it = tmp.first;
      }

      unsigned long& node_count = positive ? it->second.first : it->second.second;

      int nargs;
      const ID * args = v->arguments(id, &nargs);


      if(node_count == 0) {
        // do something cool
        switch(v->op(id)) {
          case Expr::And: {
                for(int i = 0; i < nargs; ++i) {
                  countShares(positive, args[i]);
                }
                break;
              }
          case Expr::ITE:
          case Expr::Equiv: {
                assert(v->op(id) != Expr::And);
                vector<ID> args;
                argsPseudo(positive, id, args);
                for(unsigned i = 0; i < args.size(); ++i) {
                  countShares(true, args[i]);
                }
                break;
              }
          case Expr::Or:
            assert(false);
          case Expr::Not:
            assert(false);
          case Expr::TITE:
            assert(false);
          case Expr::BV:
            assert(false);
          case Expr::Implies:
            assert(false);
          case Expr::Eq:
            assert(false);
          case Expr::F:
          case Expr::G:
          case Expr::X:
          case Expr::U:
          case Expr::R:
          case Expr::W:
            assert(false);
          case Expr::True:
          case Expr::Var:
            break;
        }
      }

      ++node_count;
    }

  };
} // namespace


namespace CNF {

  /**
   * performs pattern matching on an AIG formatted expression.  It matches ITE blocks and converts
   * appropriate forms of the ITE blocks into equivalence blocks.
   */
  int niceDAG(Expr::Manager::View * v, vector<ID>& outputs)
  {
    NiceFolder nf(v);

    v->fold(nf, outputs);
    return nf.count;
  }

  /**
   * runs the NiceDAGs CNF algorithm on an AIG formatted expression.
   *
   * @parameter verbosity is the verbosity level of the current model.  This is used for diagnostics output.
   * @parameter v is the view in which the CNF generation algorithm should work.
   * @parameter k is the merge check limit (k-limited merging).  The first k elements of a vector are kept sorted for
   * quick unioning
   * @parameter outputs is a vector of IDs that represent the circuit outputs to be converted to CNF.
   * @parameter cnf is the resulting CNF.  It is guaranteed to be made up of only variables and their negations.  Any variables encountered in the original expression will be preserved in the CNF.
   */
  void niceCNF(Options::Verbosity verbosity, Expr::Manager::View * v, unsigned k, vector<ID>& outputs, vector<vector<ID> >& cnf)
  {
    niceDAG(v, outputs);

    int64_t start_time = ::Util::get_cpu_time(false);
    niceCNFImpl nice(v,cnf,k);
    for(unsigned i = 0; i < outputs.size(); ++i) {
      nice.countShares(true, outputs[i]);
    }
    int64_t count_shares_time = ::Util::get_cpu_time(false);

    if(verbosity >= ::Options::Informative)
      cout << "NICECNF: Share Counting Time: " << static_cast<double>(count_shares_time-start_time)/1000000.0 << endl;

    for(unsigned i = 0; i < outputs.size(); ++i) {
      if(v->op(outputs[i]) == Expr::True) {
        // if a function is true, handle it
      } else if(v->op(v->apply(Expr::Not, outputs[i])) == Expr::True) {
        // if a function is false, handle it
        cnf.resize(1);
        cnf[0].clear();
        break;
      } else {
        set<pair<bool, ID> > visited; // FIXME: should probably reuse this
        nice.cnf(true, outputs[i]);

        //unsigned emit_size = cnf.size();
        nice.emit(outputs[i], true, visited);
      }
    }

    int64_t gen_time = ::Util::get_cpu_time(false);
    if(verbosity >= ::Options::Informative)
      cout << "NICECNF: CNF Generation Time: " << static_cast<double>(gen_time-count_shares_time)/1000000.0 << endl;

  }


} // namespace CNF
