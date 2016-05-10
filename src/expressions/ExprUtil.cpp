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

#include "ExprUtil.h"

#include <map>
#include <stack>
#include <climits>

using namespace std;

namespace Expr {

  void stringOfOp(Op op, ostringstream & buf) {
    switch (op) {
    case Var:
      buf << "VAR";
      break;
    case True:
      buf << "True";
      break;
    case Not:
      buf << "!";
      break;
    case And:
      buf << "&";
      break;
    case Or:
      buf << "|";
      break;
    case Equiv:
      buf << "=";
      break;
    case Implies:
      buf << "->";
      break;
    case ITE:
      buf << "ITE";
      break;
    case TITE:
      buf << "TITE";
      break;
    case BV:
      buf << "BV";
      break;
    case F:
      buf << "F";
      break;
    case G:
      buf << "G";
      break;
    case X:
      buf << "X";
      break;
    case U:
      buf << "U";
      break;
    case R:
      buf << "R";
      break;
    case W:
      buf << "W";
      break;
    case Eq:
      buf << "Eq";
      break;
    }
  }

  void shortStringOfID(Manager::View & v, ID id, ostringstream & buf) {
    int np;
    switch (v.op(id)) {
    case True:
      buf << "true";
      break;
    case Var:
      buf << v.varName(id);
      np = v.nprimes(id);
      if (np != 0)
        buf << "(" << np << ")";
      break;
    case Not: {
      int n;
      const ID * const args = v.arguments(id, &n);
      buf << "!";
      shortStringOfID(v, args[0], buf);
      break;
    }
    default:
      buf << "d" << id;
    }
  }

  void shortStringOfID(Manager::View & v, IDVector const & ids, ostringstream & buf) {
    for (IDVector::const_iterator i = ids.begin(); i != ids.end(); ++i) {
      shortStringOfID(v, *i, buf);
      if (i+1 != ids.end())
        buf << " ";
    }
  }

  string stringOf(Manager::View & v, ID id, int indent) {
    class print_folder : public Manager::View::Folder {
    public:
      print_folder(Manager::View & v, ID bid, int _indent) : Manager::View::Folder(v), buf(), bid(bid) {
        ostringstream ibuf;
        for (int i = 0; i < _indent; ++i)
          ibuf << " ";
        indent = ibuf.str();
      }

      virtual ID fold(ID id, int n, const ID * const args) {
        Op op = view().op(id);
        bool base = op == Var || op == True || op == Not;
        if (!base || id == bid)
          buf << indent;
        if (id != bid && !base) {
          buf << "let ";
          shortStringOfID(view(), id, buf);
          buf << " = ";
        }
        if (!base) {
          stringOfOp(op, buf);
          for (int i = 0; i < n; ++i) {
            buf << " ";
            shortStringOfID(view(), args[i], buf);
          }
        }
        else if (id == bid)
          shortStringOfID(view(), id, buf);
        if (id != bid && !base)
          buf << " in" << endl;
        //      else if (id == bid)
        //  buf << endl;
        return id;
      }
      string out() { 
        return buf.str();
      }
    private:
      ostringstream buf;
      ID bid;
      string indent;
    };
    print_folder pf(v, id, indent);
    v.fold(pf, id);
    return pf.out();
  }

  static void juncts(Manager::View & v, ID id, IDVector & rv, Op jop) {
    if (v.op(id) != jop) {
      rv.push_back(id);
      return;
    }

    int n;
    const ID * const args = v.arguments(id, &n);
    for (int i = 0; i < n; ++i)
      juncts(v, args[i], rv, jop);
  }

  void disjuncts(Manager::View & v, ID id, IDVector & rv) { juncts(v, id, rv, Or); }
  void conjuncts(Manager::View & v, ID id, IDVector & rv) { juncts(v, id, rv, And); }

  class var_folder : public Manager::View::Folder {
  public:
    var_folder(Manager::View & v, set<ID> & vset) : Manager::View::Folder(v), vset(vset) {}

    virtual ID fold(ID id, int n, const ID * const args) {
      if (view().op(id) == Var)
        vset.insert(id);
      return id;
    }

  private:
    set<ID> & vset;
  };

  void variables(Manager::View & v, ID id, set<ID> & rv) {
    var_folder vf(v, rv);
    v.fold(vf, id);
  }

  void variables(Manager::View & v, vector<ID> & ids, set<ID> & rv) {
    var_folder vf(v, rv);
    v.fold(vf, ids);
  }

  class prime_folder : public Manager::View::Folder {
  public:
    prime_folder(Manager::View & v, int n) : Manager::View::Folder(v) { 
      this->nprimes = n;
    }
    virtual ID fold(ID id, int n, const ID * const args) {
      if (view().op(id) == Var) {
        int cnp = view().nprimes(id);
        return view().primeTo(id, cnp+nprimes);
      }
      else
        // super creates new expression if args have changed
        return Manager::View::Folder::fold(id, n, args);
    }
  private:
    int nprimes;
  };

  ID primeFormula(Manager::View & v, ID id, int n) {
    prime_folder pf(v, n);
    return v.fold(pf, id);
  }

  void primeFormulas(Manager::View & v, IDVector & ids, int n) {
    prime_folder pf(v, n);
    v.fold(pf, ids);
  }

  class sub_folder : public Manager::View::Folder {
  public:
    sub_folder(Manager:: View & v, const IDMap & _sub) : Manager::View::Folder(v), sub(_sub) {}

    virtual ID fold(ID id, int n, const ID * const args) {
      if (view().op(id) == Var) {
        IDMap::const_iterator it = sub.find(id);
        if (it != sub.end())
          return it->second;
        else
          return id;
      }
      else
        return Manager::View::Folder::fold(id, n, args);
    }

  private:
    const IDMap & sub;
  };

  ID varSub(Manager::View & v, const IDMap & sub, ID id) {
    sub_folder sf(v, sub);
    return v.fold(sf, id);
  }

  void varSub(Manager::View & v, const IDMap & sub, IDVector & ids) {
    sub_folder sf(v, sub);
    v.fold(sf, ids);
  }

  class  tseitin_folder : public Manager::View::Folder {
  public:
    tseitin_folder(Manager::View & v, vector<IDVector> & _clauses,
        IDMap* _satIdOfId) : Manager::View::Folder(v),
        clauses(_clauses), satIdOfId(_satIdOfId) {}

    virtual ID fold(ID id, int n, const ID * const args) {
      Op op = view().op(id);
      if (op == Var || op == True)
        return id;
      if (op == Not)
        return view().apply(Not, args[0]);
      ID r = rep(id);
      ID nr = view().apply(Not, r);
      IDVector lits;
      switch (op) {
      case And:
        for (int i = 0; i < n; ++i) {
          clauses.push_back(or2(nr, args[i]));
          lits.push_back(view().apply(Not, args[i]));
        }
        lits.push_back(r);
        clauses.push_back(lits);
        break;
      case Or:
        for (int i = 0; i < n; ++i) {
          clauses.push_back(or2(view().apply(Not, args[i]), r));
          lits.push_back(args[i]);
        }
        lits.push_back(nr);
        clauses.push_back(lits);
        break;
      case Equiv: {
        ID a = args[0], b = args[1];
        ID na = view().apply(Not, a), nb = view().apply(Not, b);
        clauses.push_back(or3(nr, a, nb));
        clauses.push_back(or3(nr, na, b));
        clauses.push_back(or3(r, na, nb));
        clauses.push_back(or3(r, a, b));
        break;
      }
      case ITE: {
        ID c = args[0], a = args[1], b = args[2];
        ID nc = view().apply(Not, c), na = view().apply(Not, a), nb = view().apply(Not, b);
        clauses.push_back(or3(nc, na, r));
        clauses.push_back(or3(c, nb, r));
        clauses.push_back(or3(nr, c, b));
        clauses.push_back(or3(nr, nc, a));
        break;
      }
      default:
        assert(false);
      }
      return r;
    }
  private:
    vector<IDVector> & clauses;
    unordered_map<ID, ID>* satIdOfId;

    ID rep(ID id) {
      ostringstream buf;
      buf << "r";
      buf << id;
      ID newId = view().newVar(buf.str());
      if(satIdOfId != NULL) {
        satIdOfId->insert(pair<ID, ID>(id, newId));
      }
      return newId;
    }

    vector<ID> or2(ID l1, ID l2) {
      IDVector lits;
      lits.push_back(l1);
      lits.push_back(l2);
      return lits;
    }

    vector<ID> or3(ID l1, ID l2, ID l3) {
      IDVector lits;
      lits.push_back(l1);
      lits.push_back(l2);
      lits.push_back(l3);
      return lits;
    }
  };

  ID tseitin(Manager::View & v, ID id, vector<IDVector> & rv_clauses,
             IDMap* satIdOfId, bool assert_roots) {
    tseitin_folder tf(v, rv_clauses, satIdOfId);
    ID root = v.fold(tf, id);
    if (assert_roots) {
      IDVector unit;
      unit.push_back(root);
      rv_clauses.push_back(unit);
    }
    return root;
  }

  void tseitin(Manager::View & v, IDVector & ids, vector<IDVector> &
               rv_clauses, IDMap* satIdOfId, bool assert_roots) {
    tseitin_folder tf(v, rv_clauses, satIdOfId);
    v.fold(tf, ids);
    if (assert_roots)
      for (IDVector::iterator it = ids.begin(); it != ids.end(); it++) {
        IDVector unit;
        unit.push_back(*it);
        rv_clauses.push_back(unit);
      }
  }

  bool isLit(Manager::View & v, ID id) {
    if(v.op(id) == Var)
      return true;
    if(v.op(id) == Not) {
      int n;
      const ID * const args = v.arguments(id, &n);
      assert(n == 1);
      if(v.op(args[0]) == Var)
        return true;
    }
    return false;
  }

  void litsAndNonLitsOf(Manager::View & v, IDVector & in, IDVector & lits, IDVector & nonLits) {
    for(IDVector::const_iterator it = in.begin(); it != in.end(); ++it) {
      if(isLit(v, *it))
        lits.push_back(*it);
      else
        nonLits.push_back(*it);
    }
  }

  bool isClause(Manager::View & v, ID id, IDVector * lits) {
    IDVector disjs;
    disjuncts(v, id, disjs);
    for(IDVector::const_iterator it = disjs.begin(); it != disjs.end(); ++it) {
      if(!isLit(v, *it)) {
        return false;
      }
    }
    if(lits)
      *lits = disjs;
    return true;
  }

  ID wilson_rep(Manager::View & v) {
    static unsigned i = 0;
    ostringstream buf;
    buf << "wr";
    buf << i++;
    return v.newVar(buf.str());
  }

  void wilsonRec(Manager::View & v, ID id, vector<IDVector> & rv_clauses,
                 unordered_set<ID> & seen, unordered_map<ID, ID> & reps, unordered_set<ID> & crClauses) {
    if(seen.find(id) != seen.end())
      return;
    seen.insert(id);

    int n;
    const ID * args = v.arguments(id, &n);

    IDVector lits2;
    if(v.op(id) == True) {
      return;
    }

    if(isClause(v, id, &lits2)) {
      rv_clauses.push_back(lits2);
    }
    else if(v.op(id) == And) { // G1 & G2 & ...
      for(int i = 0; i < n; ++i) {
        wilsonRec(v, args[i], rv_clauses, seen, reps, crClauses);
      }
    }
    else if(v.op(id) == Not && v.op(args[0]) == Or) { // !(G1 | G2 | ...)
      //Get the children of the Or
      int numArgs;
      const ID * const orArgs = v.arguments(args[0], &numArgs);
      IDVector conjs;
      for(int i = 0; i < numArgs; ++i) {
        conjs.push_back(v.apply(Not, orArgs[i]));
      }
      wilsonRec(v, v.apply(And, conjs), rv_clauses, seen, reps, crClauses);
    }
    else if(v.op(id) == Not && v.op(args[0]) == And) { // !(G1 & G2 & ...)
      //Get the children of the And
      int numArgs;
      const ID * const andArgs = v.arguments(args[0], &numArgs);
      IDVector disjs;
      for(int i = 0; i < numArgs; ++i) {
        disjs.push_back(v.apply(Not, andArgs[i]));
      }
      wilsonRec(v, v.apply(Or, disjs), rv_clauses, seen, reps, crClauses);
    }
    else {
      //cout << v.op(id) << endl;
      assert(v.op(id) == Or);
      IDVector disjs;
      disjuncts(v, id, disjs);
      //Extract the literals from the disjuncts
      IDVector lits, nonLits;
      litsAndNonLitsOf(v, disjs, lits, nonLits);
      //This should not be a clause because that should have been caught in
      //the pure clause case.
      assert(!nonLits.empty());
      if(nonLits.size() == 1 && !lits.empty()) {
        if(v.op(nonLits[0]) == And) {
          //Form 1a: G = G1 & G2 & ...
          unordered_map<ID, ID>::iterator it = reps.find(nonLits[0]);
          ID rep;
          if(it != reps.end()) {
            rep = it->second;
          }
          else {
            rep = wilson_rep(v);
            reps.insert(unordered_map<ID, ID>::value_type(nonLits[0], rep));
          }
          IDVector clause = lits;
          clause.push_back(rep);
          if(lits.size() != 1 || rep != v.apply(Not, lits[0]))
            rv_clauses.push_back(clause);
          if(crClauses.find(rep) == crClauses.end()) {
            int numArgs;
            const ID * const andArgs = v.arguments(nonLits[0], &numArgs);
            for(int i = 0; i < numArgs; ++i) {
              wilsonRec(v, v.apply(Or, v.apply(Not, rep), andArgs[i]), rv_clauses, seen, reps, crClauses);
            }
            crClauses.insert(rep);
          }
        }
        else if(v.op(nonLits[0]) == Not) {
          int numArgs;
          const ID * const notArgs = v.arguments(nonLits[0], &numArgs);
          if(v.op(notArgs[0]) == Or) {
            //Form 1b: G = !(G1 | G2 | ...)
            const ID * const orArgs = v.arguments(notArgs[0], &numArgs);
            IDVector conjs;
            for(int i = 0; i < numArgs; ++i) {
              conjs.push_back(v.apply(Not, orArgs[i]));
            }
            lits.push_back(v.apply(And, conjs));
            wilsonRec(v, v.apply(Or, lits), rv_clauses, seen, reps, crClauses);
          }
          else {
            //cout << v.op(notArgs[0]) << endl;
            assert(v.op(notArgs[0]) == And);
            //Form 1c: G = !(G1 & G2 & ...)
            const ID * const andArgs = v.arguments(notArgs[0], &numArgs);
            IDVector disjs = lits;
            for(int i = 0; i < numArgs; ++i) {
              disjs.push_back(v.apply(Not, andArgs[i]));
            }
            wilsonRec(v, v.apply(Or, disjs), rv_clauses, seen, reps, crClauses);
          }
        }
      }
      else {
        //Form 1d: G = G1 | G2 | ...
        IDVector clause = lits;
        for(unsigned i = 0; i < nonLits.size(); ++i) {
          unordered_map<ID, ID>::iterator it = reps.find(nonLits[i]);
          ID rep;
          if(it != reps.end()) {
            rep = it->second;
          }
          else {
            rep = wilson_rep(v);
            reps.insert(unordered_map<ID, ID>::value_type(nonLits[i], rep));
          }
          clause.push_back(rep);
          if(crClauses.find(rep) == crClauses.end()) {
            wilsonRec(v, v.apply(Or, v.apply(Not, rep), nonLits[i]), rv_clauses, seen, reps, crClauses);
            crClauses.insert(rep);
          }
        }
        rv_clauses.push_back(clause);
      }
    }
  }

  void wilson(Manager::View & v, ID id,
              vector<IDVector> & rv_clauses) {
    unordered_set<ID> seen, crClauses;
    unordered_map<ID, ID> reps;
    ID aoied = AOIOfExpr(v, id);
    if(aoied == v.btrue() || aoied == v.bfalse()) {
      IDVector clause;
      clause.push_back(aoied);
      rv_clauses.push_back(clause);
    }
    else
      wilsonRec(v, aoied, rv_clauses, seen, reps, crClauses);
  }


  void wilson(Manager::View & v, IDVector & ids,
              vector<IDVector> & rv_clauses) {
    unordered_set<ID> seen, crClauses;
    unordered_map<ID, ID> reps;
    IDVector aoied = ids;
    AOIOfExprs(v, aoied);
    for(IDVector::const_iterator it = aoied.begin(); it != aoied.end(); ++it) {
      //cout << stringOf(v, *it) << endl;
      if(*it == v.btrue() || *it == v.bfalse()) {
        IDVector clause;
        clause.push_back(*it);
        rv_clauses.push_back(clause);
      }
      else {
        wilsonRec(v, *it, rv_clauses, seen, reps, crClauses);
      }
      /*
      cout << "===================================" << endl;
      for(vector< vector<ID> >::iterator it = rv_clauses.begin(); it != rv_clauses.end(); ++it) {
        for(vector<ID>::iterator it2 = it->begin(); it2 != it->end(); ++it2) {
          cout << stringOf(v, *it2) << " ";
        }
        cout << endl;
      }
      */


    }
  }

  void parents(Manager::View & v, ID id, IDMMap & map) {
    class parents_folder : public Manager::View::Folder {
    public:
      parents_folder(Manager::View & v, IDMMap & _map) : 
        Manager::View::Folder(v), map(_map) {}
      virtual ID fold(ID id, int n, const ID * const args) {
        for (int i = 0; i < n; ++i)
          map.insert(IDMap::value_type(args[i], id));
        return id;
      }
    private:
      IDMMap & map;
    };
    parents_folder mf(v, map);
    v.fold(mf, id);
  }

  void descendants(Manager::View & v, ID id, IDSetMap & map) {
    class descendants_folder : public Manager::View::Folder {
    public:
      descendants_folder(Manager::View & v, IDSetMap & _map) :
        Manager::View::Folder(v), map(_map) {}
      virtual ID fold(ID id, int n, const ID * const args) {
        IDSet & descendants = map[id];
        for (int i = 0; i < n; ++i) {
          descendants.insert(args[i]);
          IDSet & childDescendants = map[args[i]];
          descendants.insert(childDescendants.begin(), childDescendants.end());
        }
        return id;
      }
    private:
      IDSetMap & map;
    };

    descendants_folder df(v, map);
    v.fold(df, id);
  }

  void ancestors(Manager::View & v, ID node, ID id, IDVector & ancestors) {
    class ancestors_folder : public Manager::View::Folder {
    public:
      ancestors_folder(Manager::View & v, ID _node, IDVector & _ancestors) :
        Manager::View::Folder(v), ancestors(_ancestors) {
          ancestorsSet.insert(_node);
      }
      virtual ID fold(ID id, int n, const ID * const args) {
        //Is an ancestor of node if any of its arguments is an ancestor
        for(int i = 0; i < n; ++i) {
          if(ancestorsSet.find(args[i]) != ancestorsSet.end()) {
            if(ancestorsSet.insert(id).second) //Not already there
              ancestors.push_back(id);
          }
        }
        return id;
      }
    private:
      IDVector & ancestors;
      unordered_set<ID> ancestorsSet;
    };

    ancestors_folder af(v, node, ancestors);
    v.fold(af, id);
  }

  class aoe_folder : public Manager::View::Folder {
  public:
    aoe_folder(Manager::View & v) : Manager::View::Folder(v) {}
    virtual ID fold(ID id, int n, const ID * const args) {
      switch(view().op(id)) {
      case True:
      case Var:
        return id;
      case Not:
        return view().apply(Not, args[0]);
      case And:
        if (n == 2)
          return view().apply(And, args[0], args[1]);
        else {
          vector<ID> vargs;
          vOf(n, args, vargs);
          //return view().apply(And, vargs);
          ID conj = view().btrue();
          for(unsigned i = 0; i < vargs.size(); ++i) {
            conj = view().apply(And, conj, vargs[i]);
          }
          return conj;
        }
      case Or: {
        vector<ID> vargs;
        vOf(n, args, vargs);
        applyNot(vargs);
        return view().apply(Not, applyAnd(vargs));
      }
      case Equiv: {
        ID id0 = args[0];
        ID id1 = args[1];
        return view().apply(Not, 
                            view().apply(And, 
                                         view().apply(Not, view().apply(And, id0, id1)),
                                         view().apply(Not, view().apply(And, 
                                                                        view().apply(Not, id0), 
                                                                        view().apply(Not, id1)))));
      }
      case Implies:
        return view().apply(Not,
                            view().apply(And, args[0], view().apply(Not, args[1])));
      case ITE: {
        ID c = args[0];
        ID a = args[1];
        ID b = args[2];
        return view().apply(Not, view().apply(And,
                                              view().apply(Not, view().apply(And, c, a)),
                                              view().apply(Not, view().apply(And, 
                                                                             view().apply(Not, c), 
                                                                             view().apply(Not, b)))));
      }
      case TITE:
      case BV:
      default:
        assert (false);
        return id;
      }
    }
  private:
    void vOf(int n, const ID * const args, vector<ID> & vargs) {
      for (int i = 0; i < n; ++i)
        vargs.push_back(args[i]);
    }
    void applyNot(vector<ID> & vargs) {
      for (vector<ID>::iterator it = vargs.begin(); it != vargs.end(); it++)
        *it = view().apply(Not, *it);
    }
    ID applyAnd(vector<ID> & vargs) {
      return applyAnd(vargs, 0, vargs.size()-1);
    }
    ID applyAnd(vector<ID> & vargs, int l, int u) {
      assert (l <= u);
      if (l == u)
        return vargs[l];
      if (l+1 == u)
        return view().apply(And, vargs[l], vargs[u]);
      int m = (l+u)/2;
      ID lid = applyAnd(vargs, l, m);
      ID rid = applyAnd(vargs, m+1, u);
      return view().apply(And, lid, rid);
    }
  };
  ID AIGOfExpr(Manager::View & v, ID id) {
    aoe_folder af(v);
    return v.fold(af, id);
  }
  void AIGOfExprs(Manager::View & v, vector<ID> & ids) {
    aoe_folder af(v);
    v.fold(af, ids);
  }

  class aoi_folder : public Manager::View::Folder {
  public:
    aoi_folder(Manager::View & v) : Manager::View::Folder(v) {}
    virtual ID fold(ID id, int n, const ID * const args) {
      switch(view().op(id)) {
      case True:
      case Var:
        return id;
      case Not:
        return view().apply(Not, args[0]);
      case And: {
        vector<ID> vargs;
        vOf(n, args, vargs);
        return view().apply(And, vargs);
      }
      case Or: {
        vector<ID> vargs;
        vOf(n, args, vargs);
        return view().apply(Or, vargs);
      }
      case Equiv: {
        ID id0 = args[0];
        ID id1 = args[1];
        return view().apply(And,
                            view().apply(Or, view().apply(Not, id0), id1),
                            view().apply(Or, id0, view().apply(Not, id1)));
      }
      case ITE:
      case TITE:
      case BV:
      default:
        assert (false);
        return id;
      }
    }
  private:
    void vOf(int n, const ID * const args, vector<ID> & vargs) {
      for (int i = 0; i < n; ++i)
        vargs.push_back(args[i]);
    }
  };

  ID AOIOfExpr(Manager::View & v, ID id) {
    aoi_folder af(v);
    return v.fold(af, id);
  }

  void AOIOfExprs(Manager::View & v, vector<ID> & ids) {
    aoi_folder af(v);
    v.fold(af, ids);
  }

  /**
   * Class for dot folding.
   */
  class dot_folder : public Manager::View::Folder {
  public:
    /**
     * Constructor.
     */
    dot_folder(Manager::View& v, bool terse) :
      Manager::View::Folder(v), _terse(terse) {}
    /**
     * Write dot node and edges for an expression node.
     */
    ID fold(ID id, int n, const ID * const args) {
      Op op = view().op(id);
      switch(op) {
      case True:
        _buf << "{ rank=sink; " << id << " [label=\"";
        stringOfOp(op, _buf);
        _buf << "\"]; }\n";
        break;
      case Var:
        _buf << "{ rank=sink; " << id << " [label=\"";
        shortStringOfID(view(), id, _buf);
        _buf << "\"]; }\n";
        break;
      default:
        _buf << id << " [label=\"";
        stringOfOp(op, _buf);
        if (!_terse)
          _buf << ":" << id;
        _buf << "\"];\n";
        for (int i = 0; i != n; ++i) { 
          _buf << id << " -> " << args[i] << ";\n";
        }
      }
      return id;
    }
    dot_folder& operator<<(const string s) { _buf << s; return *this; }
    string out() { return _buf.str(); }
  private:
    bool _terse;
    ostringstream _buf;
  };

  std::string dotOf(Manager::View & v, 
                    ID id, 
                    const string name, 
                    bool terse, 
                    bool subgraph)
  {
    std::vector<ID> idv;
    idv.push_back(id);
    return dotOf(v, idv, name, terse, subgraph);
  }

  std::string dotOf(Manager::View & v,
                    vector<ID>& idv,
                    const string name,
                    bool terse,
                    bool subgraph) 
  {
    dot_folder dotf(v, terse);
    if (subgraph)
      dotf << "{\n";
    else {
      dotf << "digraph \"" << name << "\" {\nedge [dir=none];\n";
    }
    v.fold(dotf, idv);
    dotf << "}\n";
    return dotf.out();
  }

  /**
   * Class for circuit graph folding.
   */
  class cg_folder : public Manager::View::Folder {
  public:
    /**
     * Constructor.
     */
    cg_folder(Manager::View& v, bool terse) :
      Manager::View::Folder(v), _terse(terse) {}
    /**
     * Write dot node and edges for an expression node.
     */
    ID fold(ID id, int n, const ID * const args) {
      Op op = view().op(id);
      switch(op) {
      case True:
        _buf << "{ rank=sink; " << id << " [label=\"";
        stringOfOp(op, _buf);
        _buf << "\"]; }\n";
        break;
      case Var:
        _buf << id << " [shape=box,label=\"";
        shortStringOfID(view(), id, _buf);
        _buf << "\"];\n";
        break;
      case Not:
        break;
      default:
        _buf << id << " [label=\"";
        stringOfOp(op, _buf);
        if (!_terse)
          _buf << ":" << id;
        _buf << "\"];\n";
        for (int i = 0; i != n; ++i) {
          ID fanin = args[i];
          Op fop = view().op(fanin);
          if (fop == Not) {
            ID negation = view().apply(Not, fanin);
            _buf << negation << " -> " << id << " [style = dashed];\n";
          } else {
            _buf << fanin << " -> " << id << ";\n";
          }
        }
      }
      return id;
    }
    cg_folder& operator<<(const string s) { _buf << s; return *this; }
    string out() { return _buf.str(); }
  private:
    bool _terse;
    ostringstream _buf;
  };

  std::string circuitGraphOf(Manager::View & v,
                             vector<ID>& idv,
                             const string name,
                             bool terse,
                             bool subgraph) 
  {
    cg_folder cgf(v, terse);
    if (subgraph)
      cgf << "{\n";
    else {
      cgf << "digraph \"" << name << "\" {\nedge [dir=none];\n";
    }
    v.fold(cgf, idv);
    cgf << "}\n";
    return cgf.out();
  }

  /**
   * Class for node counting.
   */
  class count_folder : public Manager::View::Folder {
  public:
    /**
     * Constructor.
     */
    count_folder(Manager::View& v) :
      Manager::View::Folder(v), _count(0) {}
    /**
     * Increment count.
     */
    ID fold(ID id, int n, const ID * const args) {
      Op op = view().op(id);
      if (op != Not)
        _count++;
      return id;
    }
    unsigned long count() { return _count; }
  private:
    unsigned int _count;
  };

  unsigned int sizeOf(Manager::View & v, ID id)
  {
    count_folder cntf(v);
    v.fold(cntf, id);
    return cntf.count();
  }

  unsigned int sizeOf(Manager::View & v, vector<ID>& idv)
  {
    count_folder cntf(v);
    v.fold(cntf, idv);
    return cntf.count();
  }

  /**
   * Tarjan's algorithm for SCC analysis.
   */
  class sccAnalyzer {
  public:
    sccAnalyzer(Manager::View& view, unordered_map<ID, ID> const & lvs,
                vector< vector<ID> > & s) :
      v(view), leaves(lvs), count(0),  sccs(s) {}

    void searchScc(const ID id) {
      visit(id);
      int nfi;
      ID const *fanins = v.arguments(id, &nfi);
      for (int i = 0; i != nfi; ++i) {
        ID child = fanins[i];
        if (!visited(child)) {
          searchScc(child);
          updateLowLinkFromLowLink(id, child);
        } else {
          updateLowLinkFromDfsNumber(id, child);
        }
      }
      unordered_map<ID,ID>::const_iterator it = leaves.find(id);
      if (it != leaves.end()) {
        ID child = it->second;
        if (!visited(child)) {
          searchScc(child);
          updateLowLinkFromLowLink(id, child);
        } else {
          updateLowLinkFromDfsNumber(id, child);
        }
      }
      if (sccEntryPoint(id)) {
        collectScc(id);
      }
    }
    bool visited(const ID id) const
    {
      return ndInfo.find(id) != ndInfo.end();
    }

  private:
    class DfsNode {
    public:
      DfsNode(bool onStack, unsigned int dfnum, unsigned int low)
        : stacked(onStack), dfn(dfnum), lowl(low) {}
      bool stacked;
      unsigned int dfn;
      unsigned int lowl;
    };

    typedef unordered_map<ID,DfsNode> Info;

    void visit(const ID id)
    {
      ndInfo.insert(pair<const ID,DfsNode>(id,DfsNode(true,count,count)));
      count++;
      stk.push(id);
    }
    void updateLowLinkFromLowLink(const ID parent, const ID child)
    {
      DfsNode &ip = ndInfo.find(parent)->second;
      DfsNode const &ic = ndInfo.find(child)->second;
      if (ic.lowl < ip.lowl)
        ip.lowl = ic.lowl;
    }
    void updateLowLinkFromDfsNumber(const ID parent, const ID child)
    {
      DfsNode &ip = ndInfo.find(parent)->second;
      DfsNode const &ic = ndInfo.find(child)->second;
      if (ic.dfn < ip.dfn && ic.stacked && ic.dfn < ip.lowl)
        ip.lowl = ic.dfn;
    }
    bool sccEntryPoint(const ID id) const
    {
      DfsNode const &i = ndInfo.find(id)->second;
      return i.dfn == i.lowl;
    }
    void collectScc(const ID id)
    {
      vector<ID> component;
      ID x;
      do {
        x = stk.top();
        stk.pop();
        DfsNode &ix = ndInfo.find(x)->second;
        ix.stacked = false;
        component.push_back(x);
      } while (x != id);
      sccs.push_back(component);
    }

    Manager::View& v;
    unordered_map<ID, ID> const & leaves;
    stack<ID> stk;
    Info ndInfo;
    unsigned int count;
    vector< vector<ID> > & sccs;
  };

  vector< vector<ID> >
  sccsOf(Manager::View & v, vector<ID> const & roots,
         vector<ID> const & leaves, vector<ID> const & nsfv)
  {
    vector< vector<ID> > sccs;
    unordered_map<ID, ID> lmap;
    for (vector<ID>::size_type i = 0; i != leaves.size(); ++i) {
      lmap[leaves[i]] = nsfv[i];
    }
    sccAnalyzer sa(v, lmap, sccs);
    for (vector<ID>::const_iterator i = roots.begin();
         i != roots.end(); ++i) {
      if (!sa.visited(*i))
        sa.searchScc(*i);
    }
    return sccs;
  }

  void analyzeSccs(Manager::View & v, vector<ID> const & roots,
                   vector<ID> const & leaves, vector<ID> const & nsfv)
  {
    assert(leaves.size() == nsfv.size());
    vector< vector<ID> > sccs = sccsOf(v, roots, leaves, nsfv);
    unordered_map<ID, ID> lmap;
    for (vector<ID>::size_type i = 0; i != leaves.size(); ++i) {
      lmap[leaves[i]] = nsfv[i];
    }
    // Build set of state variables.
    std::unordered_set<ID> vars;
    for (vector<ID>::const_iterator i = leaves.begin();
         i != leaves.end(); ++i) {
      vars.insert(*i);
    }
    unsigned int sequential = 0;
    unsigned int trivSeq = 0;
    unsigned int maxLatches = 0;
    unsigned int coiLatches = 0;
    for (vector< vector<ID> >::const_iterator i = sccs.begin();
         i != sccs.end(); ++i) {
      vector<ID> const &component = *i;
      unsigned int latches = 0;
      // Count latches in this component.
      for (vector<ID>::const_iterator j = component.begin();
           j != component.end(); ++j) {
        if (vars.find(*j) != vars.end())
          latches++;
      }
      if (latches > 0) {
        sequential++;
        coiLatches += latches;
        if (latches > maxLatches)
          maxLatches = latches;
      }
      // This may be a trivial sequential SCC.
      if (component.size() == 1 && latches == 1) {
        ID id = lmap[component[0]];
        int nfi;
        ID const *fanins = v.arguments(id, &nfi);
        if (nfi != 1) {
          trivSeq++;
        } else {
          ID child = fanins[0];
          unordered_map<ID,ID>::const_iterator it = lmap.find(child);
          if (it == lmap.end() || lmap[child] != id)
            trivSeq++;
        }
      }
    }
    cout << sccs.size() << " SCCs of which " << sequential
         << " contain" << (sequential == 1 ? "s" : "")
         << " the " << coiLatches << " latches" << endl;
    cout << "Number of latches in the largest SCC = " << maxLatches << endl;
    cout << "Number of trivial sequential SCCs = " << trivSeq << endl;
  }

  vector< vector< vector<ID> > >
  sortStateVarsBySccHeight(Manager::View & v, vector<ID> const & roots,
                          vector<ID> const & leaves, vector<ID> const & nsfv) {
    assert(leaves.size() == nsfv.size());  
    vector< vector<ID> > sccs = sccsOf(v, roots, leaves, nsfv);

    unordered_map<ID, ID> lmap;
    for(unsigned i = 0; i < leaves.size(); ++i) {
      lmap.insert(unordered_map<ID, ID>::value_type(leaves[i], nsfv[i]));
    }
 
    //Build set of state variables
    unordered_set<ID> vars(leaves.begin(), leaves.end());

    set<unsigned> seqSccIndices;
    for(unsigned i = 0; i < sccs.size(); ++i) {
      bool seqScc = false;
      for(unsigned j = 0; j < sccs[i].size(); ++j) {
        if(vars.find(sccs[i][j]) != vars.end()) {
          seqScc = true;
          break;
        }
      }
      if(seqScc) {
        seqSccIndices.insert(i);
      }
    }

    //unordered_map<ID, unsigned> stateVarDepths;
    unordered_map<unsigned, unsigned> seqSCCDepths;
    unordered_map<ID, unsigned> nodeDepths;
    //Loop over sccs in their given topological order and determine the depth
    //of each SCC defined as the maximum depth of the fanins of its
    //elements that are outside of this SCC + 1
    for(vector< vector<ID> >::const_iterator i = sccs.begin();
        i != sccs.end(); ++i) {
      unsigned depth = 0;
      vector<ID> const &component = *i;
      //Build set of elements in this component
      unordered_set<ID> elements(component.begin(), component.end());
      //Loop over the elements of this SCC
      for(vector<ID>::const_iterator j = component.begin();
          j != component.end(); ++j) {
        //Look at all the fanin edges of this element and find out if any of
        //them is a bridge
        int nfi;
        ID const *fanins = v.arguments(*j, &nfi);
        for(int arg = 0; arg < nfi; ++arg) {
          if(elements.find(fanins[arg]) == elements.end()) {
            //This is a bridge. Get the depth of its fanin
            unordered_map<ID, unsigned>::const_iterator it =
                nodeDepths.find(fanins[arg]);
            assert(it != nodeDepths.end());
            depth = max(depth, it->second + (seqSccIndices.find(i - sccs.begin()) == seqSccIndices.end() ? 0 : 1));
          }
        }
        unordered_map<ID, ID>::const_iterator it = lmap.find(*j);
        if(it != lmap.end()) {
          if(elements.find(it->second) == elements.end()) {
            //This is also a bridge. Get the depth of its fanin
            unordered_map<ID, unsigned>::const_iterator it2 =
                nodeDepths.find(it->second);
            assert(it2 != nodeDepths.end());
            depth = max(depth, it2->second + (seqSccIndices.find(i - sccs.begin()) == seqSccIndices.end() ? 0 : 1));
          }
        }
      }
      bool hasLatches = false;
      //Set the depths of all the elements of this SCC to "depth"
      for(vector<ID>::const_iterator j = component.begin();
          j != component.end(); ++j) {
        nodeDepths.insert(unordered_map<ID, unsigned>::value_type(*j, depth));
        //If it is a state variable, also insert it into the stateVarDepths map
        if(vars.find(*j) != vars.end()) {
          hasLatches = true;
        }
      }
      if(hasLatches) {
        seqSCCDepths.insert(unordered_map<unsigned, unsigned>::value_type(
            i - sccs.begin(), depth));
      }
    }

    /*
    for(unordered_map<unsigned, unsigned>::const_iterator it = seqSCCDepths.begin();
        it != seqSCCDepths.end(); ++it){ 
      cout << it->second << " ";
      vector<ID> const &component = sccs[it->first];
      for(vector<ID>::const_iterator j = component.begin();
          j != component.end(); ++j) {
        if(vars.find(*j) != vars.end())
          cout << *j << " ";
      }
      cout << endl;
    }
    */

    //Get the inverse map
    multimap<unsigned, unsigned> depthToSeqSCCIndex;
    set<unsigned> depths;
    for(unordered_map<unsigned, unsigned>::const_iterator it = seqSCCDepths.begin();
        it != seqSCCDepths.end(); ++it) {
      depthToSeqSCCIndex.insert(multimap<unsigned, unsigned>::value_type(
          it->second, it->first));
      depths.insert(it->second);
    }

    vector< vector< vector<ID> > > rv;
    pair<multimap<unsigned, unsigned>::const_iterator, 
         multimap<unsigned, unsigned>::const_iterator> ret;
    for(set<unsigned>::const_iterator it = depths.begin(); it != depths.end();
        ++it) {
      rv.push_back(vector< vector<ID> >());
      ret = depthToSeqSCCIndex.equal_range(*it);
      for(multimap<unsigned, unsigned>::const_iterator mIt = ret.first;
          mIt != ret.second; ++mIt) {
        rv.back().push_back(vector<ID>());
        //Add all the state variables in this SCC to rv
        vector<ID> const &component = sccs[mIt->second];
        for(vector<ID>::const_iterator j = component.begin();
            j != component.end(); ++j) {
          if(vars.find(*j) != vars.end()) {
            rv.back().back().push_back(*j);
          }
        }
      }
    }

    /*
    for(unsigned i = 0; i < rv.size(); ++i) {
      for(unsigned j = 0; j < rv[i].size(); ++j) {
        for(unsigned k = 0; k < rv[i][j].size(); ++k) {
          cout << rv[i][j][k] << " ";
        }
        cout << endl;
      }
      cout << endl << endl;
    }
    */

    return rv;
  }

  vector< vector< vector<ID> > >
  sortStateVarsBySccDepth(Manager::View & v, vector<ID> const & roots,
                          vector<ID> const & leaves, vector<ID> const & nsfv,
                          bool useMaximum) {
    assert(leaves.size() == nsfv.size());
    vector< vector<ID> > sccs = sccsOf(v, roots, leaves, nsfv);

    unordered_map<ID, ID> lmap;
    for(unsigned i = 0; i < leaves.size(); ++i) {
      lmap.insert(unordered_map<ID, ID>::value_type(leaves[i], nsfv[i]));
    }
 
    //Build set of state variables
    unordered_set<ID> vars(leaves.begin(), leaves.end());

    unordered_map<ID, unsigned> idToSccIndex;
    set<unsigned> seqSccIndices;
    //Build a map from ID to index of SCC the ID belongs to
    for(unsigned i = 0; i < sccs.size(); ++i) {
      bool seqScc = false;
      for(unsigned j = 0; j < sccs[i].size(); ++j) {
        idToSccIndex.insert(unordered_map<ID, unsigned>::value_type(
            sccs[i][j], i));
        if(vars.find(sccs[i][j]) != vars.end()) {
          seqScc = true;
        }
      }
      if(seqScc) {
        seqSccIndices.insert(i);
      }
    }

    //cout << printSccQuotientGraph(v, leaves, nsfv, vars, sccs, idToSccIndex) << endl;

    //The depth of each SCC. Initially depths will be set to infinity
    vector<unsigned> sccDepths;
    if(useMaximum) {
      sccDepths.insert(sccDepths.end(), sccs.size(), 0);
    }
    else {
      sccDepths.insert(sccDepths.end(), sccs.size(), UINT_MAX);
    }
    //Set the depth of the last SCC in the topological order (output SCC) to 0
    sccDepths.back() = 0;

    //Loop over SCCs in an inverse topological order and for each SCC i, set
    //the depth of each of its fanin SCCs j to the minimum of SCC i's depth + 1
    //and SCC j's current depth
    for(int i = sccs.size() - 1; i >= 0; --i) {
      vector<ID> const &component = sccs[i];
      //Build set of elements in this component
      unordered_set<ID> elements(component.begin(), component.end());
      //Loop over the elements of this SCC
      for(vector<ID>::const_iterator j = component.begin();
          j != component.end(); ++j) {
        //Look at all the fanin edges of this element and find out if any of
        //them is a bridge
        int nfi;
        ID const *fanins = v.arguments(*j, &nfi);
        for(int arg = 0; arg < nfi; ++arg) {
          if(elements.find(fanins[arg]) == elements.end()) {
            //This is a bridge. Set the depth of its fanin SCC
            unordered_map<ID, unsigned>::const_iterator it =
                idToSccIndex.find(fanins[arg]);
            assert(it != idToSccIndex.end());
            if(useMaximum) {
              sccDepths[it->second] = max(sccDepths[it->second], sccDepths[i] + (seqSccIndices.find(i) == seqSccIndices.end() ? 0 : 1));
            }
            else {
              sccDepths[it->second] = min(sccDepths[it->second], sccDepths[i] + (seqSccIndices.find(i) == seqSccIndices.end() ? 0 : 1));
            }
          }
        }
        unordered_map<ID, ID>::const_iterator it = lmap.find(*j);
        if(it != lmap.end()) {
          if(elements.find(it->second) == elements.end()) {
            //This is also a bridge. Set the depth of its fanin SCCs
            unordered_map<ID, unsigned>::const_iterator it2 =
                idToSccIndex.find(it->second);
            assert(it2 != idToSccIndex.end());
            if(useMaximum) {
              sccDepths[it2->second] = max(sccDepths[it2->second], sccDepths[i] + (seqSccIndices.find(i) == seqSccIndices.end() ? 0 : 1));
            }
            else {
              sccDepths[it2->second] = min(sccDepths[it2->second], sccDepths[i] + (seqSccIndices.find(i) == seqSccIndices.end() ? 0 : 1));
            }
          }
        }
      }
    }

    //Create a map from depth to SCC index, only for sequential SCCs
    unordered_multimap<unsigned, unsigned> depthToSeqSCCIndex;
    set<unsigned> depths;
    for(set<unsigned>::const_iterator it = seqSccIndices.begin(); it != seqSccIndices.end(); ++it) {
      depthToSeqSCCIndex.insert(unordered_multimap<unsigned, unsigned>::value_type(
          sccDepths[*it], *it));
      depths.insert(sccDepths[*it]);
    }

    vector< vector< vector<ID> > > rv;
    pair<unordered_multimap<unsigned, unsigned>::const_iterator, 
         unordered_multimap<unsigned, unsigned>::const_iterator> ret;
    for(set<unsigned>::const_iterator it = depths.begin(); it != depths.end();
        ++it) {
      rv.push_back(vector< vector<ID> >());
      ret = depthToSeqSCCIndex.equal_range(*it);
      for(unordered_multimap<unsigned, unsigned>::const_iterator mIt = ret.first;
          mIt != ret.second; ++mIt) {
        rv.back().push_back(vector<ID>());
        //Add all the state variables in this SCC to rv
        vector<ID> const &component = sccs[mIt->second];
        for(vector<ID>::const_iterator j = component.begin();
            j != component.end(); ++j) {
          if(vars.find(*j) != vars.end()) {
            rv.back().back().push_back(*j);
          }
        }
      }
    }

    /*
    for(unsigned i = 0; i < rv.size(); ++i) {
      for(unsigned j = 0; j < rv[i].size(); ++j) {
        for(unsigned k = 0; k < rv[i][j].size(); ++k) {
          cout << rv[i][j][k] << " ";
        }
        cout << endl;
      }
      cout << endl << endl;
    }
    */

    return rv;
  }

  string printSccQuotientGraph(Manager::View & v, vector<ID> const & roots,
                               vector<ID> const & leaves, 
                               vector<ID> const & nsfv) {

    assert(leaves.size() == nsfv.size());
    vector< vector<ID> > sccs = sccsOf(v, roots, leaves, nsfv);

    unordered_map<ID, ID> lmap;
    for(unsigned i = 0; i < leaves.size(); ++i) {
      lmap.insert(unordered_map<ID, ID>::value_type(leaves[i], nsfv[i]));
    }
    
    //Build set of state variables
    unordered_set<ID> vars(leaves.begin(), leaves.end());

    unordered_map<ID, unsigned> idToSccIndex;
    vector<unsigned> seqSccIndices;
    //Build a map from ID to index of SCC the ID belongs to
    for(unsigned i = 0; i < sccs.size(); ++i) {
      bool seqScc = false;
      for(unsigned j = 0; j < sccs[i].size(); ++j) {
        idToSccIndex.insert(unordered_map<ID, unsigned>::value_type(
            sccs[i][j], i));
        if(vars.find(sccs[i][j]) != vars.end()) {
          seqScc = true;
        }
      }
      if(seqScc) {
        seqSccIndices.push_back(i);
      }
    }

    ostringstream dot;
    dot << "digraph SCCs {" << endl
        << "{ rank=sink;" << endl
        << "invisible [style=invisible];" << endl
        << "}" << endl
        << "concentrate=\"true\"" << endl
        << "rankdir=\"LR\"" << endl;
    for(unsigned i = 0; i < sccs.size(); ++i) {
      bool seqScc = false;
      vector<ID> stateVarIds;
      for(unsigned j = 0; j < sccs[i].size(); ++j) {
        if(vars.find(sccs[i][j]) != vars.end()) {
          seqScc = true;
          stateVarIds.push_back(sccs[i][j]);
        }
      }
      if(seqScc) {
        dot << i << " [style=filled, fillcolor=red, label=";
        dot << "\"";
        for(unsigned j = 0; j < stateVarIds.size(); ++j) {
          dot << stringOf(v, stateVarIds[j]);
          if(j != stateVarIds.size() - 1) {
            dot << "\\n";
          }
        }
        dot << "\"];" << endl;
      }
      else {
        dot << i << ";" << endl;
      }
    }

    for(unsigned i = 0; i < sccs.size(); ++i) {
      unordered_set<ID> elements;
      for(unsigned j = 0; j < sccs[i].size(); ++j) {
        elements.insert(sccs[i][j]);
      }
      for(unsigned j = 0; j < sccs[i].size(); ++j) {
        int nfi;
        ID const *fanins = v.arguments(sccs[i][j], &nfi);
        for(int arg = 0; arg < nfi; ++arg) {
          if(elements.find(fanins[arg]) == elements.end()) {
            dot << idToSccIndex[fanins[arg]] << " -> " << i << ";" << endl;
          }
        }
        unordered_map<ID, ID>::const_iterator it = lmap.find(sccs[i][j]);
        if(it != lmap.end()) {
          if(elements.find(it->second) == elements.end()) {
            dot << idToSccIndex[it->second] << " -> " << i << ";" << endl;
          }
        }
      }
    }

    dot << sccs.size() - 1 << " -> invisible" << endl;

    dot << "}" << endl;

    return dot.str();
  }


}
