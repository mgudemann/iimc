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

#include <algorithm>
#include <assert.h>
#include <vector>

#include <iostream>

#include "Expr.h"

const uint64_t NMASK_ID = (static_cast<uint64_t>(1) << 16) - 1;
const uint64_t MASK_ID = ~NMASK_ID;
const int SH_ID = 16;
const uint64_t MASK_PRIMES = (static_cast<uint64_t>(1) << 16) - 4;
const int SH_PRIMES = 2;
const uint64_t MASK_NEG = 1;

using namespace std;

#define unaryOp(op)  (op == Not || op == F || op == G || op == X)
#define binaryOp(op) (op == And || op == Or || op == Equiv || op == Implies || op == U || op == R || op == W)

namespace Expr {

  Manager::View::View(Manager * man) : HSManager<Expr>::HSView::HSView(man) {
    this->man = man;
  }

  Manager::View::~View() {
  }

  Manager::View * Manager::View::clone() const {
    return new View(*this);
  }

  Manager & Manager::View::manager() {
    return *man;
  }

  ID Manager::View::btrue() { return man->trueID; }
  ID Manager::View::bfalse() { return man->falseID; }

  ID Manager::View::newVar(const string & _name) {
    Expr * e = new Expr(_name);
    bool exists;
    ID id = add(e, &exists) << SH_ID;
    if (exists) delete e;
    return id;
  }
  const string & Manager::View::varName(ID id) {
    assert (op(id) == Var);
    Expr * e = get(id >> SH_ID);
    return e->u.varName;
  }

  bool Manager::View::varExists(const std::string & name) {
    Expr e(name);
    return exists(&e);
  }

  Op Manager::View::op(ID id) {
    if (MASK_NEG & id) {
      return Not;
    }
    else {
      Expr * e = get(id >> SH_ID);
      assert (e != NULL);
      return e->op;
    }
  }

  ID Manager::View::apply(Op op, ID arg) {
    assert (unaryOp(op));
    switch (op) {
    case Not:
      return (MASK_NEG ^ arg);
    case F:
    case G:
    case X: {
      //if (arg == btrue() || arg == bfalse()) return arg;
      Expr * e = new Expr(op, arg);
      bool exists;
      ID id = add(e, &exists) << SH_ID;
      if (exists) delete e;
      return id;
    }
    default:
      assert (false);
    }
  }
  ID Manager::View::apply(Op op, ID arg0, ID arg1) {
    assert (binaryOp(op));
    bool positive = true;
    bool ac = op == And || op == Or || op == Equiv || op == Eq;

    if (ac && arg0 > arg1) {
      ID t = arg1;
      arg1 = arg0;
      arg0 = t;
    }

    switch (op) {
    case And:
      if (arg0 == arg1) return arg0;
      if (arg0 == btrue()) return arg1;
      if (arg1 == btrue()) return arg0;
      if (arg0 == bfalse() || arg1 == bfalse()) return bfalse();
      if ((MASK_NEG ^ arg1) == arg0) return bfalse();
      break;
    case Or:
      if (arg0 == arg1) return arg0;
      if (arg0 == bfalse()) return arg1;
      if (arg1 == bfalse()) return arg0;
      if (arg0 == btrue() || arg1 == btrue()) return btrue();
      if ((MASK_NEG ^ arg1) == arg0) return btrue();
      break;
    case Equiv:
      if (arg0 == arg1) return btrue();
      if (arg0 == btrue()) return arg1;
      if (arg1 == btrue()) return arg0;
      if (arg0 == bfalse()) return apply(Not, arg1);
      if (arg1 == bfalse()) return apply(Not, arg0);
      if ((MASK_NEG ^ arg1) == arg0) return bfalse();
      // keep both arguments positive
      if (arg0 & MASK_NEG) { arg0 = MASK_NEG ^ arg0; positive = !positive; }
      if (arg1 & MASK_NEG) { arg1 = MASK_NEG ^ arg1; positive = !positive; }
      break;
    case Implies:
      if (arg0 == arg1) return btrue();
      if (arg0 == btrue()) return arg1;
      if (arg1 == btrue()) return btrue();
      if (arg0 == bfalse()) return btrue();
      if (arg1 == bfalse()) return apply(Not, arg0);
      if ((MASK_NEG ^ arg0) == arg1) return arg1;
      if ((arg0 & MASK_NEG) && (arg1 & MASK_NEG)) {
        ID tmp = MASK_NEG ^ arg0;
        arg0 = MASK_NEG ^ arg1;
        arg1 = tmp;
      }
      break;
    case Eq:
      if (arg0 == arg1) return btrue();
      break;
    case U:
      if (arg0 == arg1) return arg1;
      if (arg0 == bfalse()) return arg1;
      if (arg0 == btrue()) return apply(F, arg1);
      if (arg1 == bfalse()) return bfalse();
      if (arg1 == btrue()) return btrue();
      if ((MASK_NEG ^ arg0) == arg1) return apply(F, arg1);
      break;
    case R:
      if (arg0 == arg1) return arg1;
      if (arg0 == bfalse()) return apply(G, arg1);
      if (arg0 == btrue()) return arg1;
      if (arg1 == bfalse()) return bfalse();
      if (arg1 == btrue()) return btrue();
      if ((MASK_NEG ^ arg0) == arg1) return apply(G, arg1);
    case W:
      if (arg0 == arg1) return arg1;
      if (arg0 == bfalse()) return arg1;
      if (arg0 == btrue()) return btrue();
      if (arg1 == bfalse()) return apply(G, arg0);
      if (arg1 == btrue()) return btrue();
      if ((MASK_NEG ^ arg0) == arg1) return btrue();
      break;
    default:
      assert (false);
    }

    Expr * e = new Expr(op, arg0, arg1);
    bool exists;
    ID id = add(e, &exists) << SH_ID;
    if (exists) delete e;
    if (positive)
      return id;
    else
      return apply(Not, id);
  }

  ID Manager::View::apply(Op _op, vector<ID> & args, bool simplify) {
    bool comp = false;
    if (simplify) {
      if (_op == And || _op == Or) {
        sort(args.begin(), args.end());
        /* 1. eliminate redundancy
         * 2. look for l, !l */
        vector<ID>::iterator it = args.begin();
        if (it != args.end())
          while (it+1 != args.end()) {
            if (*it == btrue() && _op == Or)
              return btrue();
            if (*it == bfalse() && _op == And)
              return bfalse();
            if ((MASK_NEG ^ *it) == *(it+1)) {
              if (_op == And) return bfalse();
              if (_op == Or) return btrue();
            }
            if (*it == *(it+1) || (*it == btrue() && _op == And) || (*it == bfalse() && _op == Or))
              args.erase(it);
            else
              it++;
          }
        else
          if (_op == And)
            return btrue();
          else
            return bfalse();
      }

      int n = args.size();
      if (n == 1 && unaryOp(_op)) {
        return apply(_op, args[0]);
      }
      else if (n == 1 && (_op == And || _op == Or)) {
        return args[0];
      }
      else if (n == 2 && binaryOp(_op)) {
        return apply(_op, args[0], args[1]);
      }

      if (_op == ITE) {
        assert (n == 3);
        // ite(1,f,g) =f
        if (args[0] == btrue())
          return args[1];
        // ite(0,f,g) = g
        if (args[0] == bfalse())
          return args[2];
        // ite(f,1,0) = f
        if (args[1] == btrue() && args[2] == bfalse())
          return args[0];
        // ite(f,0,1) = !f
        if (args[1] == bfalse() && args[2] == btrue())
          return apply(Not, args[0]);
        // ite(f,g,g) = g
        if (args[1] == args[2])
          return args[1];
        // ite(f,f,g) = ite(f,1,g) = f || g
        if (args[0] == args[1] || args[1] == btrue())
          return apply(Or, args[0], args[2]);
        // ite(f,g,f) = ite(f,g,0) = f && g
        if (args[0] == args[2] || args[2] == bfalse())
          return apply(And, args[0], args[1]);
        // ite(f,!f,g) = ite(f,0,g) = !f && g
        if (args[0] == apply(Not, args[1]) || args[1] == bfalse())
          return apply(And,apply(Not,args[0]), args[2]);
        // ite(f,g,!f) = ite(f,g,1) = !f || g
        if (args[0] == apply(Not, args[2]) || args[2] == btrue())
          return apply(Or, apply(Not, args[0]), args[1]);
        // ite(f,g,!g) = (f = g)
        if (args[1] == apply(Not, args[2]))
          return apply(Equiv, args[0], args[1]);
        bool fc = op(args[0]) == Not;
        bool sc = op(args[1]) == Not;
        if (fc || sc) {
          // ite(f,g,h) = ...
          if (fc && !sc) {
            // ite(!f,h,g)
            args[0] = apply(Not, args[0]);
            ID t = args[1];
            args[1] = args[2];
            args[2] = t;
          }
          else if (!fc && sc) {
            // !ite(f,!g,!h)
            args[1] = apply(Not, args[1]);
            args[2] = apply(Not, args[2]);
            comp = true;
          }
          else if (fc && sc) {
            // !ite(!f,!h,!g)
            args[0] = apply(Not, args[0]);
            ID t = args[1];
            args[1] = apply(Not, args[2]);
            args[2] = apply(Not, t);
            comp = true;
          }
        }
      }
    }

    Expr * e = new Expr(_op, args);
    bool exists;
    ID id =add(e, &exists) << SH_ID;
    if (exists) delete e;
    if (comp) id = apply(Not, id);
    return id;
  }

  ID Manager::View::prime(ID id, int delta) {
    // precondition: op(get(id>>SH_ID)) == Var
    return (((~MASK_PRIMES)&id) | (MASK_PRIMES&((((MASK_PRIMES&id)>>SH_PRIMES)+delta)<<SH_PRIMES)));
  }
  ID Manager::View::unprime(ID id, int delta) {
    // precondition: op(get(id>>SH_ID)) == Var
    return (((~MASK_PRIMES)&id) | (MASK_PRIMES&((((MASK_PRIMES&id)>>SH_PRIMES)-delta)<<SH_PRIMES)));
  }
  ID Manager::View::primeTo(ID id, int n) {
    // precondition: op(get(id>>SH_ID)) == Var
    long nl = n;
    return (((~MASK_PRIMES)&id) | (MASK_PRIMES&(nl<<SH_PRIMES)));
  }
  int Manager::View::nprimes(ID id) {
    // precondition: op(get(id>>SH_ID)) == Var
    int n = (int) ((MASK_PRIMES&id)>>SH_PRIMES);
    if (n >> (SH_ID-SH_PRIMES-1)) n |= (MASK_ID >> SH_PRIMES);
    return n;
  }

  const ID * Manager::View::arguments(ID id, int * nArgs) {
    if (MASK_NEG & id) {
      *nArgs = 1;
      childrenIDs1[0] = MASK_NEG ^ id;
      return childrenIDs1;
    }
    if (id == btrue() || id == bfalse()) {
      *nArgs = 0;
      return NULL;
    }
    Expr * e = get(id >> SH_ID);
    assert (e != NULL);
    if (e->op == Var) {
      *nArgs = 0;
      return NULL;
    }
    if (e->ext) {
      *nArgs = e->u.extendedArgs.n;
      return e->u.extendedArgs.args;
    }
    *nArgs = unaryOp(e->op) ? 1 : 2;
    return e->u.args;
  }

  ID Manager::View::Folder::fold(ID id, int n, const ID * const args) {
    Expr * e = v.get(id >> SH_ID);
    if ((e->ext && e->u.extendedArgs.args == args) ||
        (!e->ext && e->u.args == args))
      return id;
    else
      return v.replaceArguments(id, e, n, args);
  }

  ID Manager::View::fold(Folder & _f, ID id) {
    fold_fold f(_f);
    return relevantHS(id)->fold(this, f, id);
  }

  void Manager::View::fold(Folder & _f, vector<ID> & ids) {
    fold_fold f(_f);
#if 0
    ID2IDMap seen;
    for (vector<ID>::iterator it = ids.begin(); it != ids.end(); it++)
      *it = relevantHS(*it)->fold(this, f, *it, &seen);
#endif
    if (ids.empty())
      return;
    relevantHS(ids.at(0))->fold(this, f, ids);
  }

  void Manager::View::sort(vector<ID>::iterator begin, vector<ID>::iterator end) {
    std::sort(begin, end);
  }

  ID Manager::View::replaceArguments(ID id, const Expr * const e, int n, const ID * const args) {
    if (e->op == True)
      return id;
    if (MASK_NEG & id)
      return MASK_NEG ^ args[0];
    if (e->op == Var)
      return modifyID(newVar(e->u.varName), id);
    if (e->ext) {
      vector<ID> vargs;
      assert (n == e->u.extendedArgs.n);
      for (int i = 0; i < n; ++i)
        vargs.push_back(args[i]);
      return apply(e->op, vargs);
    }
    return unaryOp(e->op) ? apply(e->op, args[0]) : apply(e->op, args[0], args[1]);
  }

  ID Manager::View::hsID(ID id) { return id >> SH_ID; }
  ID Manager::View::modifyID(ID id, ID by) { return (MASK_ID & id) | (~MASK_ID & by); }

  Manager::Manager() : HSManager<Expr>() {
    Expr * e = new Expr(True);
    trueID = global->add(e) << SH_ID;
    falseID = MASK_NEG ^ trueID;
    View v(this);
    global->keep(&v, trueID);
    global->keep(&v, falseID);
  }

  Manager::View * Manager::newView() {
    View * v = new View(this);
    return v;
  }

}
