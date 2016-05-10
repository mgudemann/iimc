/* -*- C++ -*- */

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

#ifndef EXPR_NODE_
#define EXPR_NODE_

/** @file ExprNode.h */

#include "ExprTypes.h"

namespace {
  inline size_t HCOMB(size_t x, size_t y) { return (17 * x)^y; }
}

namespace Expr {

  enum Op { Var, True, Not, And, Or, Equiv, Implies, ITE, BV, F, G, X, U, R, W, TITE, Eq };

  class Expr {
  public:
    explicit Expr(std::string const & s) : op(Var), ext(false), u(s) {}
  Expr(Op o, ID id0, ID id1) : op(o), ext(false), u(id0, id1) {}
  Expr(Op o, ID id) : op(o), ext(false), u(id) {}
  Expr(Op o) : op(o), ext(false), u() {}
  Expr(Op o, std::vector<ID> const & idv) :
    op(o), ext(idv.size() > 2), u(idv) {}
    ~Expr() {
      using namespace std;
      if (op == Var)
        u.varName.~string();
      else if (ext)
        delete [] u.extendedArgs.args;
    }
    struct hash {
      std::hash<std::string> hs;
      std::hash<ID> hid;
      std::hash<size_t> ht;
      std::hash<int> hop;
      size_t operator()(Expr const * const e) const {
        size_t rv;
        if (e->op == Var) {
          rv = hs(e->u.varName);
        }
        else {
          size_t s = 0;
          if (e->ext)
            for (int i = 0; i < e->u.extendedArgs.n; ++i)
              s = HCOMB(s, 1019 * hid(e->u.extendedArgs.args[i]));
          else {
            s = HCOMB(s, 1019 * hid(e->u.args[0]));
            s = HCOMB(s, 1019 * hid(e->u.args[1]));
          }
          rv = ht(HCOMB(s, 7919 * hop(e->op)));
        }
        return rv;
      }
    };
    struct equal {
      bool operator()(const Expr * const & e1, const Expr * const & e2) const {
        if (e1->op != e2->op || e1->ext != e2->ext)
          return false;
        if (e1->op == Var)
          return (e1->u.varName == e2->u.varName);
        if (e1->ext) {
          if (e1->u.extendedArgs.n != e2->u.extendedArgs.n)
            return false;
          for (int i = 0; i < e1->u.extendedArgs.n; ++i)
            if (e1->u.extendedArgs.args[i] != e2->u.extendedArgs.args[i])
              return false;
        }
        else {
          if (e1->u.args[0] != e2->u.args[0] || e1->u.args[1] != e2->u.args[1])
            return false;
        }
        return true;
      }
    };
    union U {
    U(std::string const & s) : varName(s) {}
    U() : args{0, 0} {}
    U(ID id) : args{id, 0} {}
    U(ID id0, ID id1) : args{id0, id1} {}
      U(std::vector<ID> const & idv) {
        int n = idv.size();
        if (n == 0) {
          U();
        } else if (n == 1) {
          U(idv.at(0));
        } else if (n == 2) {
          U(idv.at(0), idv.at(1));
        } else {
          ID * p = new ID[n];
          std::copy(idv.begin(), idv.end(), p);
          extendedArgs.n = n;
          extendedArgs.args = p;
        }
      }
      ~U() {}
      std::string varName;
      ID args[2];
      struct { int n; ID * args; } extendedArgs;
    };
    Op op;
    bool ext;
    U u;
  };
}

#endif
