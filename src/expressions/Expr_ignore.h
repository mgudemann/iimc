/* -*- C++ -*- */

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

#ifndef _Expr_ignore_
#define _Expr_ignore_

/** @file Expr_ignore.h */

#define HCOMB(x,y) ((17*x)^y)
class Expr {
public:
  ~Expr() {
    if (ext)
      delete[] u.extendedArgs.args;
    else if (op == Var)
      delete u.varName;
  }
  Op op;
  bool ext;
  union {
    std::string * varName;
    ID args[2];
    struct {
      int n;
      ID * args;
    } extendedArgs;
  } u;
  struct hash {
    std::hash<std::string> hs;
    std::hash<ID> hid;
    std::hash<size_t> ht;
    std::hash<int> hop;
    size_t operator()(const Expr * const & e) const {
      size_t rv;
      if (e->op == Var) {
        rv = hs(*(e->u.varName));
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
        return (e1->u.varName->compare(*(e2->u.varName)) == 0);
      if (e1->ext) {
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
};

#endif
