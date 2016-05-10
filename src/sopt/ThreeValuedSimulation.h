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

#ifndef _ThreeValuedSimulation_
#define _ThreeValuedSimulation_

/** @file ThreeValuedSimulation.h */

#include "Expr.h"

#include <unordered_map>

namespace ThreeValued {

  enum TV { TVFalse, TVTrue, TVX };
  typedef std::unordered_map<ID, TV> Map;

  inline TV tv_not(TV tv) {
    switch (tv) {
    case TVFalse:
      return TVTrue;
    case TVTrue:
      return TVFalse;
    default:
      return TVX;
    }
  }

  inline TV tv_and(TV tv1, TV tv2) {
    if (tv1 == TVFalse || tv2 == TVFalse)
      return TVFalse;
    if (tv1 == TVTrue)
      return tv2;
    if (tv2 == TVTrue)
      return tv1;
    return TVX;
  }

  inline TV tv_ite(TV c, TV a, TV b) {
    if (c == TVTrue) return a;
    if (c == TVFalse) return b;
    if (a == b) return a;
    return TVX;
  }

  class Folder : public Expr::Manager::View::Folder {
  public:
    Folder(Expr::Manager::View & v, Map & map) : Expr::Manager::View::Folder(v), map(map) {
      map.insert(Map::value_type(v.btrue(), TVTrue));
      map.insert(Map::value_type(v.bfalse(), TVFalse));
    }
    virtual bool filter(ID id) {
      return (map.find(id) == map.end());
    }
    virtual ID fold(ID id, int n, const ID * const args) {
      TV rv;
      switch (view().op(id)) {
      case Expr::True:
      case Expr::Var: {
        Map::const_iterator it = map.find(id);
        rv = it != map.end() ? it->second : TVX;
        break;
      }
      case Expr::Not: {
        Map::const_iterator it = map.find(args[0]);
        rv = tv_not(it->second);
        break;
      }
      case Expr::And: {
        assert (n == 2);
        Map::const_iterator it0 = map.find(args[0]);
        Map::const_iterator it1 = map.find(args[1]);
        rv = tv_and(it0->second, it1->second);
        if (rv == TVX) mux(id, n, args, rv);
        break;
      }
      default:
        assert (false);
      }
      map.insert(Map::value_type(id, rv));
      return id;
    }
  private:
    Map & map;
    void mux(ID id, int n, const ID * const args, TV & rv) {
      assert (n == 2);
      if (view().op(args[0]) != Expr::Not) return;
      if (view().op(args[1]) != Expr::Not) return;
      ID l = view().apply(Expr::Not, args[0]);
      if (view().op(l) != Expr::And) return;
      ID r = view().apply(Expr::Not, args[1]);
      if (view().op(r) != Expr::And) return;
      const ID * const argsl = view().arguments(l, &n);
      assert (n == 2);
      const ID * const argsr = view().arguments(r, &n);
      assert (n == 2);
      ID a, b, c;
      if (argsl[0] == view().apply(Expr::Not, argsr[0])) {
        a = argsl[1];
        b = argsr[1];
        c = argsl[0];
      }
      else if (argsl[0] == view().apply(Expr::Not, argsr[1])) {
        a = argsl[1];
        b = argsr[0];
        c = argsl[0];
      }
      else if (argsl[1] == view().apply(Expr::Not, argsr[0])) {
        a = argsl[0];
        b = argsr[1];
        c = argsl[1];
      }
      else if (argsl[1] == view().apply(Expr::Not, argsr[1])) {
        a = argsl[0];
        b = argsr[0];
        c = argsl[1];
      }
      else return;
      if (view().op(c) == Expr::Not) {
        ID t = a;
        a = b;
        b = t;
        c = view().apply(Expr::Not, c);
      }
      TV tva = map.find(a)->second, 
         tvb = map.find(b)->second, 
         tvc = map.find(c)->second;
      rv = tv_not(tv_ite(tvc, tva, tvb));
      return;
    }
  };

}

#endif
