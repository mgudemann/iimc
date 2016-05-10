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

#include "StringTR.h"
#include "ExprUtil.h"
#include <sstream>

using namespace std;

namespace {
  struct stringTRfolder : public Expr::Manager::View::Folder
  {
    stringTRfolder(Expr::Manager::View* v) : Expr::Manager::View::Folder(*v)
    {;}

    ostringstream ss;

    virtual ID fold(ID id, int n, const ID * const args)
    {
      // don't handle Not
      switch(view().op(id)) {
        case Expr::Not:
        case Expr::Var:
        case Expr::True:
          return id;
        //case Expr::Or:
          //assert(false);
        case Expr::TITE:
          assert(false);
        case Expr::BV:
          assert(false);
          return id;
        default:
          break;
      }
      if(view().op(id) == Expr::Not)
        return id;
      // get string of id
      Expr::shortStringOfID(view(), id, ss);
      ss << " = ";
      switch(view().op(id)) {
        case Expr::Or: ss << "Or( "; break;
        case Expr::And: ss << "And( "; break;
        case Expr::Equiv: ss << "Equiv( "; break;
        case Expr::ITE: ss << "ITE( "; break;
        default: assert(false); break;
      }

      for(int i = 0; i < n; i++) {
        ID aid = args[i];
        if(view().op(aid) == Expr::Not) {
          ss << "!";
          aid = view().apply(Expr::Not, aid);
        }
        Expr::shortStringOfID(view(), aid, ss);
        ss << " ";
      }

      ss << ")" << endl;
      return id;
    }
  };
} // namespace

namespace CNF {
  string stringTR(Expr::Manager::View* v, vector<ID> ids)
  {
    stringTRfolder strf(v);
    v->fold(strf, ids);
    for(unsigned i = 0; i < ids.size(); ++i) {
      ID tid = ids[i];
      strf.ss << "Output: ";
      if(v->op(tid) == Expr::Not) {
        tid = v->apply(Expr::Not, tid);
        strf.ss << "!";
      }
      Expr::shortStringOfID(*v, tid, strf.ss);
      strf.ss << endl;
    }
    return strf.ss.str();
  }

  string stringTR(Expr::Manager::View* v, ID id)
  {
    stringTRfolder strf(v);
    v->fold(strf, id);
    ID tid = id;
    strf.ss << "Output: ";
    if(v->op(tid) == Expr::Not) {
      tid = v->apply(Expr::Not, tid);
      strf.ss << "!";
    }
    Expr::shortStringOfID(*v, tid, strf.ss);
    strf.ss << endl;
    return strf.ss.str();
  }

  string stringOfID(Expr::Manager::View* v, ID id)
  {
    ostringstream ss;
    Expr::shortStringOfID(*v, id, ss);
    return ss.str();
  }

  string stringOfVectorID(Expr::Manager::View* v, const vector<ID>& ids) {
    ostringstream ss;
    ss << "{";
    bool first = true;
    for(unsigned i = 0; i < ids.size(); ++i) {
      if(first)
        first = false;
      else
        ss << ", ";
      ss << stringOfID(v, ids[i]);
    }

    ss << "}";
    return ss.str();
  }

  string stringOfVectorVectorID(Expr::Manager::View* v, const vector<vector<ID> >& ids) {
    ostringstream ss;
    ss << "[";
    bool first = true;
    for(unsigned i = 0; i < ids.size(); ++i) {
      if(first)
        first = false;
      else
        ss << ", ";
      ss << stringOfVectorID(v, ids[i]);
    }

    ss << "]";
    return ss.str();
  }
}
