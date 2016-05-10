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

#include "ExprVerilog.h"
#include "ExprUtil.h"
#include <sstream>

using namespace std;

namespace Expr {

/**
 * Class for Verilog folding.
 */
class vlg_folder : public Manager::View::Folder {
public:
  /**
   * Constructor.
   */
  vlg_folder(Manager::View & v) : Manager::View::Folder(v), buf() {}
  /**
   * Build Verilog assignment for an expression node.
   */
  ID fold(ID id, int n, const ID * const args) {
    Op op = view().op(id);
    switch(op) {
    case True:
      buf << "  wire ";
      shortStringOfID(view(), id, buf);
      buf << " = 1;\n";
      break;
    case Var:
      break;
    case Not:
#if 0
      buf << "  wire ";
      shortStringOfID(view(), id, buf);
      buf << " = ~";
      shortStringOfID(view(), args[0], buf);
      buf << ";\n";
#endif
      break;
    case And:
      assert(n>0);
      buf << "  wire ";
      shortStringOfID(view(), id, buf);
      buf << " = ";
      shortStringOfID(view(), args[0], buf);
      for (int i = 1; i != n; ++i) {
        buf << " & ";
        shortStringOfID(view(), args[i], buf);
      }
      buf << ";\n";
      break;
    case Or:
      assert(n>0);
      buf << "  wire ";
      shortStringOfID(view(), id, buf);
      buf << " = ";
      shortStringOfID(view(), args[0], buf);
      for (int i = 1; i != n; ++i) {
        buf << " | ";
        shortStringOfID(view(), args[i], buf);
      }
      buf << ";\n";
      break;
    case Equiv:
      assert(n == 2);
      buf << "  wire ";
      shortStringOfID(view(), id, buf);
      buf << " = ";
      shortStringOfID(view(), args[0], buf);
      buf << " == ";
      shortStringOfID(view(), args[1], buf);
      buf << ";\n";
      break;
    case ITE:
      assert(n == 3);
      buf << "  wire ";
      shortStringOfID(view(), id, buf);
      buf << " = ";
      shortStringOfID(view(), args[0], buf);
      buf << " ? ";
      shortStringOfID(view(), args[1], buf);
      buf << " : ";
      shortStringOfID(view(), args[2], buf);
      buf << ";\n";
      break;
    default:
      assert(false);
    }
    return id;
  }
  string out() {
    return buf.str();
  }
private:
  ostringstream buf;
};

string verilogOf(Manager::View & v, ID id) {
  vlg_folder vf(v);
  v.fold(vf, id);
  return vf.out();
}

string verilogOf(Manager::View & v, std::vector<ID> & ids) {
  vlg_folder vf(v);
  v.fold(vf, ids);
  return vf.out();
}

/**
 * Class for blif-MV folding.
 */
class bmv_folder : public Manager::View::Folder {
public:
  /**
   * Constructor.
   */
  bmv_folder(Manager::View & v) : Manager::View::Folder(v), buf() {}
  /**
   * Build .names for an expression node.
   */
  ID fold(ID id, int n, const ID * const args) {
    vector<bool> phase(n,false);
    Op op = view().op(id);
    switch(op) {
    case True:
      buf << ".names ";
      shortStringOfID(view(), id, buf);
      buf << "\n1\n";
      break;
    case Var:
      break;
    case Not:
      break;
    case And:
      assert(n>0);
      buf << ".names ";
      for (int i = 0; i != n; ++i) {
        phase[i] = inputWithPhase(args[i]);
      }
      shortStringOfID(view(), id, buf);
      buf << "\n.def 0\n";
      for (int i = 0; i != n; ++i) {
        buf << (phase[i] ? "1 " : "0 ");
      }
      buf << "1\n";
      break;
    case Or:
      assert(n>0);
      buf << ".names ";
      for (int i = 0; i != n; ++i) {
        phase[i] = inputWithPhase(args[i]);
      }
      shortStringOfID(view(), id, buf);
      buf << "\n.def 1\n";
      for (int i = 0; i != n; ++i) {
        buf << (phase[i] ? "0 " : "1 ");
      }
      buf << "0\n";
      break;
    case Equiv:
      assert(n == 2);
      buf << ".names ";
      phase[0] = inputWithPhase(args[0]);
      phase[1] = inputWithPhase(args[1]);
      shortStringOfID(view(), id, buf);
      buf << "\n.def 0\n";
      if (phase[0] == phase[1])
        buf << "1 1 1\n0 0 1\n";
      else
        buf << "1 0 1\n0 1 1\n";
      break;
    case ITE:
      assert(n == 3);
      buf << ".names ";
      phase[0] = inputWithPhase(args[0]);
      if (phase[0]) {
        phase[1] = inputWithPhase(args[1]);
        phase[2] = inputWithPhase(args[2]);
      } else {
        phase[1] = inputWithPhase(args[2]);
        phase[2] = inputWithPhase(args[1]);
      }
      shortStringOfID(view(), id, buf);
      buf << "\n.def 0\n";
      buf << "1 " << (phase[1] ? "1 " : "0 ") << "- 1\n";
      buf << "0 - " << (phase[2] ? "1 " : "0 ") << "1\n";
      break;
    default:
      assert(false);
    }
    return id;
  }
  string out() {
    return buf.str();
  }
private:
  bool inputWithPhase(const ID id)
  {
    ostringstream wbuf;
    shortStringOfID(view(), id, wbuf);
    string name = wbuf.str();
    bool phase = name[0] != '!';
    if (phase)
      buf << name;
    else
      buf << name.substr(1,name.size()-1);
    buf << " ";
    return phase;
  }
  ostringstream buf;
};

string blifMvOf(Manager::View & v, ID id) {
  bmv_folder bmvf(v);
  v.fold(bmvf, id);
  return bmvf.out();
}

string blifMvOf(Manager::View & v, std::vector<ID> & ids) {
  bmv_folder bmvf(v);
  v.fold(bmvf, ids);
  return bmvf.out();
}

/**
 * Class for AIGER folding.
 */
class aiger_folder : public Manager::View::Folder {
public:
  /**
   * Constructor.
   */
  aiger_folder(Manager::View & v, aiger * a) : Manager::View::Folder(v), aig(a) {}
  /**
   * Build AIGER nodes for an expression node.
   */
  ID fold(ID id, int n, const ID * const args) {
    Op op = view().op(id);
    switch(op) {
    case True:
    case Var:
    case Not:
      break;
    case And:
      assert(n==2);
      aiger_add_and(aig, AIGERlit(id), AIGERlit(args[0]), AIGERlit(args[1]));
      break;
    default:
      assert(false);
    }
    return id;
  }
private:
  aiger *aig;
};

void AIGEROf(Manager::View & v, std::vector<ID> & ids, aiger * aig) {
  aiger_folder af(v, aig);
  v.fold(af, ids);
}

}
