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

#include "AIGER.h"
#include "Expr.h"
#include "ExprAttachment.h"
#include "ExprUtil.h"

#include <sstream>
#include <unordered_map>
#include <vector>

extern "C" {
#include "aiger19.h"
}

using namespace std;

namespace {

  ID var(Expr::Manager::View * v, 
         const aiger_symbol * syms, unsigned int i, 
         const char prefix) 
  {
    const aiger_symbol & sym = syms[i];
    string nm;
    if (sym.name) 
      nm = sym.name;
    else {
      stringstream ss;
      ss << prefix << i;
      nm = ss.str();
    }
    return v->newVar(nm);
  }

  ID idOf(Expr::Manager::View * v, const vector<ID> & ids, unsigned int l) {
    ID lid = ids[l>>1];
    if (aiger_sign(l)) lid = v->apply(Expr::Not, lid);
    return lid;
  }

}

namespace Parser {

  void parseAIGER(const string & fn, Model & model) throw(InputError) {
    aiger * aig = aiger_init();
    aiger_open_and_read_from_file(aig, fn.c_str());
    const char * err = aiger_error(aig);
    if (err) {
      cout << err << endl;
      throw InputError(err);
    }
    if (!aiger_is_reencoded(aig))
      aiger_reencode(aig);

    model.setName(fn);
    Expr::Manager::View * v = model.newView();
    ExprAttachment * eat = (ExprAttachment *) model.attachment(Key::EXPR);
    vector<ID> ids(1+aig->num_inputs+aig->num_latches+aig->num_outputs+aig->num_ands, 
                   v->bfalse());

    size_t offset = 1;
    for (size_t i = 0; i < aig->num_inputs; ++i) {
      ids[i+offset] = var(v, aig->inputs, i, 'i');
      eat->addInput(ids[i+offset]);
    }
    offset += aig->num_inputs;
    for (size_t i = 0; i < aig->num_latches; ++i)
      ids[i+offset] = var(v, aig->latches, i, 'l');
    offset += aig->num_latches;
    for (size_t i = 0; i < aig->num_outputs; ++i)
      ids[i+offset] = var(v, aig->outputs, i, 'o');

    for (size_t i = 0; i < aig->num_ands; ++i) {
      const aiger_and * aa = aig->ands + i;
      ID arg0 = idOf(v, ids, aa->rhs0), arg1 = idOf(v, ids, aa->rhs1);
      ids[aa->lhs>>1] = v->apply(Expr::And, arg0, arg1);
    }

    vector<ID> init;
    for (size_t i = 0; i < aig->num_latches; ++i) {
      ID l = ids[aig->latches[i].lit>>1];
      unsigned int r = aig->latches[i].reset;
      if (r == 1)
        init.push_back(l);
      else if (r == 0)
        init.push_back(v->apply(Expr::Not, l));
      ID nid = idOf(v, ids, aig->latches[i].next);
      eat->setNextStateFn(l, nid);
    }
    eat->addInitialConditions(init);

    for (size_t i = 0; i < aig->num_constraints; ++i) {
      ID vnm = var(v, aig->constraints, i, 'c');
      ID cid = idOf(v, ids, aig->constraints[i].lit);
      eat->addConstraint(vnm, cid);
    }
    for (size_t i = 0; i < aig->num_outputs; ++i) {
      ID vnm = var(v, aig->outputs, i, 'o');
      ID oid = idOf(v, ids, aig->outputs[i].lit);
      eat->setOutputFn(vnm, oid);
    }
    for (size_t i = 0; i < aig->num_bad; ++i) {
      ID vnm = var(v, aig->bad, i, 'b');
      ID bid = idOf(v, ids, aig->bad[i].lit);
      eat->setBadFn(vnm, bid);
    }
    for (size_t i = 0; i < aig->num_fairness; ++i) {
      ID vnm = var(v, aig->fairness, i, 'f');
      ID fid = idOf(v, ids, aig->fairness[i].lit);
      eat->setFairnessFn(vnm, fid);
    }
    for (size_t i = 0; i < aig->num_justice; ++i) {
      ID vnm = var(v, aig->justice, i, 'j');
      const aiger_symbol & sym = aig->justice[i];
      vector<ID> just;
      for (size_t j = 0; j < sym.size; ++j)
        just.push_back(idOf(v, ids, sym.lits[j]));
      eat->setJusticeSet(vnm, just);
    }

    model.release(eat);
    delete v;
    aiger_reset(aig);
  }

}
