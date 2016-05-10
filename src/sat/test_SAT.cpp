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

#include "Expr.h"
#include "ExprUtil.h"

#include "SAT.h"

#include <assert.h>

using namespace std;

int main(int argc, const char * argv[]) {
  Expr::Manager * man = new Expr::Manager();
  Expr::Manager::View * v = man->newView();

  SAT::Clause ca, cb, cc;
  ID a = v->newVar("a");
  ID b = v->newVar("b");
  ID c = v->newVar("c");

  ca.push_back(a);
  ca.push_back(v->apply(Expr::Not, b));

  cb.push_back(b);
  cb.push_back(v->apply(Expr::Not, c));

  cc.push_back(c);

  SAT::Manager * sman = new SAT::Manager(*man);
  SAT::Manager::View * sview = sman->newView(*v);

  // global constraints on globally visible variables
  sman->add(ca);
  sman->add(cb);
  sman->add(cc);

  Expr::IDVector assumps;
  assumps.push_back(v->apply(Expr::Not, a));
  assumps.push_back(v->apply(Expr::Not, b));

  // only care about values for these variables
  SAT::Assignment asgn;
  asgn.insert(SAT::Assignment::value_type(a, SAT::Unknown));
  asgn.insert(SAT::Assignment::value_type(b, SAT::Unknown));
  asgn.insert(SAT::Assignment::value_type(c, SAT::Unknown));

  // assumps is shrunk to a core of lits
  bool rv = sview->sat(&assumps, NULL, &assumps);
  assert (!rv);
  cout << rv << " " << assumps.size() << endl;

  // which should be sufficient to still yield unsat
  rv = sview->sat(&assumps, NULL, &assumps);
  assert (!rv);
  cout << rv << " " << assumps.size() << endl;

  // but w/o the assumps, it's sat
  rv = sview->sat(NULL, &asgn, NULL);
  assert (rv);
  cout << rv << endl;
  for (SAT::Assignment::iterator it = asgn.begin(); it != asgn.end(); it++) {
    assert (it->second == SAT::True);
    cout << stringOf(*v, it->first) << " " << it->second << endl;
  }

  delete sview;
  delete sman;

  delete v;
  delete man;
}
