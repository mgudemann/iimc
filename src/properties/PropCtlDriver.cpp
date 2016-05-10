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

#include <sstream>
#include "PropCtlWrapper.h"

using namespace std;
using namespace Expr;

ctl_driver::ctl_driver(ExprAttachment *eat)
  : trace_scanning(false),
    trace_parsing(false), eat(eat)
{
  ev = eat->model().newView();
}

ctl_driver::~ctl_driver() { delete ev; }

int
ctl_driver::parse(const string &f)
{
  file = f;
  scan_begin();
  yy::ctl_parser parser(*this);
  parser.set_debug_level(trace_parsing);
  int res = parser.parse();
  scan_end();
  if (res != 0)
    eat->clearCtlProperties();
  return res;
}

void
ctl_driver::error(const yy::location& l, const string& m)
{
  cerr << l << ": " << m << endl;
}

void
ctl_driver::error(const string& m)
{
  cerr << m << endl;
}

string ctl_driver::toString(size_t index) const
{
  const vector<ID>& properties = eat->ctlProperties();
  assert(index < properties.size());
  ID root = properties[index];
  return stringOf(*ev, root);
}

string ctl_driver::toDot(size_t index) const
{
  const vector<ID>& properties = eat->ctlProperties();
  assert(index < properties.size());
  ID root = properties[index];
  return dotOf(*ev, root);
}
