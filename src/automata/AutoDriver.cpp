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

#include <sstream>
#include "AutoWrapper.h"

using namespace std;
using namespace Expr;

auto_driver::auto_driver(ExprAttachment *eat)
  : trace_scanning(false),
    trace_parsing(false), eat(eat)
{
  ev = eat->model().newView();
}

auto_driver::~auto_driver() { delete ev; }

int
auto_driver::parse(const string &f)
{
  file = f;
  scan_begin();
  autoparser::auto_parser parser(*this);
  parser.set_debug_level(trace_parsing);
  int res = parser.parse();
  scan_end();
  if (res != 0)
    eat->clearAutomata();
  return res;
}

void
auto_driver::error(const autoparser::location& l, const string& m)
{
  cerr << l << ": " << m << endl;
}

void
auto_driver::error(const string& m)
{
  cerr << m << endl;
}

string auto_driver::toString(size_t index) const
{
  const vector<Automaton>& automata = eat->automata();
  assert(index < automata.size());
  Automaton aut = automata[index];
  ostringstream oss;
  oss << "Automaton has " << aut.states.size() << " states:" << endl;
  for(vector<Automaton::State>::const_iterator it = aut.states.begin();
      it != aut.states.end(); ++it) {
    oss << *it;
    if(it != aut.states.end() - 1)
      oss << ", ";
  }
  oss << endl;
  oss << "Initial States:" << endl;
  for(vector<Automaton::State>::const_iterator it = aut.initialStates.begin();
      it != aut.initialStates.end(); ++it) {
    oss << *it;
    if(it != aut.initialStates.end() - 1)
      oss << ", ";
  }
  oss << endl;
  oss << "Bad States:" << endl;
  for(vector<Automaton::State>::const_iterator it = aut.badStates.begin();
      it != aut.badStates.end(); ++it) {
    oss << *it;
    if(it != aut.badStates.end() - 1)
      oss << ", ";
  }
  oss << endl;
  oss << "Transitions:" << endl;
  for(vector<Automaton::Transition>::const_iterator it = aut.transitions.begin();
      it != aut.transitions.end(); ++it) {
    oss << it->source << " -> " << it->destination << " on "
        << stringOf(*ev, it->label) << endl;;
  }
  return oss.str();
}

string auto_driver::toDot(size_t index) const
{
  const vector<Automaton>& automata = eat->automata();
  assert(index < automata.size());
  Automaton aut = automata[index];
  set<Automaton::State> bad(aut.badStates.begin(), aut.badStates.end());
  ostringstream oss;
  oss << "digraph automaton {" << endl;
  for(vector<Automaton::State>::const_iterator it = aut.states.begin();
      it != aut.states.end(); ++it) {
    oss << *it;
    if(bad.find(*it) != bad.end())
      oss << "[peripheries=2]";
    oss << ";" << endl;
  }
  for(vector<Automaton::State>::const_iterator it = aut.initialStates.begin();
      it != aut.initialStates.end(); ++it) {
    oss << "inv" << *it << " [style=\"invis\"];" << endl;
    oss << "inv" << *it << " -> " << *it << ";" << endl;;
  }
  for(vector<Automaton::Transition>::const_iterator it = aut.transitions.begin();
      it != aut.transitions.end(); ++it) {
    oss << it->source << " -> " << it->destination << " [ label=\" ";
    shortStringOfID(*ev, it->label, oss);
    oss << "\" ];" << endl;;
  }
  oss << "}" << endl;

  return oss.str();
}
