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

#include "DIMACS.h"
#include "Expr.h"

#include <sstream>
#include <fstream>
#include <cassert>

using namespace std;

namespace
{

/**
 * Skip as much as characters until meeting a newline character.
 */
void skip_until_newline(ifstream &ifs)
{
  ifs.ignore(256, '\n');
}

/**
 * Get the variable index of a literal.
 */
size_t lit2var(int lit)
{
  assert(lit != 0);
  return (lit > 0) ? lit : -lit;
}

/**
 * Test if the literal is complemented.
 */
bool is_not(int lit)
{
  assert(lit != 0);
  return (lit < 0);
}

} // namespace

namespace Parser
{

void parseDIMACS(const string &fn, Expr::Manager::View &v, SAT::Clauses &clauses) throw (InputError)
{
  // Check if input file is valid.
  ifstream ifs(fn.c_str());
  if (!ifs.good())
    throw InputError(string("Cannot open input file ") + fn.c_str() + ".");
  string p;
  ifs >> p;
  while (p == "c") { skip_until_newline(ifs); ifs >> p; }
  string f;
  ifs >> f;
  if (p != "p" || f != "cnf")
    throw InputError(string("Bad input format: ") + f + ".");
  // Number of variables and clauses.
  size_t nvar, ncla;
  ifs >> nvar >> ncla;
  skip_until_newline(ifs);
  // Initialize the clause counter.
  size_t cla_counter = 0;
  // Parse until the number of clauses parsed reaches "ncla".
  ostringstream ss;
  int lit;
  while (cla_counter < ncla) {
    SAT::Clause c;
    ifs >> lit;
    while (lit != 0) {
      ss << "V" << lit2var(lit);
      if (is_not(lit)) c.push_back(v.apply(Expr::Not, v.newVar(ss.str())));
      else c.push_back(v.newVar(ss.str()));
      ss.str("");
      ifs >> lit;
    }
    cla_counter++;
    clauses.push_back(c);
  }
}

} // namespace Parser
