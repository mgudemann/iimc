/********************************************************************
Copyright (c) 2010-2013, Regents of the University of Colorado

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

#include "ISOP.h"
#include "TreeTruthTable.h"
#include "BitTruthTable.h"
#include<vector>
#include<iostream>

template<typename TT>
void simpleTest()
{
  std::vector<TT> vars(2);
  TT t;
  TT f;
  TT::variables(vars.begin(), vars.end(), t, f);

  TT a = vars[0] & vars[1];

  CNF::Cover c(CNF::isop(vars.begin(), vars.end(), a, t, f));

  std::cout << c << std::endl;

  assert(c.size() == 1);
}

template<typename TT>
void test()
{
  std::vector<TT> vars(10);
  TT t;
  TT f;
  TT::variables(vars.begin(), vars.end(), t, f);

  // define our function
  TT a = vars[0] & vars[1];
  TT b = vars[1] | ~vars[2];
  TT c = vars[0] & vars[3];
  TT d = ~vars[4] | vars[5];
  TT e = vars[6] & vars[7];
  TT g = vars[8] | ~vars[9];
  TT h = a & ~b;
  TT i = ~c | ~d;
  TT j = d & e;
  TT k = ~j | g;
  TT l = i | j;
  TT m = h & l;
  TT n = k | ~m;

  std::cout << "l:" << l << std::endl;

  std::cout << CNF::isop_cost(vars.begin(), vars.end(), l, t, f).first << std::endl;
}

int main()
{
  std::cout << "TreeTruthTable simple test" << std::endl;
  simpleTest<TruthTable::TreeTruthTable>();
  std::cout << "BitTruthTable simple test" << std::endl;
  simpleTest<TruthTable::BitTruthTable>();
  std::cout << "TreeTruthTable full test" << std::endl;
  test<TruthTable::TreeTruthTable>();
  std::cout << "BitTruthTable full test" << std::endl;
  test<TruthTable::BitTruthTable>();
  return 0;
}
