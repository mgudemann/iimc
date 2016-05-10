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

#include "TreeTruthTable.h"
#include "BitTruthTable.h"
#include<vector>
#include<string>
#include<map>
#include<unordered_map>

template<typename TT>
void test_vector() {
  std::vector<TT> vars(5);
  TT t;
  TT f;

  TT::variables(vars.begin(), vars.end(), t, f);

  TT a = vars[0];
  TT b = vars[1];

  assert((a & (b & ~a)) == f);
  assert((a & (~a)) == f);
  assert((a | (~a)) == t);
  assert((b & (~b)) == f);
  assert((b | (~b)) == t);
  assert(b.negCofactor(b) == f);
  assert(b.posCofactor(b) == t);
  assert(a.negCofactor(a) == f);
  assert(a.posCofactor(a) == t);

  TT c = a & b;
  assert(c.posCofactor(a) == b);

  TT c1 = a | b;
  assert(c1.negCofactor(a) == b);

  TT d = a & b & ~(vars[2] | vars[3]);
  TT e = d.posCofactor(a);
  
  assert(TT::firstVar(vars.begin(), vars.end(), e,e) == (vars.begin()+1));
}

template<typename TT>
void test_map() {
  std::map<std::string, TT> vars;
  vars["hello"] = TT();
  vars["yo"] = TT();
  TT t;
  TT f;
  TT::variables_map(vars.begin(), vars.end(), t, f);

  TT hello = vars["hello"];
  TT yo = vars["yo"];

  assert((hello & (~hello)) == f);
  assert((hello | (~hello)) == t);
  assert((yo & (~yo)) == f);
  assert((yo | (~yo)) == t);

  TT c = yo & yo;
  assert(TT::firstVar_map(vars.begin(), vars.end(), c, c) == vars.find("yo"));
}

template <typename TT>
void hash_test() {
  std::unordered_map<TT, int> m;
  std::vector<TT> v(1);
  TT t;
  TT f;
  TT::variables(v.begin(), v.end(), t, f);

  m[t] = 0;
  m[f] = 1;
  m[v[0]] = 2;

  assert(m[t] == 0);
  assert(m[f] == 1);
  assert(m[v[0]] == 2);

  m[~f] = 13;
  m[~t] = 7;
  assert(m[t] == 13);
  assert(m[f] == 7);
}

template<typename TT>
void short_test() {
  std::vector<TT> vars(2);
  TT t;
  TT f;

  TT::variables(vars.begin(), vars.end(), t, f);

  TT a = vars[0];
  TT b = vars[1];

  assert((a & (~a)) == f);
  assert((a | (~a)) == t);
  assert((b & (~b)) == f);
  assert((b | (~b)) == t);
  assert(b.negCofactor(b) == f);
  assert(b.posCofactor(b) == t);
  assert(a.negCofactor(a) == f);
  assert(a.posCofactor(a) == t);

  TT c = a & b;
  assert(c.posCofactor(a) == b);

  TT c1 = a | b;
  assert(c1.negCofactor(a) == b);

  std::pair<TT,TT> p = c.cofactors(a);
  assert(p.second == b);
  assert(p.first == f);
}

template<typename TT>
void tt_test5s()
{
  std::vector<TT> vars(7);
  TT t;
  TT f;

  TT::variables(vars.begin(), vars.end(), t, f);
  TT a = vars[0];
  TT b = vars[1];
  TT c = vars[2];

  TT t1 = ~a | c;
  //std::cout << t1 << std::endl;
  //std::cout << t1.posCofactor(a) << std::endl;
  //std::cout << t1.negCofactor(a) << std::endl;
  assert(t1.posCofactor(a) == c);
  assert(t1.negCofactor(a) == t);
}

template<typename TT>
void tt_test_overflow()
{
  std::vector<TT> vars(7);
  TT t;
  TT f;

  TT::variables(vars.begin(), vars.end(), t, f);
  TT a = vars[6];
  TT b = vars[5];
  TT c = vars[4];

  TT t1 = ~a | c;
  //std::cout << t1 << std::endl;
  //std::cout << t1.posCofactor(a) << std::endl;
  //std::cout << t1.negCofactor(a) << std::endl;
  assert(t1.posCofactor(a) == c);
  assert(t1.negCofactor(a) == t);
}

template<typename TT>
void tt_test_varCount()
{
  std::vector<TT> vars(3);
  TT t;
  TT f;

  TT::variables(vars.begin(), vars.end(), t, f);
  TT a = vars[0];
  TT b = vars[1];
  TT c = vars[2];

  TT t1 = (~a & b) | (a & ~b);
  assert(t1.varCount() == 2);
}


int main()
{
  //std::cout << "Tree Vector" << std::endl;
  test_vector<TruthTable::TreeTruthTable>();
  //std::cout << "Tree Map" << std::endl;
  test_map<TruthTable::TreeTruthTable>();
  //std::cout << "Bit Vector" << std::endl;
  test_vector<TruthTable::BitTruthTable>();
  //std::cout << "Short Bit Vector" << std::endl;
  short_test<TruthTable::BitTruthTable>();
  //std::cout << "Bit Map" << std::endl;
  test_map<TruthTable::BitTruthTable>();
  //std::cout << "5s test bit map" << std::endl;
  tt_test5s<TruthTable::BitTruthTable>();
  //std::cout << "overflow test bit map" << std::endl;
  tt_test_overflow<TruthTable::BitTruthTable>();
  //std::cout << "Hash of Tree" << std::endl;
  hash_test<TruthTable::TreeTruthTable>();
  //std::cout << "Variable Count" << std::endl;
  tt_test_varCount<TruthTable::TreeTruthTable>();
  return 0;
}
