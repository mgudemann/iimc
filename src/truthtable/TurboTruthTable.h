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

#ifndef TURBOTRUTHTABLE_H
#define TURBOTRUTHTABLE_H

#include<vector>
#include<iterator>
#include<climits>
#include<sstream>
#include<iomanip>
#include<cassert>
#include "BitTricks.h"

namespace TruthTable
{

  struct TurboTruthTable
  {
    unsigned long index;

    TurboTruthTable() : index(0) { }
    TurboTruthTable(const unsigned long i) : index(i) { }
    TurboTruthTable(const TurboTruthTable& other) : index(other.index) { }
    TurboTruthTable& operator=(const TurboTruthTable& other)
    { index = other.index; return *this; }
  };

  template<typename ForwardIterator>
  struct MapAssignFun
  {
    void operator()(ForwardIterator& i, TurboTruthTable v)
    {
      i->second = v;
    }
  };

  template<typename ForwardIterator>
  struct VecAssignFun
  {
    void operator()(ForwardIterator& i, TurboTruthTable v)
    {
      *i = v;
    }
  };

  class TurboTruthTableManager
  {
  private:
    unsigned long nvars;
    unsigned long nwords;
    ::std::vector<unsigned long> truthtables;

    template<typename ForwardIterator, typename AssignFun = MapAssignFun<ForwardIterator> >
    void initialize(const ForwardIterator& begin, const ForwardIterator& end)
    {
      AssignFun af;
      // count variables
      nvars = ::std::distance(begin, end);

      // compute number of words per variable
      nwords = (1UL<<nvars)/sizeof(unsigned long)/8UL;
      if(nwords == 0)
        nwords = 1;

      truthtables.resize(nvars*nwords);
      unsigned long varnum = 0;
      for(ForwardIterator i = begin; i != end; ++i,++varnum) {
        if(varnum < Util::pattern_count<unsigned long>()) {
          // detail can be contained in a single word
          for(unsigned long j = 0; j < nwords; ++j) {
            truthtables[varnum*nwords+j] = Util::pattern<unsigned long>(varnum);
          }
        } else {
          // detail overflows single word
          unsigned long wordval = ~(0UL);
          unsigned long skipamt = 1<<(varnum - Util::pattern_count<unsigned long>());
          for(unsigned long j = 0; j < nwords; ++j) {
            if(j % skipamt == 0)
              wordval = ~wordval;
            truthtables[varnum*nwords+j] = wordval;
          }
        }
        af(i, varnum*nwords);
      }
    }

    inline unsigned long push()
    {
      unsigned long res = truthtables.size();
      truthtables.resize(res+nwords);
      return res;
    }

    inline void pop(unsigned long i = 1)
    {
      assert(truthtables.size() >= i*nwords);
      truthtables.resize(truthtables.size()-i*nwords);
    }

    inline void copy(unsigned long to, unsigned long from)
    {
      for(unsigned long i = to, j = from; i < to+nwords; ++i,++j) {
        truthtables[i] = truthtables[j];
      }
    }

    inline void conjoin(unsigned long to, unsigned long from)
    {
      for(unsigned long i = to, j = from; i < to+nwords; ++i,++j) {
        truthtables[i] &= truthtables[j];
      }
    }

    inline void conjoin_variable(unsigned long to, long svar)
    {
      unsigned long varnum = ::std::abs(svar)-1;
      bool invert = svar < 0;

      if(varnum < Util::pattern_count<unsigned long>()) {
        // detail can be contained in a single word
        if(invert) {
          for(unsigned long j = 0; j < nwords; ++j) {
            truthtables[to+j] &= Util::ipattern<unsigned long>(varnum);
          }
        } else {
          for(unsigned long j = 0; j < nwords; ++j) {
            truthtables[to+j] &= Util::pattern<unsigned long>(varnum);
          }
        }
      } else {
        // detail overflows single word
        unsigned long wordval = invert ? 0 : ~(0UL);
        unsigned long skipamt = 1<<(varnum - Util::pattern_count<unsigned long>());
        for(unsigned long j = 0; j < nwords; ++j) {
          if(j % skipamt == 0)
            wordval = ~wordval;
          truthtables[to+j] &= wordval;
        }
      }
    }

    inline void disjoin(unsigned long to, unsigned long from)
    {
      for(unsigned long i = to, j = from; i < to+nwords; ++i,++j) {
        truthtables[i] |= truthtables[j];
      }
    }

    inline void conjoin_negate(unsigned long to, unsigned long from)
    {
      for(unsigned long i = to, j = from; i < to+nwords; ++i,++j) {
        truthtables[i] &= ~truthtables[j];
      }
    }

    inline void disjoin_conjoin_negate(unsigned long to, unsigned long neg1, unsigned long pos2, unsigned long neg2)
    {
      for(unsigned long i = to, j = neg1, k = pos2, l = neg2; i < to+nwords; ++i,++j,++k,++l) {
        truthtables[i] &= ~truthtables[j];
        truthtables[i] |= (truthtables[k] & ~truthtables[l]);
      }
    }

    void isop_internal(unsigned long varnum, unsigned long l, unsigned long u, unsigned long fun, ::std::vector< ::std::vector<long> >& result)
    {
      // bad style to improve short circuit behavior

      // checks to see if l is false (short circuiting)
      for(unsigned long i = l; i < l+nwords; ++i) {
        if(truthtables[i] != 0UL)
          goto check_true;
      }
      for(unsigned long i = fun; i < fun+nwords; ++i) {
        truthtables[i] = 0UL;
      }
      return;

    check_true:
      // checks to see if u is true (short circuiting)
      for(unsigned long i = u; i < u+nwords; ++i) {
        if(truthtables[i] != ~0UL)
          goto do_cofactor;
      }
      for(unsigned long i = fun; i < fun+nwords; ++i) {
        truthtables[i] = ~0UL;
      }
      result.push_back(::std::vector<long>());
      return;


    do_cofactor:
      // cofactor and get variable cofactored starting with varnum

      // variables for cofactors of l and u
      unsigned long l0 = push();
      unsigned long l1 = push();
      unsigned long u0 = push();
      unsigned long u1 = push();

      // increment varnum until we find a valid cofactoring
      for(; varnum < nvars; ++varnum) {

        // if varnum details are contained within a single word
        if(varnum < Util::pattern_count<unsigned long>()) {
          // cofactor within single words

          // compute shift for cofactor
          unsigned long shiftamt = 1 << varnum;
          // keep a flag of whether the cofactoring yielded different results
          bool success = false;

          for(unsigned long i = 0; i < nwords; ++i) {
            // use pointers to prevent repeated lookup into vector
            unsigned long* tl = &(truthtables[l+i]);
            unsigned long* tu = &(truthtables[u+i]);
            unsigned long* tl0 = &(truthtables[l0+i]);
            unsigned long* tl1 = &(truthtables[l1+i]);
            unsigned long* tu0 = &(truthtables[u0+i]);
            unsigned long* tu1 = &(truthtables[u1+i]);
            // prefetch the patterns
            unsigned long ipat = Util::ipattern<unsigned long>(varnum);
            unsigned long pat = Util::pattern<unsigned long>(varnum);

            // negative cofactor l
            *tl0 = ipat & *tl;
            *tl0 |= *tl0 << shiftamt;
            // positive cofactor l
            *tl1 = pat & *tl;
            *tl1 |= *tl1 >> shiftamt;

            // negative cofactor u
            *tu0 = ipat & *tu;
            *tu0 |= *tu0 << shiftamt;
            // positive cofactor u
            *tu1 = pat & *tu;
            *tu1 |= *tu1 >> shiftamt;

            // if one of the cofactors is different than the original function, success
            if(success || *tl0 != *tl || *tl1 != *tl || *tu0 != *tu || *tu1 != *tu)
              success = true;
          }

          // if we successfully cofactored, start the recursion
          if(success)
            goto do_recursion;

          // if not, try cofactoring by the next variable

        } else {
          //cofactor between multiple words

          // compute the number of words to shift by
          unsigned long shiftwords = 1 << (varnum - Util::pattern_count<unsigned long>());

          // keep track of if we have found a valid cofactoring
          bool success = false;

          // for each pair of shiftwords
          for(unsigned long i = 0; i < nwords; i += 2*shiftwords) {
            // iterate through the shiftword
            for(unsigned long j = 0; j < shiftwords; ++j) {
              // low index is just the two bases added
              unsigned long lowindex = i+j;
              // high index adds in shiftwords to get to the high element in the pair
              unsigned long highindex = lowindex+shiftwords;

              // copy low index to both indices for negative cofactor
              truthtables[l0+lowindex] = truthtables[l0+highindex] = truthtables[l+lowindex];
              truthtables[u0+lowindex] = truthtables[u0+highindex] = truthtables[u+lowindex];
              // copy high index to both indices for positive cofactor
              truthtables[l1+lowindex] = truthtables[l1+highindex] = truthtables[l+highindex];
              truthtables[u1+lowindex] = truthtables[u1+highindex] = truthtables[u+highindex];
              
              // if the high index of a negative cofactor is different from the high index of the
              // original, success.
              // if the low index of a positive cofactor is different from the low index of the
              // original, success.
              if(success || truthtables[l0+highindex] != truthtables[l+highindex] ||
                  truthtables[u0+highindex] != truthtables[u+highindex] ||
                  truthtables[l1+lowindex] != truthtables[l+lowindex] ||
                  truthtables[u1+lowindex] != truthtables[u+lowindex])
                success = true;
            }
          }

          // if we successfully cofactored, start the recursion
          if(success)
            goto do_recursion;
        }
      }
      // didn't find a cofactor
      assert(false);
    do_recursion:
      // compute derivative functions and recurse
      // varnum contains the variable we cofactored by
      // svar contains the signed version of the variable
      long svar = static_cast<long>(varnum) + 1;

      // save where c0 recursion started inserting
      unsigned long c0_start = result.size();
      // compute new l
      unsigned long newl = push();
      copy(newl, l0);
      conjoin_negate(newl, u1);
      // recurse computing c0
      isop_internal(varnum+1, newl, u0, fun, result);
      // for each added entry in result, add negative (varnum+1) to each clause
      for(; c0_start < result.size(); ++c0_start) {
        result[c0_start].push_back(-svar);
      }

      // save where c1 recursion started inserting
      unsigned long c1_start = result.size();
      // a function for the 
      unsigned long c1f = push();
      // compute new l
      copy(newl, l1);
      conjoin_negate(newl, u0);
      // recurse computing c1
      isop_internal(varnum+1, newl, u1, c1f, result);
      // for each added entry in result, add positive (varnum+1) to each clause
      for(; c1_start < result.size(); ++c1_start) {
        result[c1_start].push_back(svar);
      }

      // compute lnew for third isop
      disjoin_conjoin_negate(l0, fun, l1, c1f);

      // construct function from c0f, and c1f
      // and resulting fun with negative (varnum+1)
      conjoin_variable(fun, -svar);
      // and resulting fun with positive (varnum+1)
      conjoin_variable(c1f, svar);
      // or the result of c1f into fun
      disjoin(fun, c1f);

      // compute the u for third recursion
      conjoin(u0, u1);

      // recurse computing c*
      isop_internal(varnum+1, l0, u0, c1f, result);

      // add the result function of the third isop recursion to the function
      disjoin(fun, c1f);

      // finsihed clean up 6 variables:
      //   c1f, newl, l0, l1, u0, u1
      pop(6);
    }

  public:
    TurboTruthTableManager() { }

#if 0
    template<typename ForwardIterator, typename AssignFun = MapAssignFun<ForwardIterator> >
    void reset(ForwardIterator& begin, ForwardIterator& end)
    { initialize<ForwardIterator,AssignFun>(begin, end); }
#endif

    template<typename ForwardIterator, typename AssignFun = MapAssignFun<ForwardIterator> >
    void reset(const ForwardIterator& begin, const ForwardIterator& end)
    { initialize<ForwardIterator,AssignFun>(begin, end); }

    void conjoin(TurboTruthTable& lhs, const TurboTruthTable& rhs)
    {
      for(unsigned long i = lhs.index, j = rhs.index; i < lhs.index+nwords; ++i,++j) {
        truthtables[i] &= truthtables[j];
      }
    }

    void disjoin(TurboTruthTable& lhs, const TurboTruthTable& rhs)
    {
      for(unsigned long i = lhs.index, j = rhs.index; i < lhs.index+nwords; ++i,++j) {
        truthtables[i] |= truthtables[j];
      }
    }

    void negate(TurboTruthTable& v)
    {
      for(unsigned long i = v.index; i < v.index+nwords; ++i) {
        truthtables[i] = ~truthtables[i];
      }
    }

    void makefalse(TurboTruthTable& v)
    {
      for(unsigned long i = v.index; i < v.index+nwords; ++i) {
        truthtables[i] = 0;
      }
    }

    void copy(TurboTruthTable& to, const TurboTruthTable& from)
    {
      to.index = push();
      copy(to.index, from.index);
    }

    ::std::string toString(TurboTruthTable v)
    {
      ::std::stringstream ss;
      ss << "0x" << ::std::hex;

      const unsigned long width = sizeof(unsigned long)*8/4;

      for(unsigned long i = nwords; i > 0; --i) {
        ss.fill('0');
        ss.width(width);
        ss << truthtables[v.index+i-1];
      }
      return ss.str();
    }

    void isop(TurboTruthTable& f, ::std::vector< ::std::vector<long> >& cover)
    {
#ifndef NDEBUG
      unsigned long size = truthtables.size();
#endif
      unsigned long tmp = push();
      isop_internal(0, f.index, f.index, tmp, cover);
      pop();
      assert(size == truthtables.size());
    }

    unsigned long size() const
    {
      return truthtables.size();
    }
  };

} // namespace TruthTable

#endif
