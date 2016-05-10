/* -*- C++ -*- */

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

#ifndef BITTRUTHTABLE_H
#define BITTRUTHTABLE_H
#include<vector>
#include<boost/operators.hpp>
#include<cassert>
#include<iostream>
#include<utility>
#include<functional>

/** @file BitTruthTable.h */

namespace TruthTable
{
  class BitTruthTable : ::boost::bitwise<BitTruthTable>, ::boost::equality_comparable<BitTruthTable> {
  private:
    std::vector<unsigned long> function;
  public:
    inline BitTruthTable& operator=(const BitTruthTable& rhs);
    inline BitTruthTable& negate();
    inline BitTruthTable operator~() const;
    inline BitTruthTable& operator&=(const BitTruthTable& rhs);
    inline BitTruthTable& operator|=(const BitTruthTable& rhs);
    inline BitTruthTable& operator^=(const BitTruthTable& rhs);
    inline bool operator==(const BitTruthTable& rhs) const;

    size_t hash() const;


    template <typename ForwardIterator>
    static ForwardIterator firstVar(const ForwardIterator& begin, const ForwardIterator& end, const BitTruthTable& a, const BitTruthTable b);

    template <typename MapIterator>
    static MapIterator firstVar_map(const MapIterator& begin, const MapIterator& end, const BitTruthTable& a, const BitTruthTable b);

    friend ::std::ostream& operator<<(::std::ostream& ostr, const BitTruthTable& tt);


    BitTruthTable posCofactor(const BitTruthTable& rhs) const;
    BitTruthTable negCofactor(const BitTruthTable& rhs) const;
    ::std::pair<BitTruthTable,BitTruthTable> cofactors(const BitTruthTable& rhs) const;

    BitTruthTable();
    BitTruthTable(const BitTruthTable& o);

  public:
    template <typename ForwardIterator>
    static void variables(const ForwardIterator& begin, const ForwardIterator& end, BitTruthTable& tprop, BitTruthTable& fprop);

    template <typename MapIterator>
    static void variables_map(const MapIterator& begin, const MapIterator& end, BitTruthTable& tprop, BitTruthTable& fprop);
  };


  // BitTruthTable Operators

  BitTruthTable& BitTruthTable::operator=(const BitTruthTable& rhs)
  {
    function = rhs.function;
    return *this;
  }

  BitTruthTable& BitTruthTable::negate()
  {
    unsigned size = function.size();
    for(unsigned i = 0; i < size; ++i) {
      function[i] = ~function[i];
    }
    return *this;
  }

  BitTruthTable BitTruthTable::operator~() const
  {
    BitTruthTable ret(*this);
    ret.negate();
    return ret;
  }

  BitTruthTable& BitTruthTable::operator&=(const BitTruthTable& rhs)
  {
    assert(function.size() == rhs.function.size());
    unsigned size = function.size();
    for(unsigned i = 0; i < size; ++i) {
      function[i] = function[i] & rhs.function[i];
    }
    return *this;
  }

  BitTruthTable& BitTruthTable::operator|=(const BitTruthTable& rhs)
  {
    assert(function.size() == rhs.function.size());
    unsigned size = function.size();
    for(unsigned i = 0; i < size; ++i) {
      function[i] = function[i] | rhs.function[i];
    }
    return *this;
  }

  BitTruthTable& BitTruthTable::operator^=(const BitTruthTable& rhs)
  {
    assert(function.size() == rhs.function.size());
    unsigned size = function.size();
    for(unsigned i = 0; i < size; ++i) {
      function[i] = function[i] ^ rhs.function[i];
    }
    return *this;
  }

  bool BitTruthTable::operator==(const BitTruthTable& rhs) const
  {
    assert(function.size() == rhs.function.size());
    unsigned size = function.size();
    for(unsigned i = 0; i < size; ++i) {
      if(function[i] != rhs.function[i])
        return false;
    }
    return true;
  }


  template <typename T>
  inline T max(T a, T b)
  {
    return a > b ? a : b;
  }

  namespace Private
  {
    unsigned long get_pattern(unsigned varn);
  }

  template <typename ForwardIterator>
  void BitTruthTable::variables(const ForwardIterator& begin, const ForwardIterator& end, BitTruthTable& tprop, BitTruthTable& fprop)
  {
    //count variables
    unsigned nvars = 0;
    for(ForwardIterator i = begin; i != end; ++i) {
      ++nvars;
    }

    // count the number of machine words needed to store truth table and number
    // of variables before exceeding a machine word
    unsigned varcutoff;
    switch(sizeof(unsigned long)) {
      case 2:
        //16 bits = 4 vars
        varcutoff = 4;
        break;
      case 4:
        varcutoff = 5;
        break;
      case 8:
        varcutoff = 6;
        break;
      case 16:
        varcutoff = 7;
        break;
      default:
        assert(false);
        break;
    }
    unsigned nwords = nvars < varcutoff ? 1 : (1 << (nvars - varcutoff));

    // generate true (all 1s)
    tprop.function.resize(nwords);
    for(unsigned i = 0; i < nwords; ++i) {
      tprop.function[i] = ~(unsigned long)(0);
    }
    // generate false (all 0s)
    fprop.function.resize(nwords);
    for(unsigned i = 0; i < nwords; ++i) {
      fprop.function[i] = (unsigned long)(0);
    }

    // fill in variables
    unsigned varn = 0;
    for(ForwardIterator i = begin; i != end; ++i) {
      i->function.resize(nwords);
      
      // if pattern is in less than a single word
      if(varn < varcutoff) {
        unsigned long pat = Private::get_pattern(varn);
        for(unsigned j = 0; j < nwords; ++j) {
          i->function[j] = pat;
        }
      } else {
        unsigned nblocks = 1 << (varn - varcutoff);
        //std::cout << "nblocks: " << nblocks << std::endl;
        unsigned long val = ~(0UL);
        for(unsigned j = 0; j < nwords; ++j) {
          if(j % nblocks == 0)
            val = ~val;
          i->function[j] = val;
          // if we've exhausted the number of blocks, change
        }
      }
      ++varn;
    }

  }

  template <typename MapIterator>
  void BitTruthTable::variables_map(const MapIterator& begin, const MapIterator& end, BitTruthTable& tprop, BitTruthTable& fprop)
  {
    //count variables
    unsigned nvars = 0;
    for(MapIterator i = begin; i != end; ++i) {
      ++nvars;
    }

    // count the number of machine words needed to store truth table and number
    // of variables before exceeding a machine word
    unsigned varcutoff;
    switch(sizeof(unsigned long)) {
      case 2:
        //16 bits = 4 vars
        varcutoff = 4;
        break;
      case 4:
        varcutoff = 5;
        break;
      case 8:
        varcutoff = 6;
        break;
      case 16:
        varcutoff = 7;
        break;
      default:
        assert(false);
        break;
    }
    unsigned nwords = nvars < varcutoff ? 1 : (1 << (nvars - varcutoff));

    // generate true (all 1s)
    tprop.function.resize(nwords);
    for(unsigned i = 0; i < nwords; ++i) {
      tprop.function[i] = ~(unsigned long)(0);
    }
    // generate false (all 0s)
    fprop.function.resize(nwords);
    for(unsigned i = 0; i < nwords; ++i) {
      fprop.function[i] = (unsigned long)(0);
    }

    // fill in variables
    unsigned varn = 0;
    for(MapIterator i = begin; i != end; ++i) {
      i->second.function.resize(nwords);
      
      // if pattern is in less than a single word
      if(varn < varcutoff) {
        unsigned long pat = Private::get_pattern(varn);
        for(unsigned j = 0; j < nwords; ++j) {
          i->second.function[j] = pat;
        }
      } else {
        unsigned nblocks = 1 << (varn - varcutoff);
        //std::cout << "nblocks: " << nblocks << std::endl;
        unsigned long val = ~(0UL);
        for(unsigned j = 0; j < nwords; ++j) {
          if(j % nblocks == 0)
            val = ~val;
          i->second.function[j] = val;
          // if we've exhausted the number of blocks, change
        }
      }
      ++varn;
    }
  }

  template <typename ForwardIterator>
  ForwardIterator BitTruthTable::firstVar(const ForwardIterator& begin, const ForwardIterator& end, const BitTruthTable& a, const BitTruthTable b)
  {
    //TODO: this is too expensive, I'm sure
    for(ForwardIterator i = begin; i != end; ++i) {
      if(a.posCofactor(*i) != a)
        return i;
      if(a.negCofactor(*i) != a)
        return i;
      if(b.posCofactor(*i) != b)
        return i;
      if(b.negCofactor(*i) != b)
        return i;
    }
    assert(false);
    return end;
  }

  template <typename MapIterator>
  MapIterator BitTruthTable::firstVar_map(const MapIterator& begin, const MapIterator& end, const BitTruthTable& a, const BitTruthTable b)
  {
    //TODO: this is too expensive, I'm sure
    for(MapIterator i = begin; i != end; ++i) {
      if(a.posCofactor(i->second) != a)
        return i;
      if(a.negCofactor(i->second) != a)
        return i;
      if(b.posCofactor(i->second) != b)
        return i;
      if(b.negCofactor(i->second) != b)
        return i;
    }
    assert(false);
    return end;
  }

} // end namespace TruthTable

namespace std
{
  template<>
  struct hash< ::TruthTable::BitTruthTable > : public std::unary_function< ::TruthTable::BitTruthTable, size_t>
  {
    size_t operator()(const ::TruthTable::BitTruthTable& tt) const
    {
      return tt.hash();
    }
  };
} // end namespace std

#endif
