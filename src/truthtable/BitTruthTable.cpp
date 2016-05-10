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

#include "BitTruthTable.h"
#include<climits>
#include<iomanip>

namespace TruthTable
{
  namespace Private
  {
    unsigned long get_pattern(unsigned varn)
    {
#if ULONG_MAX == 0xFFFFFFFF
      switch(varn) {
        case 0: return 0xAAAAAAAAUL;
        case 1: return 0xCCCCCCCCUL;
        case 2: return 0xF0F0F0F0UL;
        case 3: return 0xFF00FF00UL;
        case 4: return 0xFFFF0000UL;
        default:
          assert(false);
          return 0;
      }
#elif ULONG_MAX == 0xFFFFFFFFFFFFFFFF
      switch(varn) {
        case 0: return 0xAAAAAAAAAAAAAAAAUL;
        case 1: return 0xCCCCCCCCCCCCCCCCUL;
        case 2: return 0xF0F0F0F0F0F0F0F0UL;
        case 3: return 0xFF00FF00FF00FF00UL;
        case 4: return 0xFFFF0000FFFF0000UL;
        case 5: return 0xFFFFFFFF00000000UL;
        default:
          assert(false);
          return 0;
      }
#else
#  error Unsupported integer size
#endif
    }
  } // end namespace Private

  namespace {
    // horribly inefficent search for number of trailing zeros in a bit vector.
    unsigned trailing_zeros(const ::std::vector<unsigned long>& f)
    {
      unsigned count = 0;
      unsigned size = f.size();
      unsigned i = 0;
      for(; i < size; ++i) {
        if(f[i] != 0)
          break;
        count += sizeof(unsigned long)*8;
      }
      assert(i != size);

      if(f[i] & 1)
        return count;

      unsigned long v = f[0];
      unsigned c = 1;
#if ULONG_MAX == 0xFFFFFFFFFFFFFFFF
      // 64 bit only
      if((v & 0xFFFFFFFF) == 0) {
        v >>= 32;
        c += 32;
      }
#endif
      if((v & 0xFFFF) == 0) {
        v >>= 16;
        c += 16;
      }
      if((v & 0xFF) == 0) {
        v >>= 8;
        c += 8;
      }
      if((v & 0xF) == 0) {
        v >>= 4;
        c += 4;
      }
      if((v & 0x3) == 0) {
        v >>= 2;
        c += 2;
      }
      c -= v & 0x1;

      return c + count;
    }


    ::std::ostream& outputHex(::std::ostream& ostr, unsigned long i)
    {
      char old = ostr.fill('0');
      ::std::streamsize oss = ostr.width(2*sizeof(unsigned long));
      ostr << ::std::hex << i;
      ostr.width(oss);
      ostr.fill(old);
      return ostr;
    }
  } // end namespace anonymous

  BitTruthTable::BitTruthTable() { ; }
  BitTruthTable::BitTruthTable(const BitTruthTable& o) : function(o.function)
  { ; }

  BitTruthTable BitTruthTable::posCofactor(const BitTruthTable& rhs) const
  {
    BitTruthTable res(*this);
    unsigned trail_zeros = trailing_zeros(rhs.function);
    if(trail_zeros < sizeof(unsigned long)*8) {
      unsigned size = res.function.size();
      unsigned long variable_mask = rhs.function[0];
      for(unsigned i = 0; i < size; ++i) {
        unsigned long masked = res.function[i] & variable_mask;
        res.function[i] = masked | (masked >> trail_zeros);
      }
    } else {
      unsigned var_block_words = trail_zeros / (sizeof(unsigned long)*8);
      unsigned var_double_block = 2*var_block_words;
      unsigned blocks = res.function.size() / var_double_block;
      for(unsigned j = 0; j < blocks; ++j) {
        for(unsigned i = 0; i < var_block_words; ++i) {
          unsigned lowindex = var_double_block*j + i;
          unsigned highindex = lowindex + var_block_words;
          res.function[lowindex] = res.function[highindex];
        }
      }
    }
    return res;
  }

  BitTruthTable BitTruthTable::negCofactor(const BitTruthTable& rhs) const
  {
    BitTruthTable res(*this);
    unsigned trail_zeros = trailing_zeros(rhs.function);
    if(trail_zeros < sizeof(unsigned long)*8) {
      unsigned size = res.function.size();
      unsigned long variable_mask = ~rhs.function[0];
      for(unsigned i = 0; i < size; ++i) {
        unsigned long masked = res.function[i] & variable_mask;
        res.function[i] = masked | (masked << trail_zeros);
      }
    } else {
      unsigned var_block_words = trail_zeros / (sizeof(unsigned long)*8);
      unsigned var_double_block = 2*var_block_words;
      unsigned blocks = res.function.size() / var_double_block;
      for(unsigned j = 0; j < blocks; ++j) {
        for(unsigned i = 0; i < var_block_words; ++i) {
          unsigned lowindex = var_double_block*j + i;
          unsigned highindex = lowindex + var_block_words;
          res.function[highindex] = res.function[lowindex];
        }
      }
    }
    return res;
  }

  ::std::pair<BitTruthTable,BitTruthTable> BitTruthTable::cofactors(const BitTruthTable& rhs) const
  {
    return ::std::make_pair(negCofactor(rhs), posCofactor(rhs));
  }


  ::std::ostream& operator<<(::std::ostream& ostr, const BitTruthTable& tt)
  {
    ostr << "0x";
    for(int i = tt.function.size() - 1; i >= 0; --i) {
      outputHex(ostr, tt.function[i]);
    }
    return ostr;
  }

  size_t BitTruthTable::hash() const
  {
    unsigned size = function.size();
    size_t v = size;
    for(unsigned i = 0; i < size; ++i) {
      v ^= function[i]*29*i;
    }
    return v;
  }

} // end namespace TruthTable
