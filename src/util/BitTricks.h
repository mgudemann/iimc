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

#ifndef BITTRICKS_H
#define BITTRICKS_H
#include<cassert>
#include<stdint.h>

namespace Util
{
  namespace Private
  {
    template<typename T, int size>
    struct basic_pattern
    {
      static const T value = (((T)1) << (size-1)) | (basic_pattern<T, size-1>::value);
    };

    template<typename T>
    struct basic_pattern<T, 0>
    {
      static const T value = 0;
    };

    template<typename T, int size, int start=(sizeof(T)*8)>
    struct generate_pattern
    {
      static const T value = ((basic_pattern<T, size/2>::value) << (start - size)) | (generate_pattern<T, size, start-size>::value);
    };

    template<typename T, int size>
    struct generate_pattern<T, size, 0>
    {
      static const T value = 0;
    };

    template<typename T, int index>
    struct generate_bit_pattern
    {
      static const T value = generate_pattern<T, 1 << (index+1)>::value;
    };

    template<int i>
    struct log2
    {
      static const int value = 1+log2<(i>>1)>::value;
    };

    template<>
    struct log2<0>
    {
      static const int value = -1;
    };

    template<typename T, int index=log2<sizeof(T)*8>::value-1>
    struct count_bits {
      static inline int count(const T& v)
      {
        T c = count_bits<T, index-1>::count(v);
        c = ((c >> (1 << index)) + c) & generate_bit_pattern<T, index>::value;
        return c;
      }
    };

    template<typename T>
    struct count_bits<T, 1>
    {
      static inline int count(const T& v)
      {
        int c = count_bits<T, 0>::count(v);
        c = ((c >> 2) & generate_bit_pattern<T, 1>::value) + (c & generate_bit_pattern<T, 1>::value);
        return c;
      }
    };

    template<typename T>
    struct count_bits<T, 0>
    {
      static inline int count(const T& v)
      {
        return v - ((v >> 1) & generate_bit_pattern<T, 0>::value);
      }
    };

    template<typename T>
    struct pattern_count
    {
      static const int value = log2<sizeof(T)*8>::value;
    };

    template<typename T, int pat>
    struct pattern_get
    {
      static inline T getPattern(const int i)
      {
        if(i == pat)
          return generate_bit_pattern<T, pat>::value;
        else
          return pattern_get<T, pat-1>::getPattern(i);
      }
    };

    template<typename T>
    struct pattern_get<T, -1>
    {
      static inline T getPattern(const int i)
      {
        assert(false);
      }
    };
  } // namespace Private


  // counts number of set bits in any integer type
  template<typename T>
  inline unsigned count_bits(const T& v)
  {
    return Private::count_bits<T>::count(v);
  }

  template<>
  inline unsigned count_bits(const uint32_t& v)
  {
    unsigned c = v - ((v >> 1) & 0x55555555);
    c = (c & 0x33333333) + ((c >> 2) & 0x33333333);
    c = (((c + (c >> 4)) & 0xF0F0F0F) * 0x1010101) >> 24;
    return c;
  }

#if 0
  template<>
  inline unsigned count_bits(const uint64_t& v)
  {
    assert(false);
  }
#endif

  // generates alternating bit pattern eg (for 32 bit int):
  // pattern 0: 0xAAAAAAAA
  // pattern 1: 0xCCCCCCCC
  // pattern 2: 0xF0F0F0F0
  // pattern 3: 0xFF00FF00
  template<typename T>
  inline const T pattern(const int i)
  {
    return ~Private::pattern_get<T, Private::log2<sizeof(T)*8>::value - 1>::getPattern(i);
  }

  // generates inverse of pattern
  template<typename T>
  inline const T ipattern(const int i)
  {
    return Private::pattern_get<T, Private::log2<sizeof(T)*8>::value - 1>::getPattern(i);
  }

  template<typename T>
  inline const T pattern_count()
  {
    return Private::pattern_count<T>::value;
  }

} // namespace Util


#if 0

#include <iostream>
#include <iomanip>

int main()
{
  unsigned long i = Util::Private::basic_pattern<unsigned long, 32>::value;
  std::cout << std::hex << i << std::endl;

  return 0;
}
#endif

#endif
