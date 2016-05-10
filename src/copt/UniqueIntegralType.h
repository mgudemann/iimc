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

#ifndef UNIQUEINTEGRALTYPE_H
#define UNIQUEINTEGRALTYPE_H
#include<boost/operators.hpp>
#include<iostream>
#include<functional>
#include<utility>

#ifndef UNIQUE
#define UIGET(n) (n)
#else
#define UIGET(n) ((n).get())
#endif

namespace Opt
{
  template <typename T, int ident>
  class UniqueIntegralType : ::boost::operators<UniqueIntegralType<T,ident> >, ::boost::operators2<UniqueIntegralType<T,ident>,T>
  {
  private:
    T value;

  public:
    UniqueIntegralType() { }
    UniqueIntegralType(const UniqueIntegralType<T, ident>& other) : value(other.value) { }
    UniqueIntegralType(const T& v) : value(v) { }

    inline UniqueIntegralType<T, ident>& operator=(const UniqueIntegralType<T, ident>& other)
    {
      value = other.value;
      return *this;
    }

    inline UniqueIntegralType<T, ident>& operator=(const T& other)
    {
      value = other;
      return *this;
    }
    
    inline bool operator<(const UniqueIntegralType<T, ident>& other) const
    { return value < other.value; }

    inline bool operator==(const UniqueIntegralType<T, ident>& other) const
    { return value == other.value; }
    
    inline UniqueIntegralType<T, ident>& operator+=(const UniqueIntegralType<T, ident>& other)
    { 
      value += other.value;
      return *this;
    }

    inline UniqueIntegralType<T, ident>& operator-=(const UniqueIntegralType<T, ident>& other)
    { 
      value -= other.value;
      return *this;
    }

    inline UniqueIntegralType<T, ident>& operator*=(const UniqueIntegralType<T, ident>& other)
    { 
      value *= other.value;
      return *this;
    }

    inline UniqueIntegralType<T, ident>& operator/=(const UniqueIntegralType<T, ident>& other)
    { 
      value /= other.value;
      return *this;
    }

    inline UniqueIntegralType<T, ident>& operator%=(const UniqueIntegralType<T, ident>& other)
    { 
      value %= other.value;
      return *this;
    }

    inline UniqueIntegralType<T, ident>& operator|=(const UniqueIntegralType<T, ident>& other)
    { 
      value |= other.value;
      return *this;
    }

    inline UniqueIntegralType<T, ident>& operator&=(const UniqueIntegralType<T, ident>& other)
    { 
      value &= other.value;
      return *this;
    }
    
    inline UniqueIntegralType<T, ident>& operator^=(const UniqueIntegralType<T, ident>& other)
    { 
      value ^= other.value;
      return *this;
    }

    inline UniqueIntegralType<T, ident>& operator++()
    {
      ++value;
      return *this;
    }

    inline UniqueIntegralType<T, ident>& operator--()
    {
      --value;
      return *this;
    }

    inline bool operator<(const T& other) const
    { return value < other; }

    inline bool operator==(const T& other) const
    { return value == other; }
    
    inline UniqueIntegralType<T, ident>& operator+=(const T& other)
    { 
      value += other;
      return *this;
    }

    inline UniqueIntegralType<T, ident>& operator-=(const T& other)
    { 
      value -= other;
      return *this;
    }

    inline UniqueIntegralType<T, ident>& operator*=(const T& other)
    { 
      value *= other;
      return *this;
    }

    inline UniqueIntegralType<T, ident>& operator/=(const T& other)
    { 
      value /= other;
      return *this;
    }

    inline UniqueIntegralType<T, ident>& operator%=(const T& other)
    { 
      value %= other;
      return *this;
    }

    inline UniqueIntegralType<T, ident>& operator|=(const T& other)
    { 
      value |= other;
      return *this;
    }

    inline UniqueIntegralType<T, ident>& operator&=(const T& other)
    { 
      value &= other;
      return *this;
    }
    
    inline UniqueIntegralType<T, ident>& operator^=(const T& other)
    { 
      value ^= other;
      return *this;
    }

    inline T get() const
    {
      return value;
    }

  };
} // end namespace Opt

namespace std
{
  template <typename T, int ident>
  inline ostream& operator<<(ostream& ostr, const ::Opt::UniqueIntegralType<T, ident>& rhs)
  {
    ostr << rhs.get();
    return ostr;
  }

  template <typename T, int ident>
  struct hash< ::Opt::UniqueIntegralType<T, ident> > : public std::unary_function< ::Opt::UniqueIntegralType<T, ident>, size_t>
  {
    size_t operator()(const ::Opt::UniqueIntegralType<T, ident>& uit) const
    {
      hash<T> h;
      return h(uit.get());
    }
  };
  
} // end namespace std

#endif
