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

#ifndef CUBE_H
#define CUBE_H

#include<set>
#include<vector>
#include<iterator>
#include<cassert>
#include<cstdlib>
#include<boost/operators.hpp>
#ifndef NIOS
#include<iostream>
#endif

namespace CNF
{

  class Cover : ::boost::multipliable<Cover, long>, ::boost::addable<Cover> {
  private:
    std::set<std::set<long> > value;
    
  public:
    Cover(bool b) {
      if(b) {
        std::set<long> s;
        value.insert(s);
      } 
    }

    Cover(const Cover& o) : value(o.value)
    { }

    Cover& operator*=(const long l)
    {
      assert(l != 0);
      std::set<std::set<long> > res;
      for(std::set<std::set<long> >::iterator i = value.begin(); i != value.end(); ++i) {
        std::set<long> t(i->begin(), i->end());
        t.insert(l);
        res.insert(t);
      }
      value = res;
      return *this;
    }

    Cover& operator+=(const Cover& rhs)
    {
      value.insert(rhs.value.begin(), rhs.value.end());
      return *this;
    }

    unsigned size() const
    {
      return value.size();
    }

    template<typename ForwardIterator, typename TT>
    TT toTruthTable(const ForwardIterator& begin, const ForwardIterator& end, const TT& t, const TT& f) const
    {
      TT res = f;
      std::set<std::set<long> >::iterator i = value.begin();
      for(; i != value.end(); ++i) {
        TT disjunct = t;
        for(std::set<long>::iterator j = i->begin(); j != i->end(); ++j) {
          assert(begin + *j - 1 < end);
          assert(begin - *j - 1 < end);
          //std::cout << *j << std::endl;
          assert(*j != 0);
          ForwardIterator f(begin);
          if(*j > 0) {
            ::std::advance(f, *j - 1);
            disjunct &= *f;
          } else {
            ::std::advance(f, -*j - 1);
            disjunct &= ~(*f);
          }
        }
        res |= disjunct;
      }
      return res;
    }

    template<typename MapIterator, typename TT>
    TT toTruthTable_map(const MapIterator& begin, const MapIterator& end, const TT& t, const TT& f) const
    {
      TT res = f;
      std::set<std::set<long> >::iterator i = value.begin();
      for(; i != value.end(); ++i) {
        TT disjunct = t;
        for(std::set<long>::iterator j = i->begin(); j != i->end(); ++j) {
          //std::cout << *j << std::endl;
          assert(*j != 0);
          MapIterator f(begin);
          if(*j > 0) {
            ::std::advance(f, *j - 1);
            disjunct &= f->second;
          } else {
            ::std::advance(f, -*j - 1);
            disjunct &= ~(f->second);
          }
        }
        res |= disjunct;
      }
      return res;
    }

    template <typename OutputIterator>
    void variables(OutputIterator& result)
    {
      for(std::set<std::set<long> >::iterator i = value.begin(); i != value.end(); ++i) {
        for(std::set<long>::iterator j = i->begin(); j != i->end(); ++j) {
          *result = abs(*j);
          ++result;
        }
      }
    }


    inline ::std::set< ::std::set<long>>& getCover()
    {
      return value;
    }


#ifndef NIOS
    friend ::std::ostream& operator<<(::std::ostream& ostr, const Cover& c);
#endif

  };
} // end namespace CNF

#endif
