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

#ifndef ISOP_H
#define ISOP_H

#include<iterator>
#include<utility>
#include<iterator>
#include "Cover.h"

namespace CNF
{
  template <typename ForwardIterator, typename TT>
  Cover isop(const ForwardIterator& begin, const ForwardIterator& start, const ForwardIterator& end, const TT& l, const TT& u, const TT& t, const TT& f)
  {
    //if the search is complete, just return true or false
    if(l == f) {
      Cover n(false);
      return n;
    }

    if(u == t) {
      Cover n(true);
      return n;
    }

    //select a variable that affects the problem and take the cofactors of the propblem with respect to it
    ForwardIterator fv = TT::firstVar(start, end, l, u);
    //std::cout << "selected var: " << fv-begin << std::endl;
    ::std::pair<TT,TT> lcof = l.cofactors(*fv);
    ::std::pair<TT,TT> ucof = u.cofactors(*fv);
    
    //produce a new iterator that is one past the found variable.  This prunes the search space for firstVar.
    ForwardIterator newstart = fv;
    ++newstart;

    //compute the first two recursive calls.  Compute the negation separately, so we can mutate it, potentially saving time.
    TT nu1 = ~ucof.second;
    TT nu0 = ~ucof.first;
    nu1 &= lcof.first;
    nu0 &= lcof.second;
    Cover c0 = isop(begin, newstart, end, nu1, ucof.first, t, f);
    Cover c1 = isop(begin, newstart, end, nu0, ucof.second, t, f);

    // convert covers to truth tables
    TT c0f = c0.toTruthTable(begin, end, t, f);
    TT c1f = c1.toTruthTable(begin, end, t, f);

    //now we mutate l0, l1 and u0 to compute the third recursive call
    lcof.first &= ~(c0f);
    lcof.second &= ~(c1f);
    lcof.first |= lcof.second;
    ucof.first &= ucof.second;
    Cover cs = isop(begin, newstart, end, lcof.first, ucof.first, t, f);

    //compute the cost of this portion of the problem

    //compute the resulting function
    long dist = (long)(::std::distance(begin,fv)+1);
    c0 *= -dist;
    c1 *= dist;
    c0 += c1;
    c0 += cs;

    return c0;
  }

  template <typename MapIterator, typename TT>
  Cover isop_map(const MapIterator& begin, const MapIterator& start, const MapIterator& end, const TT& l, const TT& u, const TT& t, const TT& f)
  {
    //if the search is complete, just return true or false
    if(l == f) {
      Cover n(false);
      return n;
    }

    if(u == t) {
      Cover n(true);
      return n;
    }

    //select a variable that affects the problem and take the cofactors of the propblem with respect to it
    MapIterator fv = TT::firstVar_map(start, end, l, u);
    //std::cout << "selected var: " << fv-begin << std::endl;
    ::std::pair<TT,TT> lcof = l.cofactors(fv->second);
    ::std::pair<TT,TT> ucof = u.cofactors(fv->second);
    
    //produce a new iterator that is one past the found variable.  This prunes the search space for firstVar.
    MapIterator newstart = fv;
    ++newstart;

    //compute the first two recursive calls.  Compute the negation separately, so we can mutate it, potentially saving time.
    TT nu1 = ~ucof.second;
    TT nu0 = ~ucof.first;
    nu1 &= lcof.first;
    nu0 &= lcof.second;
    Cover c0 = isop_map(begin, newstart, end, nu1, ucof.first, t, f);
    Cover c1 = isop_map(begin, newstart, end, nu0, ucof.second, t, f);

    // convert covers to truth tables
    TT c0f = c0.toTruthTable_map(begin, end, t, f);
    TT c1f = c1.toTruthTable_map(begin, end, t, f);

    //now we mutate l0, l1 and u0 to compute the third recursive call
    lcof.first &= ~(c0f);
    lcof.second &= ~(c1f);
    lcof.first |= lcof.second;
    ucof.first &= ucof.second;
    Cover cs = isop_map(begin, newstart, end, lcof.first, ucof.first, t, f);

    //compute the cost of this portion of the problem

    //compute the resulting function
    long dist = (long)(::std::distance(begin,fv)+1);
    c0 *= -dist;
    c1 *= dist;
    c0 += c1;
    c0 += cs;

    return c0;
  }

  template<typename ForwardIterator, typename TT>
  std::pair<unsigned, std::set<long> >isop_cost(const ForwardIterator& begin, const ForwardIterator& end, const TT& fun, const TT& t, const TT& f)
  {
    Cover c = isop(begin, begin, end, fun, fun, t, f);
    TT nfun(fun);
    nfun.negate();
    Cover cn = isop(begin, begin, end, nfun, nfun, t, f);

    std::set<long> vars;
    std::insert_iterator<std::set<long> > ins = ::std::inserter(vars, vars.begin());
    c.variables(ins);
    cn.variables(ins);

    return make_pair(c.size()+cn.size(), vars);
  }

  template<typename MapIterator, typename TT, typename OutputIterator>
  unsigned isop_cost_map(const MapIterator& begin, const MapIterator& end, const TT& fun, const TT& t, const TT& f, OutputIterator& result)
  {
    Cover c = isop_map(begin, begin, end, fun, fun, t, f);
    TT nfun(fun);
    nfun.negate();
    Cover cn = isop_map(begin, begin, end, nfun, nfun, t, f);

    // get variables and merge them
    std::set<long> vars;
    std::insert_iterator<std::set<long> > ins = ::std::inserter(vars, vars.begin());
    c.variables(ins);
    cn.variables(ins);

    // construct result by converting variables to the appropriate index type
    for(std::set<long>::iterator i = vars.begin(); i != vars.end(); ++i) {
      MapIterator t(begin);
      advance(t, *i-1);
      *result = t->first;
      ++result;
    }
    return c.size()+cn.size();
  }

  template<typename ForwardIterator, typename TT>
  Cover isop(const ForwardIterator& begin, const ForwardIterator& end, const TT& fun, const TT& t, const TT& f)
  {
    Cover c(isop(begin, begin, end, fun, fun, t, f));
    return c;
  }

  template<typename MapIterator, typename TT>
  Cover isop_map(const MapIterator& begin, const MapIterator& end, const TT& fun, const TT& t, const TT& f)
  {
    Cover c(isop_map(begin, begin, end, fun, fun, t, f));
    return c;
  }

} // end namespace CNF

#endif
