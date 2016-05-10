/* -*- C++ -*- */

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

#ifndef TREETRUTHTABLE_H
#define TREETRUTHTABLE_H

#define BOOST_DISABLE_ASSERTS
#include<boost/operators.hpp>
#include<iostream>
#include<utility>
#include<functional>
#include<cassert>

/** @file TreeTruthTable.h */

namespace TruthTable
{
  namespace Private
  {
    struct TreeTruthTableNode;
  }
}

// declaration of the reference counting routines
namespace boost
{
  void intrusive_ptr_add_ref(::TruthTable::Private::TreeTruthTableNode* p);
  void intrusive_ptr_release(::TruthTable::Private::TreeTruthTableNode* p);
}

#include<boost/intrusive_ptr.hpp>

namespace TruthTable
{
  namespace Private
  {
    // internal data structure used to represent truth tables on ordered variables
    struct TreeTruthTableNode {
      enum TreeTruthTableNodeT { VAR, TRUE, FALSE };
      const TreeTruthTableNodeT type;
      const unsigned long variable;
      const ::boost::intrusive_ptr<TreeTruthTableNode> tptr;
      const ::boost::intrusive_ptr<TreeTruthTableNode> fptr;

    private:
      // reference count
      unsigned count;

      // friend routines to modify the count
      friend void ::boost::intrusive_ptr_add_ref(TreeTruthTableNode* p);
      friend void ::boost::intrusive_ptr_release(TreeTruthTableNode* p);

    public:
      TreeTruthTableNode(bool b);
      TreeTruthTableNode(unsigned long variable, const ::boost::intrusive_ptr<TreeTruthTableNode>& tptr, const ::boost::intrusive_ptr<TreeTruthTableNode>& fptr);

      friend std::ostream& operator<<(std::ostream& ostr, const TreeTruthTableNode& n);

      size_t hash() const;
    };
  } // end namespace Private

  class TreeTruthTable : ::boost::bitwise<TreeTruthTable>, ::boost::equality_comparable<TreeTruthTable> {
  private:
    ::boost::intrusive_ptr<Private::TreeTruthTableNode> function;
    TreeTruthTable(const ::boost::intrusive_ptr<Private::TreeTruthTableNode>& f);
  public:
    inline TreeTruthTable& operator=(const TreeTruthTable& rhs);
    inline TreeTruthTable& negate();
    inline TreeTruthTable operator~() const;
    inline TreeTruthTable& operator&=(const TreeTruthTable& rhs);
    inline TreeTruthTable& operator|=(const TreeTruthTable& rhs);
    inline TreeTruthTable& operator^=(const TreeTruthTable& rhs);
    inline bool operator==(const TreeTruthTable& rhs) const;

    inline TreeTruthTable posCofactor(const TreeTruthTable& rhs) const;
    inline TreeTruthTable negCofactor(const TreeTruthTable& rhs) const;
    inline ::std::pair<TreeTruthTable,TreeTruthTable> cofactors(const TreeTruthTable& rhs) const;

    unsigned varCount() const;

    size_t hash() const;

    template <typename ForwardIterator>
    static ForwardIterator firstVar(const ForwardIterator& begin, const ForwardIterator& end, const TreeTruthTable& a, const TreeTruthTable b);

    template <typename MapIterator>
    static MapIterator firstVar_map(const MapIterator& begin, const MapIterator& end, const TreeTruthTable& a, const TreeTruthTable b);

    friend std::ostream& operator<<(std::ostream& ostr, const TreeTruthTable& t);

    TreeTruthTable();
    TreeTruthTable(const TreeTruthTable& o);

  public:
    template <typename ForwardIterator>
    static void variables(const ForwardIterator& begin, const ForwardIterator& end, TreeTruthTable& tprop, TreeTruthTable& fprop);

    template <typename MapIterator>
    static void variables_map(const MapIterator& begin, const MapIterator& end, TreeTruthTable& tprop, TreeTruthTable& fprop);
  };
} // end namespace TruthTable



namespace TruthTable
{

  namespace Private {
    bool compareEqual(const ::boost::intrusive_ptr<TreeTruthTableNode>& a, const ::boost::intrusive_ptr<TreeTruthTableNode>& b);
    ::boost::intrusive_ptr<TreeTruthTableNode> negate(const ::boost::intrusive_ptr<TreeTruthTableNode>& n);
    ::boost::intrusive_ptr<TreeTruthTableNode> conjoin(const ::boost::intrusive_ptr<TreeTruthTableNode>& a, const ::boost::intrusive_ptr<TreeTruthTableNode>& b);
    ::boost::intrusive_ptr<TreeTruthTableNode> disjoin(const ::boost::intrusive_ptr<TreeTruthTableNode>& a, const ::boost::intrusive_ptr<TreeTruthTableNode>& b);
    ::boost::intrusive_ptr<TreeTruthTableNode> cofactor(bool cof, const ::boost::intrusive_ptr<TreeTruthTableNode>& a, const ::boost::intrusive_ptr<TreeTruthTableNode>& b);
  }




  // TreeTruthTable Operators

  TreeTruthTable& TreeTruthTable::operator=(const TreeTruthTable& rhs)
  {
    function = rhs.function;
    return *this;
  }

  TreeTruthTable& TreeTruthTable::negate()
  {
    function = Private::negate(function);
    return *this;
  }

  TreeTruthTable TreeTruthTable::operator~() const
  {
    return Private::negate(function);
  }

  TreeTruthTable& TreeTruthTable::operator&=(const TreeTruthTable& rhs)
  {
    function = Private::conjoin(function, rhs.function);
    return *this;
  }

  TreeTruthTable& TreeTruthTable::operator|=(const TreeTruthTable& rhs)
  {
    function = Private::disjoin(function, rhs.function);
    return *this;
  }

  TreeTruthTable& TreeTruthTable::operator^=(const TreeTruthTable& rhs)
  {
    function = Private::disjoin(Private::conjoin(function, Private::negate(rhs.function)), Private::conjoin(Private::negate(function), rhs.function));
    return *this;
  }

  bool TreeTruthTable::operator==(const TreeTruthTable& rhs) const
  {
    return Private::compareEqual(function, rhs.function);
  }

  
  TreeTruthTable TreeTruthTable::posCofactor(const TreeTruthTable& rhs) const
  {
    TreeTruthTable ret(Private::cofactor(true, function, rhs.function));
    return ret;
  }

  TreeTruthTable TreeTruthTable::negCofactor(const TreeTruthTable& rhs) const
  {
    TreeTruthTable ret(Private::cofactor(false, function, rhs.function));
    return ret;
  }

  ::std::pair<TreeTruthTable,TreeTruthTable> TreeTruthTable::cofactors(const TreeTruthTable& rhs) const
  {
    return ::std::make_pair(negCofactor(rhs), posCofactor(rhs));
  }

  // TreeTruthTable variable initializers
  template <typename ForwardIterator>
  void TreeTruthTable::variables(const ForwardIterator& begin, const ForwardIterator& end, TreeTruthTable& tprop, TreeTruthTable& fprop)
  {
    unsigned long index = 0;
    ::boost::intrusive_ptr<Private::TreeTruthTableNode> tptr(new Private::TreeTruthTableNode(true));
    ::boost::intrusive_ptr<Private::TreeTruthTableNode> fptr(new Private::TreeTruthTableNode(false));
    for(ForwardIterator i = begin; i != end; ++i) {
      ::boost::intrusive_ptr<Private::TreeTruthTableNode> tpn(new Private::TreeTruthTableNode(index, tptr, fptr));
      TreeTruthTable tp(tpn);
      *i = tp;
      ++index;
    }

    tprop = TreeTruthTable(tptr);
    fprop = TreeTruthTable(fptr);
  }

  template <typename MapIterator>
  void TreeTruthTable::variables_map(const MapIterator& begin, const MapIterator& end, TreeTruthTable& tprop, TreeTruthTable& fprop)
  {
    unsigned long index = 0;
    ::boost::intrusive_ptr<Private::TreeTruthTableNode> tptr(new Private::TreeTruthTableNode(true));
    ::boost::intrusive_ptr<Private::TreeTruthTableNode> fptr(new Private::TreeTruthTableNode(false));
    for(MapIterator i = begin; i != end; ++i) {
      ::boost::intrusive_ptr<Private::TreeTruthTableNode> tpn(new Private::TreeTruthTableNode(index, tptr, fptr));
      TreeTruthTable tp(tpn);
      i->second = tp;
      ++index;
    }

    tprop = TreeTruthTable(tptr);
    fprop = TreeTruthTable(fptr);
  }

  template <typename ForwardIterator>
  ForwardIterator TreeTruthTable::firstVar(const ForwardIterator& begin, const ForwardIterator& end, const TreeTruthTable& a, const TreeTruthTable b)
  {
    assert(a.function->type == Private::TreeTruthTableNode::VAR || b.function->type == Private::TreeTruthTableNode::VAR);
    for(ForwardIterator i = begin; i != end; ++i) {
      assert(i->function->type == Private::TreeTruthTableNode::VAR);
      if(a.function->type == Private::TreeTruthTableNode::VAR && a.function->variable == i->function->variable)
        return i;
      if(b.function->type == Private::TreeTruthTableNode::VAR && b.function->variable == i->function->variable)
        return i;
    }
    assert(false);
    return end;
  }

  template <typename MapIterator>
  MapIterator TreeTruthTable::firstVar_map(const MapIterator& begin, const MapIterator& end, const TreeTruthTable& a, const TreeTruthTable b)
  {
    assert(a.function->type == Private::TreeTruthTableNode::VAR || b.function->type == Private::TreeTruthTableNode::VAR);
    for(MapIterator i = begin; i != end; ++i) {
      assert(i->second.function->type == Private::TreeTruthTableNode::VAR);
      if(a.function->type == Private::TreeTruthTableNode::VAR && a.function->variable == i->second.function->variable)
        return i;
      if(b.function->type == Private::TreeTruthTableNode::VAR && b.function->variable == i->second.function->variable)
        return i;
    }
    assert(false);
    return end;
  }


} // end namespace TruthTable

namespace std
{
  template<>
  struct hash< ::TruthTable::TreeTruthTable > : public std::unary_function< ::TruthTable::TreeTruthTable, size_t>
  {
    size_t operator()(const ::TruthTable::TreeTruthTable& tt) const
    {
      return tt.hash();
    }
  };
} // end namespace std

#endif
