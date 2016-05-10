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

#include "TreeTruthTable.h"
#include<cassert>
#include<set>

// implementation of the reference couting routines
namespace boost
{
  void intrusive_ptr_add_ref(::TruthTable::Private::TreeTruthTableNode* p)
  { ++p->count; }
  void intrusive_ptr_release(::TruthTable::Private::TreeTruthTableNode* p)
  { if(--p->count == 0) delete p; }
} // end namespace boost

namespace TruthTable
{
  namespace Private
  {

    // TreeTruthTableNode Constructors
    TreeTruthTableNode::TreeTruthTableNode(bool b) : type(b ? TRUE : FALSE), variable(0), count(0)
    { }

    TreeTruthTableNode::TreeTruthTableNode(unsigned long variable,
                               const ::boost::intrusive_ptr<TreeTruthTableNode>& tptr,
                               const ::boost::intrusive_ptr<TreeTruthTableNode>& fptr)
                                  : type(VAR), variable(variable), tptr(tptr), fptr(fptr), count(0)
    { }

    size_t TreeTruthTableNode::hash() const
    {
      switch(type) {
        case TRUE:
          return 0;
        case FALSE:
          return 1;
        case VAR:
          return (17*variable) ^ ((17*1019*tptr->hash()) ^ (1019*1019*fptr->hash()));
        default:
          assert(false);
          break;
      }
      return 0;
    }

    // Functions on TreeTruthTableNodes
    bool compareEqual(const ::boost::intrusive_ptr<TreeTruthTableNode>& a, const ::boost::intrusive_ptr<TreeTruthTableNode>& b)
    {
      assert(a != 0);
      assert(b != 0);
      // short circuit compare pointers
      if(a == b)
        return true;

      // if types are different, we already know they're different
      if(a->type != b->type)
        return false;

      // if types are true or false and they're the same, true
      switch(a->type) {
        case TreeTruthTableNode::TRUE:
        case TreeTruthTableNode::FALSE:
          return true;
        default:
          // fall through
          break;
      }

      // both are variables
      assert(a->type == TreeTruthTableNode::VAR);
      assert(b->type == TreeTruthTableNode::VAR);

      // if variables are different they're not the same
      if(a->variable != b->variable)
        return false;

      // variables are the same, recursively compare each part
      return compareEqual(a->tptr,b->tptr) && compareEqual(a->fptr, b->fptr);
    }


    ::boost::intrusive_ptr<TreeTruthTableNode> negate(const ::boost::intrusive_ptr<TreeTruthTableNode>& n)
    {
      assert(n != 0);
      if(n->type == TreeTruthTableNode::TRUE) {
        ::boost::intrusive_ptr<TreeTruthTableNode> r(new TreeTruthTableNode(false));
        return r;
      } else if(n->type == TreeTruthTableNode::FALSE) {
        ::boost::intrusive_ptr<TreeTruthTableNode> r(new TreeTruthTableNode(true));
        return r;
      } else {
        ::boost::intrusive_ptr<TreeTruthTableNode> ntptr(negate(n->tptr));
        ::boost::intrusive_ptr<TreeTruthTableNode> nfptr(negate(n->fptr));
        ::boost::intrusive_ptr<TreeTruthTableNode> r(new TreeTruthTableNode(n->variable, ntptr, nfptr));
        return r;
      }
    }

    ::boost::intrusive_ptr<TreeTruthTableNode> conjoin(const ::boost::intrusive_ptr<TreeTruthTableNode>& a, const ::boost::intrusive_ptr<TreeTruthTableNode>& b)
    {
      assert(a != 0);
      assert(b != 0);
      switch(a->type) {
        case TreeTruthTableNode::TRUE:
          return b;
        case TreeTruthTableNode::FALSE:
          return a;
        default:
          // fall through
          break;
      }

      switch(b->type) {
        case TreeTruthTableNode::TRUE:
          return a;
        case TreeTruthTableNode::FALSE:
          return b;
        default:
          // fall through
          break;
      }

      // actually found a variable
      if(a->variable < b->variable) {
        ::boost::intrusive_ptr<TreeTruthTableNode> l(conjoin(a->tptr, b));
        ::boost::intrusive_ptr<TreeTruthTableNode> r(conjoin(a->fptr, b));
        if(compareEqual(l, r)) {
          return l;
        } else {
          ::boost::intrusive_ptr<TreeTruthTableNode> res(new TreeTruthTableNode(a->variable, l, r));
          return res;
        }
      } else if(a->variable == b->variable) {
        ::boost::intrusive_ptr<TreeTruthTableNode> l(conjoin(a->tptr, b->tptr));
        ::boost::intrusive_ptr<TreeTruthTableNode> r(conjoin(a->fptr, b->fptr));
        if(compareEqual(l, r)) {
          return l;
        } else {
          ::boost::intrusive_ptr<TreeTruthTableNode> res(new TreeTruthTableNode(a->variable, l, r));
          return res;
        }
      } else {
        ::boost::intrusive_ptr<TreeTruthTableNode> l(conjoin(a, b->tptr));
        ::boost::intrusive_ptr<TreeTruthTableNode> r(conjoin(a, b->fptr));
        if(compareEqual(l, r)) {
          return l;
        } else {
          ::boost::intrusive_ptr<TreeTruthTableNode> res(new TreeTruthTableNode(b->variable, l, r));
          return res;
        }
      }
    }

    ::boost::intrusive_ptr<TreeTruthTableNode> disjoin(const ::boost::intrusive_ptr<TreeTruthTableNode>& a, const ::boost::intrusive_ptr<TreeTruthTableNode>& b)
    {
      assert(a != 0);
      assert(b != 0);
      switch(a->type) {
        case TreeTruthTableNode::TRUE:
          return a;
        case TreeTruthTableNode::FALSE:
          return b;
        default:
          // fall through
          break;
      }

      switch(b->type) {
        case TreeTruthTableNode::TRUE:
          return b;
        case TreeTruthTableNode::FALSE:
          return a;
        default:
          // fall through
          break;
      }

      // actually found a variable
      if(a->variable < b->variable) {
        ::boost::intrusive_ptr<TreeTruthTableNode> l(disjoin(a->tptr, b));
        ::boost::intrusive_ptr<TreeTruthTableNode> r(disjoin(a->fptr, b));
        if(compareEqual(l, r)) {
          return l;
        } else {
          ::boost::intrusive_ptr<TreeTruthTableNode> res(new TreeTruthTableNode(a->variable, l, r));
          return res;
        }
      } else if(a->variable == b->variable) {
        ::boost::intrusive_ptr<TreeTruthTableNode> l(disjoin(a->tptr, b->tptr));
        ::boost::intrusive_ptr<TreeTruthTableNode> r(disjoin(a->fptr, b->fptr));
        if(compareEqual(l, r)) {
          return l;
        } else {
          ::boost::intrusive_ptr<TreeTruthTableNode> res(new TreeTruthTableNode(a->variable, l, r));
          return res;
        }
      } else {
        ::boost::intrusive_ptr<TreeTruthTableNode> l(disjoin(a, b->tptr));
        ::boost::intrusive_ptr<TreeTruthTableNode> r(disjoin(a, b->fptr));
        if(compareEqual(l, r)) {
          return l;
        } else {
          ::boost::intrusive_ptr<TreeTruthTableNode> res(new TreeTruthTableNode(b->variable, l, r));
          return res;
        }
      }
    }

    ::boost::intrusive_ptr<TreeTruthTableNode> cofactor(bool cof, const ::boost::intrusive_ptr<TreeTruthTableNode>& a, const ::boost::intrusive_ptr<TreeTruthTableNode>& b)
    {
      assert(a != 0);
      assert(b != 0);
      // b should be a variable
      assert(b->type == TreeTruthTableNode::VAR);
      assert(b->tptr->type == TreeTruthTableNode::TRUE);
      assert(b->fptr->type == TreeTruthTableNode::FALSE);

      unsigned long cofvar = b->variable;

      // if a is true or false, just return a
      switch(a->type) {
        case TreeTruthTableNode::TRUE:
        case TreeTruthTableNode::FALSE:
          return a;
        default:
          // fall through
          break;
      }

      assert(a->type == TreeTruthTableNode::VAR);
      if(a->variable < cofvar) {
        // keep looking for variable
        ::boost::intrusive_ptr<TreeTruthTableNode> l(cofactor(cof, a->tptr, b));
        ::boost::intrusive_ptr<TreeTruthTableNode> r(cofactor(cof, a->fptr, b));
        if(compareEqual(l, r)) {
          return l;
        } else {
          ::boost::intrusive_ptr<TreeTruthTableNode> res(new TreeTruthTableNode(a->variable, l, r));
          return res;
        }
      } else if(a->variable == cofvar) {
        // we found it, take cofactor
        return cof ? a->tptr : a->fptr;
      } else {
        // we've passed it
        return a;
      }

    }


    std::ostream& operator<<(std::ostream& ostr, const TreeTruthTableNode& n)
    {
      if(n.type == TreeTruthTableNode::TRUE)
        ostr << "t";
      else if(n.type == TreeTruthTableNode::FALSE)
        ostr << "f";
      else //type == TreeTruthTableNode::VAR
        ostr << "(" << n.variable << " " << *(n.tptr) << " " << *(n.fptr) << ")";
      return ostr;
    }

    void varCount(const ::boost::intrusive_ptr<TreeTruthTableNode>& p, ::std::set<unsigned>& visited)
    {
      switch(p->type) {
        case TreeTruthTableNode::VAR:
          visited.insert(p->variable);
          varCount(p->tptr, visited);
          varCount(p->fptr, visited);
          break;
        default:
          // don't do anything
          break;
      }
    }

  } // end namespace Private


  size_t TreeTruthTable::hash() const
  {
    return function->hash();
  }

  unsigned TreeTruthTable::varCount() const
  {
    ::std::set<unsigned> indices;
    ::TruthTable::Private::varCount(function, indices);
    return indices.size();
  }


  // TreeTruthTable Constructors
  TreeTruthTable::TreeTruthTable(const ::boost::intrusive_ptr<Private::TreeTruthTableNode>& f) : function(f)
  { }

  TreeTruthTable::TreeTruthTable() : function()
  { }

  TreeTruthTable::TreeTruthTable(const TreeTruthTable& o) : function(o.function)
  { }

  std::ostream& operator<<(std::ostream& ostr, const TreeTruthTable& t)
  {
    ostr << *(t.function);
    return ostr;
  }
} // end namespace TruthTable
