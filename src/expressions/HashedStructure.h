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

#ifndef HASHED_STRUCTURE_
#define HASHED_STRUCTURE_

/** @file HashedStructure.h */

#include <unordered_map>
#include <vector>
#include <cassert>
#include <stdexcept>

#ifdef HAVE_CONFIG_H
#include "config.h"
#endif

#include "ExprTypes.h"

// Fortyeight bits of the 64 that make up an ID are used by the HashedStructure
// base class.  The remaining 16 are left to the derived class.  These 16
// bits are added by shifting the internal 48-bit ID to the left and then
// ORing them to the result.  Of the 48 bits used internally, the most
// significant bits are used to select the context in which the ID exists.
// The following constants create appropriate masks for the manipulation of the
// context levels.  The only "degree of freedom" is N_LOCAL_BITS.

ID const N_LOCAL_BITS = static_cast<ID>(3);
ID const LOCAL_SHIFT = static_cast<ID>(48 - N_LOCAL_BITS);
ID const MASK_LOCAL = ((static_cast<ID>(1) << N_LOCAL_BITS) - 1) << LOCAL_SHIFT;

namespace {

  inline size_t local_level(ID id) {
    return static_cast<size_t>((id & MASK_LOCAL) >> LOCAL_SHIFT);
  }

  inline ID add_level(ID id, size_t level) {
    return id | (static_cast<ID>(level) << LOCAL_SHIFT);
  }

  inline ID remove_level(ID id) {
    return id & ~MASK_LOCAL;
  }

} // anonymous namespace

template <typename N> class HashedStructure;

template<typename N>
class HSManager {

public:

  explicit HSManager(void) : global(new HashedStructure<N>()) {}

  ~HSManager(void) { delete global; }

protected:

  HashedStructure<N> * global;

public:

  class HSView {

    friend class HashedStructure<N>;
    struct stack_element { HashedStructure<N> * hs; bool owns; };
    typedef std::vector<stack_element> HSStack;

  public:

    explicit HSView(HSManager<N> * mgr) :
      stk{stack_element{mgr->global, false}}, man(mgr) {}

    HSView(HSView const & from) {
      for (typename HSStack::const_iterator it = from.stk.begin();
           it != from.stk.end(); ++it) {
        stk.push_back(stack_element{it->hs, false});
      }
    }

    virtual ~HSView(void) {
      // free owned tables
      for (typename HSStack::const_reverse_iterator rit = stk.rbegin();
           rit != stk.rend(); ++rit) {
        if (rit->owns)
          delete rit->hs;
      }
    }

    /**
     * This method should be implemented by the derived class by
     * calling its copy constructor.
     */
    virtual HSView * clone(void) const = 0;

    virtual const ID * arguments(ID id, int * nChildren) = 0;

    /**
     * Returns the number of IDs visible from a view.
     */
    size_t size(void) const {
      size_t s = 0;
      for (typename HSStack::const_iterator cit = stk.begin();
           cit != stk.end(); ++cit) {
        s += cit->hs->size();
      }
      return s;
    }

    /**
     * Begins a local expression creation context.  Expressions
     * created within a begin_local/end_local block exist only within
     * that block and are not visible to other views.
     */
    void begin_local(void) {
      size_t level = stk.size();
      if (level > 7)
        throw std::domain_error("too many nested local contexts");
      stk.push_back(stack_element{new HashedStructure<N>(level), true});
    }

    /**
     * Ends a local expression creation context.  All local
     * expressions are lost.
     */
    void end_local(void) {
      if (stk.size() < 2)
        throw std::logic_error("no local expression context left to close");
      stack_element & top = stk.back();
      if (top.owns)
        delete top.hs;
      stk.pop_back();
    }

    /**
     * Upgrades an expression ID and the IDs it depends on to the next
     * outer scope.  This feature is used to upgrade the final result of
     * many local expression manipulations to the next outer scope.  It
     * must be called from within a begin_local/end_local block.
     */
    ID global(ID id, ID2IDMap * _seen = nullptr) {

      class local_fold : public HashedStructure<N>::Folder {
      public:
        local_fold(HSView * v) : v(v), more_global_view(v->clone()),
                                 level(v->stk.size() - 1) {
          more_global_view->end_local();
        }
        ~local_fold(void) { delete more_global_view; }
        bool filter(ID id, N *) {
          size_t idLevel = local_level(v->hsID(id));
          return idLevel == level;
        }
        ID fold(ID id, N * e, int n, const ID * const args) {
          return more_global_view->replaceArguments(id, e, n, args);
        }
      private:
        HSView * v;
        HSView * more_global_view;
        size_t level;
      };

      local_fold lf(this);
      size_t this_level = local_level(hsID(id));
      if (this_level != stk.size() - 1) {
        if (this_level >= stk.size()) {
          throw std::domain_error(
            "ID to be made global does not belong to this context");
        } else {
          // ID is already "more global".  This may happen as a side
          // effect of simplifications in apply.
          return id;
        }
      }
      ID fid = stk.back().hs->fold(this, lf, id, _seen);
      return fid;
    }

    /**
     * Upgrades expression IDs and the IDs they depend on to the next
     * outer scope, returning the upgraded IDs via the input vector.
     * This feature is used to upgrade the final result of many
     * local expression manipulations to the next outer scope.  It
     * must be called from within a begin_local/end_local block.
     */
    void global(std::vector<ID> & ids, ID2IDMap * _seen = nullptr) {
      ID2IDMap _local;
      ID2IDMap * seen = _seen == nullptr ? &_local : _seen;
      for (std::vector<ID>::iterator it = ids.begin(); it != ids.end(); it++)
	*it = global(*it, seen);
    }

    /**
     * Keeps an ID and those it depends on from being removed via clean.
     * This operation is not thread-safe and does not prevent IDs from
     * being removed as a result of calling end_local.
     */
    void keep(ID id) {
      size_t level = local_level(id);
      stk.at(level).hs->keep(this, id);
    }

    /**
     * Keeps IDs and those they depend on from being removed via clean.
     * This operation is not thread-safe and does not prevent IDs from
     * being removed as a result of calling end_local.
     */
    void keep(std::vector<ID> const & ids) {
      std::vector< std::vector<ID> > bins(stk.size(), std::vector<ID>());
      for (std::vector<ID>::const_iterator it = ids.begin(); it != ids.end(); it++) {
        size_t level = local_level(*it);
        bins.at(level).push_back(*it);
      }
      for (size_t level = stk.size(); level != 0;) {
        --level;
        if (!bins.at(level).empty())
          stk.at(level).hs->keep(this, bins.at(level));
      }
    }

    /**
     * Cleans the current expression context.
     */
    void clean(void) {
      stk.back().hs->clean();
    }

  protected:

    virtual ID replaceArguments(ID id, const N * const e, int n, const ID * const args) = 0;

    virtual ID hsID(ID id) = 0;

    bool exists(N * n) const {
      for (typename HSStack::const_reverse_iterator rit = stk.rbegin();
           rit != stk.rend(); ++rit) {
        HashedStructure<N> * hs = rit->hs;
        ID id;
        if (hs->exists(n, id))
          return true;
      }
      return false;
    }

    ID add(N * n, bool * _exists) {
      for (typename HSStack::const_reverse_iterator rit = stk.rbegin();
           rit != stk.rend(); ++rit) {
        ID rv;
        if (rit->hs->exists(n, rv)) {
          if (_exists)
            *_exists = true;
          return rv;
        }
      }
      return stk.back().hs->add(n, _exists);
    }

    N * get(ID id) {
      size_t level = local_level(id);
      return stk.at(level).hs->get(id);
    }

    HashedStructure<N> * relevantHS(ID id) {
      size_t level = local_level(id);
      return stk.at(level).hs;
    }

  private:

    HSStack stk;
    HSManager * man;

  }; // HSView

}; // HSManager


const uintptr_t NMASK_PTR = 1;
const uintptr_t MASK_PTR = ~NMASK_PTR;

namespace {

  template <class N>
  inline bool KEEP_SET(N * x) {
    return (reinterpret_cast<uintptr_t>(x) & NMASK_PTR);
  }

  template <class N>
  inline void SET_KEEP(N * & x) {
    x = reinterpret_cast<N *>(reinterpret_cast<uintptr_t>(x) | NMASK_PTR);
  }

  template <class N>
  inline N * PTR(N * x) {
    return (reinterpret_cast<N *>(reinterpret_cast<uintptr_t>(x) & MASK_PTR));
  }

} // anonymous namespace


template<typename N>
class HashedStructure {

public:

  explicit HashedStructure(size_t level = 0) : level(level) {}

  ~HashedStructure(void) {
    for (unsigned int i = 0; i < id2n.size(); ++i)
      if (PTR(id2n[i]) != 0)
        delete PTR(id2n[i]);
  }

  bool exists(N * node, ID & id) const {
    typename NMap::const_iterator it = n2id.find(node);
    bool rv = it != n2id.end();
    if (rv)
      id = add_level(it->second, level);
    return rv;
  }

  ID add(N * node, bool * _exists = nullptr) {
    typename NMap::const_iterator it = n2id.find(node);
    if (it != n2id.end()) {
      if (_exists)
        *_exists = true;
      return it->second;
    }
    if (_exists)
      *_exists = false;
    ID id = id2n.size();
    n2id.insert(typename NMap::value_type(node,id));
    id2n.push_back(node);
    return add_level(id, level);
  }

  N * get(ID id) const {
    return PTR(id2n.at(id & ~MASK_LOCAL));
  }

  size_t size(void) const {
    return n2id.size();
  }

  class Folder {
  public:
    virtual bool filter(ID id, N * e) = 0;
    virtual ID fold(ID id, N * e, int n, const ID * const args) = 0;
  };

#if 0
  ID fold(typename HSManager<N>::HSView * v, HashedStructure<N>::Folder & f,
          ID id, ID2IDMap * _seen = nullptr) {

    /* Folding is a post-order traversal of the DAG performed with two stacks.
     * The former (preStack) is used to get the nodes in DFS pre-order.
     * The second stack (evalStack) is used to reverse that order and reduce
     * eagerly.
     */
    ID2IDMap _local;
    ID2IDMap & seen = _seen == nullptr ? _local : *_seen;
    std::vector<ID> preStack{id};
    std::vector<fold_stack_elem> evalStack;
    std::vector<ID> argsMod(4);
    fold_helper pushOrEval(evalStack, seen, argsMod, v, f);

    while (!preStack.empty()) {
      ID curr = preStack.back();
      preStack.pop_back();
      typename ID2IDMap::iterator it = seen.find(curr);
      if (it != seen.end()) { // folded node
        pushOrEval(it->second);
      } else {
        ID nid = curr;
        int nArgs;
        const ID * const args = v->arguments(curr, &nArgs);
        if (nArgs > 0) { // unfolded internal node
          if (nArgs > argsMod.size())
            argsMod.reserve(nArgs);
          for (int i = nArgs; i != 0;) {
            --i;
            preStack.push_back(args[i]);
          }
          evalStack.push_back({curr, nArgs, 0});
        } else { // unfolded leaf
          ID hsID = v->hsID(curr);
          N * node = v->get(hsID);
          assert(node != nullptr);
          if (f.filter(curr, node))
            nid = f.fold(curr, node, 0, nullptr);
          seen.insert(ID2IDMap::value_type(curr, nid));
          pushOrEval(nid);
        }
      }
    }
    return evalStack.back().id;
  }
#endif
  ID fold(typename HSManager<N>::HSView * v, HashedStructure<N>::Folder & f,
          ID id, ID2IDMap * _seen = nullptr) {
    ID2IDMap _local;
    ID2IDMap * seen = _seen == 0 ? &_local : _seen;
    return _fold(v, f, id, seen);
  }

  void fold(typename HSManager<N>::HSView * v, HashedStructure<N>::Folder & f,
            std::vector<ID> & ids) {

    /* Folding is a post-order traversal of the DAG performed with two stacks.
     * The former (preStack) is used to get the nodes in DFS pre-order.
     * The second stack (evalStack) is used to reverse that order and reduce
     * eagerly.
     */
    ID2IDMap seen;
    std::vector<ID> preStack;
    std::vector<fold_stack_elem> evalStack;
    std::vector<ID> argsMod(4);
    fold_helper pushOrEval(evalStack, seen, argsMod, v, f);

    for (std::vector<ID>::iterator iit = ids.begin(); iit != ids.end(); ++iit) {
      preStack.push_back(*iit);

      while (!preStack.empty()) {
        ID curr = preStack.back();
        preStack.pop_back();
        typename ID2IDMap::iterator it = seen.find(curr);
        if (it != seen.end()) { // folded node
          pushOrEval(it->second);
        } else {
          ID nid = curr;
          int nArgs;
          const ID * const args = v->arguments(curr, &nArgs);
          if (nArgs > 0) { // unfolded internal node
            if (nArgs > (int) argsMod.size())
              argsMod.reserve(nArgs);
            for (int i = nArgs; i != 0;) {
              --i;
              preStack.push_back(args[i]);
            }
            evalStack.push_back({curr, nArgs, 0});
          } else { // unfolded leaf
            ID hsID = v->hsID(curr);
            N * node = v->get(hsID);
            assert(node != nullptr);
            if (f.filter(curr, node))
              nid = f.fold(curr, node, 0, nullptr);
            seen.insert(ID2IDMap::value_type(curr, nid));
            pushOrEval(nid);
          }
        }
      }
      *iit = evalStack.back().id;
      evalStack.pop_back();
    }
  }

  void keep(typename HSManager<N>::HSView * v, ID id) {
    keep_fold kfold(v, this);
    fold(v, kfold, id);
  }

  void keep(typename HSManager<N>::HSView * v, const std::vector<ID> & ids) {
    ID2IDMap seen;
    keep_fold kfold(v, this);
    for (std::vector<ID>::const_iterator it = ids.begin(); it != ids.end(); it++)
      fold(v, kfold, *it, &seen);
  }

  void clean(void) {
    for (typename IDMap::iterator it = id2n.begin(); it != id2n.end(); ++it) {
      if (!KEEP_SET(*it)) {
        n2id.erase(n2id.find(PTR(*it)));
        delete *it;
        *it = nullptr;
      }
    }
  }

private:

  typedef std::unordered_map<N *, ID, typename N::hash, typename N::equal> NMap;
  typedef std::vector<N *> IDMap;

  /**
   * Field nargs records the number of arguments still needed to fold the
   * topmost yet unfolded ID at this level or below.  So, an unfolded node has
   * its number of arguments as nargs, its last argument has one minus that
   * number and so on.  When finally the first argument arrives, the nargs
   * field at the top is 1.
   * Field distance gives the distance from the unfolded node below.
   */
  struct fold_stack_elem {
    ID id;
    int nargs;
    int distance;
  };

  size_t level;
  NMap n2id;
  IDMap id2n;

  class fold_helper {
  public:
    fold_helper(std::vector<fold_stack_elem> & evalStack,
                ID2IDMap & seen, std::vector<ID> & argsMod,
                typename HSManager<N>::HSView * v,
                HashedStructure<N>::Folder & f)
      : evalStack(evalStack), seen(seen), argsMod(argsMod),
        v(v), f(f) {}
    void operator()(ID nid) {
      int topArgs;
      while (!evalStack.empty() && (topArgs = evalStack.back().nargs) == 1) {
        // This is the last missing argument: evaluate.
        while (evalStack.back().distance != 0) {
          argsMod[evalStack.back().distance -1] = evalStack.back().id;
          evalStack.pop_back();
        }
        int nargs = evalStack.back().nargs;
        argsMod[nargs - 1] = nid;
        ID id = evalStack.back().id;
        evalStack.pop_back();
        ID hsID = v->hsID(id);
        N * node = v->get(hsID);
        nid = id;
        if (f.filter(id, node)) {
          assert(nargs <= (int) argsMod.capacity());
          nid = f.fold(id, node, nargs, argsMod.data());
        }
        seen.insert(ID2IDMap::value_type(id, nid));
      }

      if (evalStack.empty()) {
        evalStack.push_back({nid, 0, 0});
      } else {
        int distance = evalStack.back().distance + 1;
        evalStack.push_back({nid, topArgs - 1, distance});
      }
    }
  private:
    std::vector<fold_stack_elem> & evalStack;
    ID2IDMap & seen;
    std::vector<ID> & argsMod;
    typename HSManager<N>::HSView * v;
    HashedStructure<N>::Folder & f;
  };

  ID _fold(typename HSManager<N>::HSView * v, HashedStructure<N>::Folder & f, ID id, ID2IDMap * seen) {
    // obtain HS part of ID
    typename ID2IDMap::iterator it = seen->find(id);
    if (it != seen->end())
      return it->second;
    else {
      // not yet seen
      ID __argsm[4];
      ID * _argsm = __argsm;
      int nArgs;
      const ID * const args = v->arguments(id, &nArgs);
      if (nArgs > 4)
        _argsm = new ID[nArgs];
      // preorder traversal: process arguments first
      for (int i = 0; i < nArgs; ++i)
        _argsm[i] = _fold(v, f, args[i], seen);
      // now handle this node
      volatile ID hsID = v->hsID(id);
      N * n = v->get(hsID);
      ID nid = id;
      // call folding function on this node with modified arguments
      if (f.filter(id, n))
        nid = f.fold(id, n, nArgs, _argsm);
      if (nArgs > 4)
        delete[] _argsm;
      // now it's been seen and processed
      seen->insert(ID2IDMap::value_type(id, nid));
      return nid;
    }
  }

  class keep_fold : public Folder {
  public:
    keep_fold(typename HSManager<N>::HSView * vi, HashedStructure<N> * hst)
      : v(vi), hs(hst) {}

    bool filter(ID id, N *) {
      id = v->hsID(id);
      size_t level = local_level(id);
      return !KEEP_SET(v->stk.at(level).hs->id2n.at(remove_level(id)));
    }

    ID fold(ID id, N *, int, ID const * const) {
      id = v->hsID(id);
      size_t level = local_level(id);
      SET_KEEP(v->stk.at(level).hs->id2n.at(remove_level(id)));
      return id;
    }

  private:
    typename HSManager<N>::HSView * v;
    HashedStructure<N> * hs;

  }; // keep_fold

}; // HashedStructure

#endif
