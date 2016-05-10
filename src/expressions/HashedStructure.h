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

#ifndef _HashedStructure_
#define _HashedStructure_

/** @file HashedStructure.h */

#ifdef HAVE_CONFIG_H
#include "config.h"
#endif

#if HAVE_INTTYPES_H != 1
#error "standard integer types not available."
#endif

#include <cinttypes>

#include <assert.h>
#include <iostream>
#include <unordered_map>
#include <unordered_set>
#include <vector>

#ifdef MTHREADS
#include "tbb/concurrent_hash_map.h"
#include "tbb/concurrent_vector.h"
#include "tbb/tbb_allocator.h"
#endif

typedef uint64_t ID;
const uint64_t MASK_LOCAL = (static_cast<uint64_t>(1) << 47);

template <class N> class HashedStructure;
typedef std::unordered_map<ID, ID> ID2IDMap;

template <class N>
class HSManager {
public:

  class HSView {
    friend class HashedStructure<N>;
  public:
    HSView(HSManager<N> * man) {
      assert (man != 0);
      this->man = man;
      local = new HashedStructure<N>(true, man->global);
      mode = Global;
    }
    ~HSView() {
      delete local;
    }

    virtual const ID * arguments(ID id, int * nChildren) = 0;

    /**
     * Begins a thread-local expression creation context.  Expressions
     * created within a begin_local/end_local block exist only within
     * that block and are not visible to other views.
     */
    void begin_local() {
      assert (mode == Global);
      mode = Local; 
    }

    /**
     * Upgrades an expression ID and the IDs it depends on to the global
     * scope.  This feature is used to upgrade the final result of many
     * thread-local expression manipulations to the global scope.  It
     * must be called from within a begin_local/end_local block.
     */
    ID global(ID id, ID2IDMap * _seen = 0) {
      assert (mode == Local);

      class local_fold : public HashedStructure<N>::Folder {
      public:
        local_fold(HSView * v) { this->v = v; }
        virtual bool filter(ID id, N * e) {
          return (MASK_LOCAL & v->hsID(id));
        }
        virtual ID fold(ID id, N * e, int n, const ID * const args) {
          return v->replaceArguments(id, e, n, args);
        }
      private:
        HSView * v;
      };

      // 1. switch to Global mode
      Mode oldMode = mode;
      mode = Global;
      // 2. fold over the partially local structure
      local_fold lf(this);
      ID gid = local->fold(this, lf, id, _seen);
      // 3. restore mode
      mode = oldMode;

      return gid;
    }

    /**
     * Upgrades expression IDs and the IDs they depend on to the
     * global scope, returning the upgraded IDs via the input vector.
     * This feature is used to upgrade the final result of many
     * thread-local expression manipulations to the global scope.  It
     * must be called from within a begin_local/end_local block.
     */
    void global(std::vector<ID> & ids, ID2IDMap * _seen = 0) {
      ID2IDMap _local;
      ID2IDMap * seen = _seen == 0 ? &_local : _seen;
      for (std::vector<ID>::iterator it = ids.begin(); it != ids.end(); it++)
	*it = global(*it, seen);
    }

    /**
     * Ends a thread-local expression creation context.  All non-kept
     * local expressions are lost.  If full == true, all local
     * expressions are lost.
     */
    void end_local(bool full = false) {
      assert (mode == Local);
      mode = Global;
      if (full) {
        delete local;
        local = new HashedStructure<N>(true, man->global);
      }
      else
        local->clean();
    }

    /**
     * Keeps an ID and those it depends on from being removed via clean.
     */
    void keep(ID id) {
      if (MASK_LOCAL & id) {
        local->keep(this, id);
      }
      man->global->keep(this, id);
    }

    /**
     * Keeps IDs and those they depend on from being removed via clean.
     */
    void keep(const std::vector<ID> & ids) {
      std::vector<ID> locals, globals;
      for (std::vector<ID>::const_iterator it = ids.begin(); it != ids.end(); it++)
	if (MASK_LOCAL & *it)
	  locals.push_back(*it);
	else
	  globals.push_back(*it);
      if (locals.size() > 0) local->keep(this, locals);
      if (globals.size() > 0) man->global->keep(this, globals);
    }

    /**
     * Cleans the expression context.  If scope is local (via
     * "begin_local"), then only the local context is cleaned.
     */
    void clean() {
      if (mode == Local)
        local->clean();
      else
        man->global->clean();
    }

  protected:
    virtual ID replaceArguments(ID id, const N * const e, int n, const ID * const args) = 0;
    virtual ID hsID(ID id) = 0;

    bool exists(N * e) {
      if (mode == Local)
        return local->exists(e);
      else
        return man->global->exists(e);
    }
    N * get(ID id) {
      return relevantHS(id)->get(id);
    }
    ID add(N * e, bool * _exists = 0) {
      if (mode == Local)
        return local->add(e, _exists);
      else
        return man->global->add(e, _exists);
    }
    HashedStructure<N> * relevantHS(ID id) {
      if (mode == Local || (MASK_LOCAL & id))
        return local;
      else
        return man->global;
    }

  private:
    enum Mode { Global, Local };
    Mode mode;
    HSManager * man;
    HashedStructure<N> * local;
  };

  HSManager() {
    global = new HashedStructure<N>();
  }
  ~HSManager() {
    delete global;
  }

protected:
  HashedStructure<N> * global;
};

const uintptr_t NMASK_PTR = 1;
const uintptr_t MASK_PTR = ~NMASK_PTR;

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

#ifdef MTHREADS
#define _HAS_THREADS 1
#else
#define _HAS_THREADS 0
#endif

template <class N>
class HashedStructure {
public:

  class Folder {
  public:
    virtual bool filter(ID id, N * e) = 0;
    virtual ID fold(ID id, N * e, int n, const ID * const args) = 0;
  };

  HashedStructure(bool local = false, HashedStructure<N> * fallback = 0) : 
    n2id(), id2n(), gid(0), low(0)
#ifdef MTHREADS
    , n2idTS(), id2nTS()
#endif
  {
    this->local = local;
    this->fallback = fallback;
#ifdef MTHREADS
    gidTS = 0;
#endif
  }
  ~HashedStructure() {
    for (unsigned int i = 0; i < id2n.size(); ++i)
      if (PTR(id2n[i]) != 0)
        delete PTR(id2n[i]);
  }

  bool exists(N * node) {
    if (local || !_HAS_THREADS) {
      if (local) {
#ifndef MTHREADS
        typename NMap::const_iterator it = fallback->n2id.find(node);
        if (it != fallback->n2id.end()) return true;
#else
        typename NMapTS::const_accessor a;
        if (fallback->n2idTS.find(a, node)) return true;
#endif
      }
      return n2id.find(node) != n2id.end();
    }
#ifdef MTHREADS
    else {
      typename NMapTS::const_accessor a;
      return n2idTS.find(a, node);
    }
#endif
  }

  ID add(N * node, bool * _exists = 0) {
    assert (node != 0);

    if (local || !_HAS_THREADS) {
      ID id = gid;
      if (local) {
#ifndef MTHREADS
        typename NMap::const_iterator it = fallback->n2id.find(node);
        if (it != fallback->n2id.end()) {
          if (_exists != 0) *_exists = true;
          return it->second;
        }
#else
        typename NMapTS::const_accessor a;
        bool exists = fallback->n2idTS.find(a, node);
        if (exists) {
          if (_exists != 0) *_exists = true;
          return a->second;
        }
#endif
        id |= MASK_LOCAL;
      }

      std::pair<typename NMap::iterator, bool> q = n2id.insert(typename NMap::value_type(node, id));
      if (!q.second) {
        if (_exists != 0) *_exists = true;
        return q.first->second;
      }
      if (_exists != 0) *_exists = false;

      if (id2n.size() == gid)
        id2n.push_back(node);
      else {
        assert (id2n[gid] == 0);
        id2n[gid] = node;
      }
      gid++;

      return id;
    }
#ifdef MTHREADS
    else {
      ID id;
      do {
        id = gidTS;
      } while (gidTS.fetch_and_add(1) != id);

      {
        typename NMapTS::accessor a;
        bool is_new = n2idTS.insert(a, node);
        if (!is_new) {
          if (_exists != 0) *_exists = true;
          return a->second;
        }
        if (_exists != 0) *_exists = false;
        a->second = id;
      }
      while (id2nTS.size() <= id)
        id2nTS.push_back(0);
      id2nTS[id] = node;
    
      return id;
    }
#endif
  }

  N * get(ID id) {
    if (local && !(MASK_LOCAL & id))
      return fallback->get(id);
    id = ~MASK_LOCAL & id;
#ifndef MTHREADS
    return (PTR(id2n[id]));
#else
    return (PTR(local ? id2n[id] : id2nTS[id]));
#endif
  }

  ID fold(typename HSManager<N>::HSView * v, HashedStructure<N>::Folder & f, ID id, ID2IDMap * _seen = 0) {
    ID2IDMap _local;
    ID2IDMap * seen = _seen == 0 ? &_local : _seen;
    return _fold(v, f, id, seen);
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

  // NOT THREAD SAFE, even with MTHREADS
  void clean() {
    bool only_kept = true;
    for (ID i = low; i < gid; ++i ) {
      if (local || !_HAS_THREADS) {
        if (!KEEP_SET(id2n[i])) {
          only_kept = false;
          n2id.erase(n2id.find(PTR(id2n[i])));
          delete id2n[i];
          id2n[i] = 0;
        }
        else if (only_kept)
          low++;
      }
#ifdef MTHREADS
      else {
        if (!KEEP_SET(id2nTS[i])) {
          only_kept = false;
          n2idTS.erase(PTR(id2nTS[i]));
          delete id2nTS[i];
          id2nTS[i] = 0;
        }
        else if (only_kept)
          low++;
      }
#endif
    }
    gid = low;
  }

private:
  typedef std::unordered_map<N *, ID, typename N::hash, typename N::equal> NMap;
  typedef std::vector<N *> IDMap;

  NMap n2id;
  IDMap id2n;

  HashedStructure<N> * fallback;
  bool local;
  ID gid;
  ID low;

#ifdef MTHREADS
  struct HashCompare {
    typename N::hash hashf;
    typename N::equal equalf;
    size_t hash(const N * const & e) const {
      return hashf(e);
    }
    bool equal(const N * const & e1, const N * const & e2) const {
      return equalf(e1, e2);
    }
  };
  typedef tbb::concurrent_hash_map<N *, ID, HashCompare, tbb::tbb_allocator<N *> > NMapTS;
  typedef tbb::concurrent_vector<N *, tbb::tbb_allocator<N *> > IDMapTS;
  NMapTS n2idTS;
  IDMapTS id2nTS;
  tbb::atomic<ID> gidTS;
#endif

  class keep_fold : public Folder {
  public:
    keep_fold(typename HSManager<N>::HSView * vi, HashedStructure<N> * hst) { 
      this->v = vi;
      this->hs = hst;
    }
    virtual bool filter(ID id, N * _e) {
      id = v->hsID(id);
      if (MASK_LOCAL & id) {
	return !KEEP_SET(hs->id2n[~MASK_LOCAL & id]);
      }
      else {
	HashedStructure<N> * ths = hs->local ? hs->fallback : hs;
#ifndef MTHREADS
	return !KEEP_SET(ths->id2n[id]);
#else
	return !KEEP_SET(ths->id2nTS[id]);
#endif
      }
    }
    virtual ID fold(ID id, N * e, int n, const ID * const args) {
      id = v->hsID(id);
      if (MASK_LOCAL & id) {
	SET_KEEP(hs->id2n[~MASK_LOCAL & id]);
      }
      else {
	HashedStructure<N> * ths = hs->local ? hs->fallback : hs;
#ifndef MTHREADS
	SET_KEEP(ths->id2n[id]);
#else
	SET_KEEP(ths->id2nTS[id]);
#endif
      }
      return id;
    }
  private:
    typename HSManager<N>::HSView * v;
    HashedStructure<N> * hs;
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
      N * n = get(hsID);
      if (n == 0) {
        assert (fallback != 0);
        // in global context
        n = fallback->get(hsID);
        assert (n != 0);
      }
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
};

#endif
