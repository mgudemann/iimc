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

#ifndef _ThreeValuedSimulation_
#define _ThreeValuedSimulation_

/** @file ThreeValuedSimulation.h */

#include "AIG.h"
#include "AIGAttachment.h"
#include "Expr.h"

#include <vector>
#include <unordered_map>

namespace ThreeValued {

  // Encoding chosen to speed up tv_and and tv_not.
  enum TV : unsigned char { TVFalse=0, TVTrue=3, TVX=1 };
  std::ostream & operator<<(std::ostream & os, TV t);
  typedef std::unordered_map<ID, TV> Map;

  class PackedTvVector;
  typedef std::vector<TV> TVvec;
  typedef std::vector<PackedTvVector> vecSeq;

  inline TV tv_not(TV tv) {
    return (TV) (((~(unsigned char) tv & 2)>> 1) | ((~(unsigned char) tv & 1)<<1));
  }

  inline TV tv_and (TV tv1, TV tv2) {
    return (TV) ((unsigned char) tv1 & (unsigned char) tv2);
  }

#if 0
  inline TV tv_not(TV tv) {
    switch (tv) {
    case TVFalse:
      return TVTrue;
    case TVTrue:
      return TVFalse;
    default:
      return TVX;
    }
  }

  inline TV tv_and(TV tv1, TV tv2) {
    if (tv1 == TVFalse || tv2 == TVFalse)
      return TVFalse;
    if (tv1 == TVTrue)
      return tv2;
    if (tv2 == TVTrue)
      return tv1;
    return TVX;
  }
#endif

  inline TV tv_ite(TV c, TV a, TV b) {
    if (c == TVTrue) return a;
    if (c == TVFalse) return b;
    if (a == b) return a;
    return TVX;
  }

  class Folder : public Expr::Manager::View::Folder {
  public:
    Folder(Expr::Manager::View & v, Map & map) : Expr::Manager::View::Folder(v), map(map) {
      map.insert(Map::value_type(v.btrue(), TVTrue));
      map.insert(Map::value_type(v.bfalse(), TVFalse));
    }
    virtual bool filter(ID id) {
      return (map.find(id) == map.end());
    }
    virtual ID fold(ID id, int n, const ID * const args) {
      TV rv;
      switch (view().op(id)) {
      case Expr::True:
      case Expr::Var: {
        Map::const_iterator it = map.find(id);
        rv = it != map.end() ? it->second : TVX;
        break;
      }
      case Expr::Not: {
        Map::const_iterator it = map.find(args[0]);
        rv = tv_not(it->second);
        break;
      }
      case Expr::And: {
        assert (n == 2);
        Map::const_iterator it0 = map.find(args[0]);
        Map::const_iterator it1 = map.find(args[1]);
        rv = tv_and(it0->second, it1->second);
        if (rv == TVX) mux(id, n, args, rv);
        break;
      }
      default:
        assert (false);
      }
      map.insert(Map::value_type(id, rv));
      return id;
    }
  private:
    Map & map;
    void mux(ID, int n, const ID * const args, TV & rv) {
      assert (n == 2);
      if (view().op(args[0]) != Expr::Not) return;
      if (view().op(args[1]) != Expr::Not) return;
      ID l = view().apply(Expr::Not, args[0]);
      if (view().op(l) != Expr::And) return;
      ID r = view().apply(Expr::Not, args[1]);
      if (view().op(r) != Expr::And) return;
      const ID * const argsl = view().arguments(l, &n);
      assert (n == 2);
      const ID * const argsr = view().arguments(r, &n);
      assert (n == 2);
      ID a, b, c;
      if (argsl[0] == view().apply(Expr::Not, argsr[0])) {
        a = argsl[1];
        b = argsr[1];
        c = argsl[0];
      }
      else if (argsl[0] == view().apply(Expr::Not, argsr[1])) {
        a = argsl[1];
        b = argsr[0];
        c = argsl[0];
      }
      else if (argsl[1] == view().apply(Expr::Not, argsr[0])) {
        a = argsl[0];
        b = argsr[1];
        c = argsl[1];
      }
      else if (argsl[1] == view().apply(Expr::Not, argsr[1])) {
        a = argsl[0];
        b = argsr[0];
        c = argsl[1];
      }
      else return;
      if (view().op(c) == Expr::Not) {
        ID t = a;
        a = b;
        b = t;
        c = view().apply(Expr::Not, c);
      }
      TV tva = map.find(a)->second, 
         tvb = map.find(b)->second, 
         tvc = map.find(c)->second;
      rv = tv_not(tv_ite(tvc, tva, tvb));
      return;
    }
  };

  inline bool mux(const Opt::AIG & aig, unsigned i, std::vector<TV> & tvs) {
    Opt::NodeRef fanin1 = aig[i][0];
    Opt::NodeRef fanin2 = aig[i][1];
    if (!Opt::isNot(fanin1)) return false;
    if (!Opt::isNot(fanin2)) return false;
    Opt::NodeIndex fanin1index = Opt::indexOf(fanin1);
    if (aig[fanin1index].isVar()) return false;
    Opt::NodeIndex fanin2index = Opt::indexOf(fanin2);
    if (aig[fanin2index].isVar()) return false;
    const Opt::AIGNode & argsl = aig[fanin1index];
    const Opt::AIGNode & argsr = aig[fanin2index];
    Opt::NodeRef a, b, c;
    if (argsl[0] == Opt::invert(argsr[0])) {
      a = argsl[1];
      b = argsr[1];
      c = argsl[0];
    }
    else if (argsl[0] == Opt::invert(argsr[1])) {
      a = argsl[1];
      b = argsr[0];
      c = argsl[0];
    }
    else if (argsl[1] == Opt::invert(argsr[0])) {
      a = argsl[0];
      b = argsr[1];
      c = argsl[1];
    }
    else if (argsl[1] == Opt::invert(argsr[1])) {
      a = argsl[0];
      b = argsr[0];
      c = argsl[1];
    }
    else return false;
    TV tva = Opt::isNot(a) ? tv_not(tvs[UIGET(Opt::indexOf(a))]) :
                             tvs[UIGET(Opt::indexOf(a))],
       tvb = Opt::isNot(b) ? tv_not(tvs[UIGET(Opt::indexOf(b))]) :
                             tvs[UIGET(Opt::indexOf(b))],
       tvc = Opt::isNot(c) ? tv_not(tvs[UIGET(Opt::indexOf(c))]) :
                             tvs[UIGET(Opt::indexOf(c))];
    tvs[i] = tv_not(tv_ite(tvc, tva, tvb));
    return true;
  }

  inline void simulate(const Opt::AIG & aig, std::vector<TV> & tvs) {
    for (unsigned i = aig.numInputs() + aig.numStateVars() + 1; i < aig.size(); ++i) {
      Opt::NodeRef fanin1 = aig[i][0];
      Opt::NodeRef fanin2 = aig[i][1];
      TV fanin1Val = Opt::isNot(fanin1) ? tv_not(tvs[UIGET(Opt::indexOf(fanin1))]) : 
                                          tvs[UIGET(Opt::indexOf(fanin1))];
      TV fanin2Val = Opt::isNot(fanin2) ? tv_not(tvs[UIGET(Opt::indexOf(fanin2))]) : 
                                          tvs[UIGET(Opt::indexOf(fanin2))];

      tvs[i] = tv_and(fanin1Val, fanin2Val);
      if (tvs[i] == TVX) mux(aig, i, tvs);
    }

  }

  /*
   * AIG-based three valued simulator
   */
  class AIGTVSim {
    public:
      AIGTVSim(const AIGAttachment * aat);

      /*
       * Reset the latch values according to the passed in vector
       */
      void reset(Expr::Manager::View & view, const std::vector<ID> & init);

      /*
       * Simulate for one cycle
       */
      void step();

      std::vector<TV>::iterator inputBegin();
      std::vector<TV>::iterator inputEnd();
      std::vector<TV>::iterator latchBegin();
      std::vector<TV>::iterator latchEnd();

      /*
       * Return a vector with the next-state values
       */
      const std::vector<TV> & getNSValues() const;

      /*
       * Return a vector with the output values
       */
      const std::vector<TV> & getOutputValues() const;


    private:
      void simulate();

      const AIGAttachment * aat;
      const Opt::AIG & aig;
      std::vector<TV> tvs;
      std::vector<char> isMux;
      const std::vector<TV>::iterator _inputBegin, _inputEnd, 
                                      _latchBegin, _latchEnd;
      std::vector<TV> nsValues;
      std::vector<TV> outputValues;
  };


  /** Brie: Better than trie.  (For this application.)
   *  This class manages insertion and searches in a simulation lasso. */
  class BrieTV {

  public:

    BrieTV(vecSeq & l) : lasso(l) {}

    // Add vector to lasso.
    void insert(PackedTvVector const & key);

    // Return an iterator to key in lasso if present;
    // cend() iterator if not present.
    vecSeq::const_iterator find(PackedTvVector const & key) const;

  private:
    typedef unsigned long hval;
    typedef std::pair<hval,TVvec::size_type> mapval;
    typedef std::unordered_multimap<hval,TVvec::size_type> map;

    /** Hash function for vectors of TV. */
    hval hash(TVvec const & v) const
    {
      hval h = 0;
      for (TVvec::const_iterator it = v.begin(); it != v.end(); ++it) {
        h ^= (hval) *it;
        h *= 0x9e3779b9;
      }
      return h;
    }

    vecSeq & lasso;
    map m;
  };


  /** Store simulation vectors in packed form. */
  class PackedTvVector {
  public:
    typedef size_t size_type;
    /**
     * Proxy classes are used to allow PackedTvVector to have operators [] that work for both
     * read and write access and hide the details of packing and unpacking.
     */
    class Proxy {
      friend class PackedTvVector;
    public:
      Proxy & operator=(TV val);
      Proxy & operator=(Proxy const & rhs);
      operator TV() const { return value; }
    private:
      Proxy(PackedTvVector & r, size_type i) : ref(r), index(i), value(r.at(i)) {}
      PackedTvVector & ref;
      size_type index;
      TV value;
    };
    class ProxyConst {
      friend class PackedTvVector;
    public:
      operator TV() const { return value; }
    private:
      ProxyConst(PackedTvVector const & r, size_type i) : ref(r), index(i), value(r.at(i)) {}
      PackedTvVector const & ref;
      size_type index;
      TV value;
    };
    PackedTvVector(size_type vs);
    PackedTvVector(std::vector<TV> const & v);
    PackedTvVector(PackedTvVector const & from);
    PackedTvVector & operator=(PackedTvVector const & rhs);
    Proxy operator[](size_type i) { return Proxy(*this, i); }
    ProxyConst operator[](size_type i) const { return ProxyConst(*this, i); }
    TV at(size_type i) const;
    unsigned long hash(void) const { return hashv; }
    void set(size_type i, TV val);
    size_type size(void) const { return usize; }
    void unpack(std::vector<TV> & v) const;
  private:
    typedef unsigned long storage_t;
    friend bool operator==(PackedTvVector const & a, PackedTvVector const & b);
    static const size_t packing_ratio = sizeof(storage_t) * 4;
    size_type findWord(size_type i) const { return i / packing_ratio; }
    size_type findShift(size_type i) const { return (i % packing_ratio) * 2; }
    size_type usize;
    std::vector<storage_t> data;
    unsigned long hashv;
  };


  /** Use ternary simulation to compute the values
   *  of the autonomous signals. */
  vecSeq::size_type computeLasso(
    Expr::Manager::View & ev,
    std::vector<ID> const & init,
    std::vector<ID> const & outputFns,
    AIGAttachment const * aat,
    vecSeq & lasso,
    vecSeq & outputValues,
    Options::Verbosity verbosity,
    bool allowWidening = true,
    int * pconclusion = 0,
    Model::Mode mode = Model::mIC3,
    unsigned int * pfirstNonzero = 0,
    bool * pwidened = 0,
    int finalTime = -1);
}

#endif
