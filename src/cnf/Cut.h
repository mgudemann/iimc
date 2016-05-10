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

#ifndef CUT_H
#define CUT_H

#include<set> 
#include<algorithm>
#include<iostream>
#include "AIG.h"
#include "BitTricks.h"

namespace CNF
{
  class Cut;
}

namespace std
{
  template <> void swap(::CNF::Cut& c1, ::CNF::Cut& c2);
}

namespace CNF
{
  class Cut
  {
  public:
    typedef std::set< ::Opt::NodeIndex> set;
    typedef set::iterator iterator;
    typedef set::const_iterator const_iterator;
  protected:
    set inputs;
    unsigned signature;

    void compute_signature()
    {
      signature = 0;
      for(iterator i = begin(); i != end(); ++i) {
        signature |= (1 << UIGET(*i) & (sizeof(unsigned)*8 - 1));
      }
    }
  public:
    // empty cut
    Cut()
    { compute_signature(); }

    // copy an existing cut
    Cut(const Cut& other) : inputs(other.inputs), signature(other.signature)
    { }

    Cut& operator=(const Cut& rhs)
    {
      inputs = rhs.inputs;
      signature = rhs.signature;
      return *this;
    }

    // trivial cut
    Cut(::Opt::NodeIndex i)
    {
      inputs.insert(i);
      compute_signature();
    }

    // new complex cut
    template<typename T>
    Cut(const T& b, const T& e) : inputs(b, e)
    { compute_signature(); }

    // new complex cut
    Cut(set& i) : inputs(i)
    { compute_signature(); }

    // iterate over cut
    const_iterator begin() const
    { return inputs.begin(); }

    // iterate over cut
    const_iterator end() const
    { return inputs.end(); }

    // iterate over cut
    iterator begin()
    { return inputs.begin(); }

    // iterate over cut
    iterator end()
    { return inputs.end(); }

    bool contains(const ::Opt::NodeIndex& i) const
    {
      return inputs.find(i) != inputs.end();
    }

    void erase(const ::Opt::NodeIndex& i)
    { inputs.erase(i); }

    unsigned hash() const
    { return signature; }

    // compare cut use hash as a quick lookup
    bool operator==(const Cut& rhs) const
    {
      // speed lookup
      if(signature != rhs.signature)
        return false;

      return inputs == rhs.inputs;
    }

    bool operator!=(const Cut& rhs) const
    {
      if(signature != rhs.signature)
        return true;

      return inputs != rhs.inputs;
    }

    // test dominance of cut using hash as a quick lookup
    bool dominates(Cut& rhs) const
    {
      if((signature | rhs.signature) != rhs.signature)
        return false;
      
      for(iterator i = begin(); i != end(); ++i) {
        if(rhs.inputs.find(*i) == rhs.end())
          return false;
      }
      return true;
    }

    unsigned size() const
    {
      return inputs.size();
    }
  private:


    template<typename T>
    void enumMembers(const ::Opt::AIG& aig, T& s, ::Opt::NodeIndex i)
    {
      // end recursion
      if(s.find(i) != s.end())
        return;

      s.insert(i);

      enumMembers(aig, s, ::Opt::indexOf(aig[i][0]));
      enumMembers(aig, s, ::Opt::indexOf(aig[i][1]));
    }


  public:

    template<typename T>
    void members(const ::Opt::AIG& aig, ::Opt::NodeIndex i, T& s)
    {
      // add all inputs to end recursion
      s.insert(inputs.begin(), inputs.end());
      enumMembers(aig, s, i);
    }

    friend void ::std::swap<Cut>(Cut& c1, Cut& c2);
    friend void merge(const Cut& c1, const Cut& c2, Cut& cout);
    friend bool merge(const Cut& c1, const Cut& c2, unsigned k, Cut& cout);
  };

  // unconditional merge
  void merge(const Cut& c1, const Cut& c2, Cut& cout)
  {
    ::std::set_union(c1.inputs.begin(), c1.inputs.end(), c2.inputs.begin(), c2.inputs.end(), inserter(cout.inputs, cout.inputs.begin()));
  }

  // k-limited merge
  bool merge(const Cut& c1, const Cut& c2, unsigned k, Cut& cout)
  {
    // check signature before merge
    if(Util::count_bits(c1.hash() | c2.hash()) > k) 
      return false;

    ::std::set_union(c1.inputs.begin(), c1.inputs.end(), c2.inputs.begin(), c2.inputs.end(), inserter(cout.inputs, cout.inputs.begin()));
    if(cout.size() > k)
      return false;
    return true;
  }

  namespace Private {

    void find_removal(const ::Opt::AIG& aig,
        ::Opt::NodeIndex i,
        Cut& outcut,
        ::Opt::NodeIndex least,
        std::set< ::Opt::NodeIndex>& visited,
        std::set< ::Opt::NodeIndex>& to_remove)
    {
      // if we've searched past the least (topologically) input, end recursion
      if(i < least)
        return;

      if(visited.find(i) != visited.end())
        return;

      //if(display) std::cout << "visiting: " << i << ": " << ::Opt::indexOf(aig[i][0]) << " " << ::Opt::indexOf(aig[i][1]) << std::endl;

      // if we hit a primary input, end recursion
      if(aig[i].isVar() || i == 0) {
        if(outcut.contains(i))
          visited.insert(i);
        return;
      }

      // recurse adding all contained nodes to visited
      find_removal(aig, ::Opt::indexOf(aig[i][0]), outcut, least, visited, to_remove);
      find_removal(aig, ::Opt::indexOf(aig[i][1]), outcut, least, visited, to_remove);

      // add current node to visited if appropriate
      // also remove any cuts that are completely contained
      if(outcut.contains(i)) {
        if(visited.find(::Opt::indexOf(aig[i][0])) != visited.end() &&
            visited.find(::Opt::indexOf(aig[i][1])) != visited.end()) {
          to_remove.insert(i);
        }
        visited.insert(i);
      } else if(visited.find(::Opt::indexOf(aig[i][0])) != visited.end() &&
          visited.find(::Opt::indexOf(aig[i][1])) != visited.end()) {
        visited.insert(i);
      }
    }

  }

#if 0
  // k-limited merge with reduction
  bool merge(const ::Opt::AIG& aig, ::Opt::NodeIndex i, const Cut& c1, const Cut& c2, unsigned k, Cut& outcut)
  {
    // merge the cuts blindly
    if(!merge(c1,c2,k,outcut))
      return 0;

    // find the least element of the cut
    ::Opt::NodeIndex least = i;
    for(Cut::const_iterator it = outcut.begin(); it != outcut.end(); ++it) {
      if(*it < least)
        least = *it;
    }

    // keep track of nodes that should be later removed and nodes that have been visited
    std::set< ::Opt::NodeIndex> to_remove;
    std::set< ::Opt::NodeIndex> visited;

    // remove all nodes from cut that are completely contained within a smaller cut constructed of all inputs but removed node
    Private::find_removal(aig, i, outcut, least, visited, to_remove);


    // update the cut to remove everything from to_remove
    for(std::set< ::Opt::NodeIndex>::iterator it = to_remove.begin(); it != to_remove.end(); ++it) {
      outcut.erase(*it);
    }

    assert(outcut.size() > 0);

    return outcut.size() <= k;
  }
#endif

  // k-limited merge with reduction
  bool merge(const ::Opt::AIG& aig, ::Opt::NodeIndex i, const Cut& c1, const Cut& c2, unsigned k, Cut& outcut)
  {
    // merge the cuts blindly
    if(!merge(c1,c2,k,outcut))
      return 0;

    /*
    std::cout << "Starting node " << i << ": ";

    std::cout << "[ ";
    for(Cut::const_iterator it = outcut.begin(); it != outcut.end(); ++it) {
      std::cout << *it << " ";
    }
    std::cout << "]" << std::endl;
    */

    // enumerate all member nodes
    std::set< ::Opt::NodeIndex> members;
    outcut.members(aig, i, members);

    std::set< ::Opt::NodeIndex> to_remove;

    // find the least element of the cut
    for(Cut::const_iterator it = outcut.begin(); it != outcut.end(); ++it) {
      if(*it != 0 && !aig[*it].isVar() &&
          members.find(::Opt::indexOf(aig[*it][0])) != members.end() &&
          members.find(::Opt::indexOf(aig[*it][1])) != members.end()) {
        // mark for removal
        to_remove.insert(*it);
      }
    }

    // update the cut to remove everything from to_remove
    for(std::set< ::Opt::NodeIndex>::iterator it = to_remove.begin(); it != to_remove.end(); ++it) {
      outcut.erase(*it);
    }

    /*
    std::cout << "Ending node " << i << ": ";

    std::cout << "[ ";
    for(Cut::const_iterator it = outcut.begin(); it != outcut.end(); ++it) {
      std::cout << *it << " ";
    }
    std::cout << "]" << std::endl;
    */

    assert(outcut.size() > 0);

    return outcut.size() <= k;
  }
} // namespace CNF

namespace std
{
  template <>
  void swap(::CNF::Cut& c1, ::CNF::Cut& c2)
  {
    swap(c1.inputs, c2.inputs);
    swap(c1.signature, c2.signature);
  }

  ostream& operator<<(ostream& ostr, const ::CNF::Cut& c)
  {
    bool first = true;
    ostr << "[";
    for(::CNF::Cut::iterator i = c.begin(); i != c.end(); ++i) {
      if(first) {
        first = false;
      } else {
        ostr << ",";
      }
      ostr << *i;
    }
    ostr << "]";
    return ostr;
  }

  template<>
  struct hash< ::CNF::Cut> : public unary_function< ::CNF::Cut, size_t>
  {
    size_t operator()(const ::CNF::Cut& c) const
    {
      return c.hash();
    }
  };
} // namespace std

#endif
