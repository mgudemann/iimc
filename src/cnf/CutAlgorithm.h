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

#ifndef CUTALGORITHM_H
#define CUTALGORITHM_H

#include "AIG.h"
#include "Util.h"
#include <unordered_set>

namespace CNF
{

  typedef ::Opt::AIG AIG;
  typedef ::Opt::NodeIndex NodeIndex;

  namespace Private
  {

    template<typename T, typename CostFun>
    void enumerateCut(const AIG& aig, ::std::vector< ::std::vector<T> >& cuts, unsigned k, unsigned b, NodeIndex i, CostFun& cf)
    {
      //std::cout << "Cuts for :" << i << std::endl;
      // if not an input, compute children
      if(!aig[i].isVar() || i == 0) {
        // iterate over input cut pairs
        std::unordered_set<T> cut_set;
        unsigned size_0 = cuts[UIGET(::Opt::indexOf(aig[i][0]))].size();
        unsigned size_1 = cuts[UIGET(::Opt::indexOf(aig[i][1]))].size();
        for(unsigned m = 0; m < size_0; ++m) {
          for(unsigned n = 0; n < size_1; ++n) {
            T output;
            if(merge(aig, i, cuts[UIGET(::Opt::indexOf(aig[i][0]))][m], cuts[UIGET(::Opt::indexOf(aig[i][1]))][n], k, output)) {
            //if(merge(cuts[UIGET(::Opt::indexOf(aig[i][0]))][m], cuts[UIGET(::Opt::indexOf(aig[i][1]))][n], k, output)) {
              // if the merge is successful, add cut to list of cuts
              output.computeCost(aig, cuts, i, cf);
              //cuts[UIGET(i)].push_back(output);
              cut_set.insert(output);
            }
          }
        }
        for(typename std::unordered_set<T>::iterator it = cut_set.begin(); it != cut_set.end(); ++it) {
          cuts[UIGET(i)].push_back(*it);
        }
        // sort the generated list of cuts by their cost
        ::std::sort(cuts[UIGET(i)].begin(), cuts[UIGET(i)].end());
        // if there are more than b cuts by cost, reduce to b cuts
        if(cuts[UIGET(i)].size() > b)
          cuts[UIGET(i)].resize(b);
      }
      assert(aig[i].isVar() || i == 0 || cuts[UIGET(i)].size() > 0);
      // insert trivial cut
      cuts[UIGET(i)].push_back(T(aig, cuts, i, cf));

      // invariant: trivial cut is always last
    }
  } // namespace private

  template<typename T, typename CostFun>
  void enumerateCuts(const AIG& aig, std::vector<std::vector<T> >& cuts, unsigned k, unsigned b, double timeLeft, CostFun& cf)
  {
    //std::cout << "Enumerating cuts k = " << k << ", b = " << b << std::endl;
    // resize the result vector to contain all results
    cuts.resize(aig.size());

    int64_t start_time = Util::get_cpu_time(false);

    // iterate over the AIG producing cuts
    for(::Opt::NodeIndex i = 1; i != aig.size(); ++i) {
      Private::enumerateCut<T, CostFun>(aig, cuts, k, b, i, cf);
      if(timeLeft > 0.0 && (i % 1000) == 0) {
        int64_t end_time = Util::get_cpu_time(false);
        timeLeft -= static_cast<double>(end_time - start_time)/1000000.0;
        start_time = end_time;
        if(timeLeft < 0.0) {
          // if we timed out, reduce k and b to their minimal values
          k = 2;
          b = 1;
          cf.timeout();
        }
      }
    }
  }

  namespace Private
  {
    template<typename T, typename Action>
    void bestCutsInternal(const AIG& aig, std::vector<std::vector<T> >& cuts, const NodeIndex& i, std::set<unsigned>& visited, Action& action)
    {
      //::std::cout << "Starting: " << i << ::std::endl;
      // if node is already visited, skip it
      if(visited.find(UIGET(i)) != visited.end())
        return;

      // if node is an input, skip it
      if(aig[i].isVar() || i == 0)
        return;

      assert(cuts[UIGET(i)].size() > 0);

      // get best cut for this node
      T& bestcut = cuts[UIGET(i)][0];

      // recurse on input cuts
      for(typename T::iterator it = bestcut.begin(); it != bestcut.end(); ++it) {
        bestCutsInternal(aig, cuts, *it, visited, action);
      }

      // call action on the best (0th) cut of each node backward reachable from other cuts or outputs
      action(aig, bestcut, i);

      visited.insert(UIGET(i));
    }
  }

  template<typename T, typename ForwardIterator, typename Action>
  void bestCuts(const AIG& aig, std::vector<std::vector<T> >& cuts, const ForwardIterator& out_begin, const ForwardIterator& out_end, Action& action)
  {
    std::set<unsigned> visited;
    
    for(ForwardIterator i = out_begin; i != out_end; ++i) {
      Private::bestCutsInternal(aig, cuts, *i, visited, action);
    }
  }


  template<typename T>
  double recursiveSelect(const AIG& aig, std::vector<std::vector<T> >& cuts, std::vector<int>& refcount, const NodeIndex& i, const unsigned index)
  {
    assert(i < cuts.size());
    assert(index < cuts[UIGET(i)].size());

    // get the best cut
    T& best = cuts[UIGET(i)][index];

    assert(refcount.size() > i);

    // if node is an input
    if(aig[i].isVar() || i == 0)
      return 0.0;

    double area = best.getCutCost();

    // for all inputs, select them
    for(typename T::const_iterator it = best.begin(); it != best.end(); ++it) {
      if(refcount[UIGET(*it)]++ == 0)
        area += recursiveSelect(aig, cuts, refcount, *it, 0);
    }

    return area;
  }

  template<typename T>
  int recursiveDeselect(const AIG& aig, std::vector<std::vector<T> >& cuts, std::vector<int>& refcount, const NodeIndex& i, const unsigned index)
  {

    assert(i < cuts.size());
    assert(index < cuts[UIGET(i)].size());
    // get the best cut
    T& best = cuts[UIGET(i)][index];

    // ensure that the refcount vector is correct
    assert(refcount.size() > i);

    // if node is an input
    if(aig[i].isVar() || i == 0)
      return 1;

    int maxdepth = 0;

    for(typename T::const_iterator it = best.begin(); it != best.end(); ++it) {
      assert(refcount[UIGET(*it)] > 0);
      refcount[UIGET(*it)]--;
      if(refcount[UIGET(*it)] == 0) {
        int depth = recursiveDeselect(aig, cuts, refcount, *it, 0);
        if(depth > maxdepth)
          maxdepth = depth;
      }
    }
    return maxdepth + 1;
  }

  template<typename T>
  void refineCuts(const AIG& aig, std::vector<std::vector<T> >& cuts, std::vector<int>& refcount, double& timeleft) {
    //int total_depth = 0;
    //int count = 0;
    int64_t start_time = Util::get_cpu_time(false);
    //::Opt::printAIG(aig);
    for(NodeIndex i = 0; i < aig.size(); ++i) {
      // check time left
      if(i % 500 == 0) {
        int64_t curr_time = Util::get_cpu_time(false);
        if(timeleft - (curr_time - start_time)/1000000.0 < 0) {
          std::cout << "TMCNF: Refinement Timeout" << std::endl;
          return;
        }
      }
#if 0
      if(i % 100 == 0) {
        std::cout << "Refining " << i << std::endl;
        std::cout << "Avg depth: " << (float)total_depth / (float)count << std::endl;
        std::cout << "Count: " << count << std::endl;
        total_depth = 0;
        count = 0;
      }
#endif
      // skip inputs
      if(i == 0 || aig[i].isVar())
        continue;

      // get the cut list for a given node
      std::vector<T>& cutlist = cuts[UIGET(i)];

      // if cut is already selected, deselect it first
      if(refcount[UIGET(i)] != 0) {
        // deselect cut
        //total_depth += recursiveDeselect(aig, cuts, refcount, i, 0);
        recursiveDeselect(aig, cuts, refcount, i, 0);
        //count++;
      }


#if 0
      std::cout << "Refcount: ";
      for(unsigned pi = 0; pi < refcount.size(); ++pi)
        std::cout << refcount[pi] << " ";
      std::cout << std::endl;
#endif

      assert(cutlist.size() > 1);

      for(unsigned j = 0; j < cutlist.size() - 1; ++j) {
        // recompute the cost for each cut according which cuts they select
        double area = recursiveSelect(aig, cuts, refcount, i, j);
        recursiveDeselect(aig, cuts, refcount, i, j);
        //total_depth += recursiveDeselect(aig, cuts, refcount, i, j);
        //count++;
        cutlist[j].setCost(area);
      }

      // resort the cuts according to their new costs
      // but don't sort the trivial cut
      std::stable_sort(cutlist.begin(), cutlist.end()-1);

      // update trivial cut's cost
      (cutlist.end()-1)->setCost(cutlist.begin()->getCost());

      // if cut was originally selected, reselect it
      if(refcount[UIGET(i)] != 0) {
        recursiveSelect(aig, cuts, refcount, i, 0);
      }
    }
  }

}

#endif
