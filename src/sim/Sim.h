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

#ifndef _Sim_
#define _Sim__

/** @file Sim.h */

#include<vector>
#include<list>
#include<unordered_map>

#include "Expr.h"
#include "AIG.h"
#include "Model.h"

namespace Sim {

  /**
   * Defines the call back function object which retrieves the state
   */
  class StateFunctor {
  public:
    virtual bool operator()(std::vector<char>& state) = 0;
  };

  class StateFunctor64 {
  public:
    virtual bool operator()(std::vector<uint64_t>::const_iterator stateBegin,
                            std::vector<uint64_t>::const_iterator stateEnd) = 0;
  };

  class NodeValuesFunctor64 {
  public:
    virtual bool operator()(std::vector<uint64_t>& nodeValues) = 0;
    virtual void indexToIDMap(std::vector<ID>& indexToID) = 0;
  };

  /**
   * Defines the call back function object which retrieves the state and
   * generates simulation input values
   */
  class StateAndInputsFunctor {
  public:
    virtual bool operator()(std::vector<char>& state,
        std::vector<char>& inputs) = 0;
  };

  class StateAndInputsFunctor64 {
  public:
    virtual bool operator()(std::vector<uint64_t>::const_iterator stateBegin,
                            std::vector<uint64_t>::const_iterator stateEnd,
                            std::vector<uint64_t>::iterator inputsBegin,
                            std::vector<uint64_t>::iterator inputsEnd) = 0;
  };

  class NodeValuesAndInputsFunctor64 {
  public:
    virtual bool operator()(std::vector<uint64_t>& nodeValues,
                            std::vector<uint64_t>::iterator inputsBegin,
                            std::vector<uint64_t>::iterator inputsEnd) = 0;
    virtual void indexToIDMap(std::vector<ID>& indexToID) = 0;
  };


  class OutputsFunctor64 {
  public:
    virtual void operator()(std::vector<uint64_t>& outputValues)= 0;
  };

}

namespace {

  //class DefaultOutputsFunctor64 : public OutputsFunctor64 {
  class DefaultOutputsFunctor64 : public Sim::OutputsFunctor64 {
    public:
      void operator()(std::vector<uint64_t>& outputValues) { }
  };

  DefaultOutputsFunctor64 empty;

}

namespace Sim {

  /**
   * Perform sequential random simulation and call the function func to pass
   * the initial state, and the current state after every clock cycle
   */
  void sequentialSimulateRandom(Model& model, unsigned numCycles,
      StateFunctor& func);
  void sequentialSimulateRandom64(Model& model, unsigned numCycles,
      StateFunctor64& func, OutputsFunctor64& outFunc = empty);
  void sequentialSimulateRandom64(Model& model, unsigned numCycles,
      NodeValuesFunctor64& func);

  /**
   * Perform sequential simulation. The function func is first called to pass
   * the initial state and get the simulation input values. It is then called
   * after every clock cycle to pass the current state and get the new
   * simulation input values
   */
  void sequentialSimulate(Model& model, unsigned numCycles,
      StateAndInputsFunctor& func);
  void sequentialSimulate64(Model& model, unsigned numCycles,
      StateAndInputsFunctor64& func, OutputsFunctor64& outFunc = empty);
  void sequentialSimulate64(Model& model, unsigned numCycles,
      NodeValuesAndInputsFunctor64& func);
  
  /**
   * Perform random simulation of the given AIG
   * Output: nodeValues: contains the value of each of the AIG nodes
   */
  void randomSimulate(Model& model, Opt::AIG& aig,
      Opt::IDRefMap& aigRefOfId, std::vector<char>& nodeValues);
  //void randomSimulate64(Opt::AIG& aig, std::vector<uint64_t>& nodeValues, std::vector<Opt::NodeIndex>& liveNodes);
  void randomSimulate64(const Opt::AIG& aig, std::vector<uint64_t>& nodeValues);
  /**
   * Perform simulation of the given AIG
   * Input: inputValues: the input simulation vector
   * Output: nodeValues: contains the value of each of the AIG nodes
   */
  void simulate(Model& model, Opt::AIG& aig, Opt::IDRefMap& aigRefOfId,
      std::vector<char>& nodeValues, std::vector<char>& inputValues);
  //void simulate64(Opt::AIG& aig, std::vector<uint64_t>& nodeValues,
  //    std::vector<uint64_t>& inputValues);

  //void simulateAig64(const Opt::AIG& aig, std::vector<uint64_t>& nodeValues, std::vector<Opt::NodeIndex>& liveNodes);
  void simulateAig64(const Opt::AIG& aig, std::vector<uint64_t>& nodeValues);
  void simulateAig64(const Opt::AIG& aig, std::vector<uint64_t>& nodeValues,
      std::vector<Opt::NodeIndex>& relevantIndices);
}

#endif
