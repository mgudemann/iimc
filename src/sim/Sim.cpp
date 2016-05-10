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

#include<unordered_map>
#include<vector>

#include "Sim.h"
#include "Expr.h"
#include "AIGAttachment.h"
#include "ExprAttachment.h"
#include "Model.h"
#include "AIG.h"
#include "Random.h"

using namespace std;

namespace {

  /**
   * This is the low-level function that evaluates the AIG node values
   * according to the topological sort
   */
  void simulateAig(Opt::AIG const & aig, vector<char>& nodeValues) {
    for(unsigned i = 1; i < aig.size(); ++i) {
      //Skip nodes that don't have fanins
      if(aig[i].isVar()) continue;
      
      //Lookup value of first fanin
      Opt::NodeRef fanin1 = aig[i][0];
      bool fanin1val = Opt::isNot(fanin1) ?
          !nodeValues[UIGET(Opt::indexOf(aig[i][0]))] :
          nodeValues[UIGET(Opt::indexOf(aig[i][0]))];

      if(!fanin1val) {
        nodeValues[i] = 0;
        continue;
      }

      //Lookup value of second fanin
      Opt::NodeRef fanin2 = aig[i][1];
      bool fanin2val = Opt::isNot(fanin2) ?
          !nodeValues[UIGET(Opt::indexOf(aig[i][1]))] :
          nodeValues[UIGET(Opt::indexOf(aig[i][1]))];

      //Compute the value of the node and add it to the map
      nodeValues[i] = fanin2val;
    }
  }

}

namespace Sim {

  void sequentialSimulateRandom(Model& model, unsigned numCycles,
      StateFunctor& func) {

    class RandomInputs : public StateAndInputsFunctor {
      public:
      RandomInputs(StateFunctor& func) : stateFunc(func) {}
      bool operator()(vector<char>& state, vector<char>& inputs) {
        bool ret = stateFunc(state);
        for(unsigned i = 0; i < inputs.size(); ++i) {
          inputs[i] = Random::randomBool();
        }
        return ret;
      }
      private:
      StateFunctor& stateFunc;
    };

    RandomInputs random(func);

    sequentialSimulate(model, numCycles, random);
  }


  void sequentialSimulate(Model& model, unsigned numCycles,
      StateAndInputsFunctor& func) {

    //Grab the AIG attachment (read-only)
    AIGAttachment const * const aat = (AIGAttachment const *) model.constAttachment(Key::AIG);
    //Create a reference to the AIG from the AIG attachment
    Opt::AIG const & aig = aat->aig;
    //Get the ID to AIG reference
    Opt::IDRefMap const & aigRefOfId = aat->id2ref;

    //Get the ExprAttachment (read-only)
    ExprAttachment const * const eat = (ExprAttachment const *) model.constAttachment(Key::EXPR);
    const vector<ID>& inputs = eat->inputs();
    const vector<ID>& stateVars = eat->stateVars();

    //Create a view of the model
    Expr::Manager::View* modelView = model.newView();

    vector<char> state(stateVars.size());

    vector<char> nodeValues(aig.size());
    //Set the node value for the constant false node
    nodeValues[0] = 0;

    //Keep track of which latches are specified in the initial conditions and
    //which are not
    unordered_set<ID> latchAssigned;

    //Get the initial conditions
    vector<ID> initialConditions = eat->initialConditions();
    //Set the latch values according to the initial conditions
    for(unsigned i = 0; i < initialConditions.size(); ++i) {
      //Check whether it is true or false by checking if it's a Expr::Var or an
      //Expr::Not
      Expr::Op op = modelView->op(initialConditions[i]);
      if(op == Expr::Var) {
        //For AIGER, we should never come here
        cout << "op not Var!" << endl;
        assert(false);
        //Check if the latch references by this initial condition is in the AIG
        Opt::IDRefMap::const_iterator it = aigRefOfId.find(initialConditions[i]);
        if(it != aigRefOfId.end()) {
          //Then it is true
          nodeValues[UIGET(Opt::indexOf(aigRefOfId.at(initialConditions[i])))] =
              1;
          //Mark this latch as assigned
          latchAssigned.insert(initialConditions[i]);
        }
      }
      else {
        assert(op == Expr::Not);
        ID latch = modelView->apply(Expr::Not,initialConditions[i]);
        //Check if the latch references by this initial condition is in the AIG
        Opt::IDRefMap::const_iterator it = aigRefOfId.find(latch);
        if(it != aigRefOfId.end()) {
          nodeValues[UIGET(Opt::indexOf(aigRefOfId.at(latch)))] =
              0;
          latchAssigned.insert(latch);
        }
      }
    }
    delete modelView;

    //Generate random values for latches that have not been initialized
    //if there are some
    if(latchAssigned.size() < stateVars.size()) {
      for(unsigned i = 0; i < stateVars.size(); ++i) {
        //Check if this latch is in the AIG
        Opt::IDRefMap::const_iterator it = aigRefOfId.find(stateVars[i]);
        if(it != aigRefOfId.end()) {
          //Check if this latch has not already been assigned
          if(latchAssigned.find(stateVars[i]) == latchAssigned.end()) {
            //Should never come here for AIGER
            assert(false);
            //If not generate a random value for it
            nodeValues[UIGET(Opt::indexOf(aigRefOfId.at(stateVars[i])))] =
                Random::randomBool();
          }
          //Assign this state
          state[i] = nodeValues[UIGET(Opt::indexOf(aigRefOfId.at(stateVars[i])))];
        }
      }
    }

    vector<char> inputValues(inputs.size());
    //Simulate the circuit for numCycles clock cycles
    for(unsigned cycle = 0; cycle < numCycles; ++cycle) {
      //Call func to pass the current state and get the input values
      bool proceed = func(state, inputValues);
      if(!proceed) break;
      //Assign input values
      for(unsigned i = 0; i < inputs.size(); ++i) {
        //Make sure this input is in the AIG
        Opt::IDRefMap::const_iterator it = aigRefOfId.find(inputs[i]);
        if(it != aigRefOfId.end()) {
          nodeValues[UIGET(Opt::indexOf(aigRefOfId.at(inputs[i])))] =
              inputValues[i];
        }
      }
      //Evaluate node values according to the topological sort
      simulateAig(aig, nodeValues);

      //Update current state values with next state ones if this is not the
      //last cycle
      if(cycle != numCycles - 1) {
        for(unsigned i = 0; i < stateVars.size(); ++i) {
          //Check if this latch is in the AIG
          Opt::IDRefMap::const_iterator it = aigRefOfId.find(stateVars[i]);
          if(it != aigRefOfId.end()) {
            //Get the next state values of this state variable. The next state
            //value might either be a value in nodeValues if it's equal to a node
            //in the AIG, or the negation of a value in nodeValues if it's the
            //negation of a node in the AIG
            Opt::NodeRef nextFn = aigRefOfId.at(eat->nextStateFnOf(stateVars[i]));
            bool val = nodeValues[UIGET(Opt::indexOf(nextFn))];
            if(Opt::isNot(nextFn)) {
              val = !val;
            }
            //Add this to the state vector
            state[i] = val;

            //Assign the value of the latch to the next state value
            nodeValues[UIGET(Opt::indexOf(aigRefOfId.at(stateVars[i])))] = val;
          }
        }
      }
    }
    //Pass the final state reached
    func(state, inputValues);

    model.constRelease(eat);
    model.constRelease(aat);
  }

  void randomSimulate(Model& model, Opt::AIG& aig,
      Opt::IDRefMap& aigRefOfId, vector<char>& nodeValues) {

    ExprAttachment const * const eat = (ExprAttachment const *) model.constAttachment(Key::EXPR);
    int inputLength = eat->inputs().size() + eat->stateVars().size();

    //Create random vectors
    vector<char> randValues(inputLength);
    //Generate random values
    for(int i = 0; i < inputLength; ++i) {
      //randValues[i] = rand() % 2;
      randValues[i] = Random::randomBool();
    }

    simulate(model, aig, aigRefOfId, nodeValues, randValues);

    model.constRelease(eat);
  }

  void simulate(Model& model, Opt::AIG& aig, Opt::IDRefMap& aigRefOfId,
      vector<char>& nodeValues, vector<char>& inputValues) {
    
    //Add the input and state variable values to the map
    ExprAttachment const * const eat = (ExprAttachment const *) model.constAttachment(Key::EXPR);
    const vector<ID>& inputs = eat->inputs();
    const vector<ID>& stateVars = eat->stateVars();

    for(unsigned i = 0; i < inputs.size(); ++i) {
      //Make sure this input is in the AIG
      Opt::IDRefMap::iterator it = aigRefOfId.find(inputs[i]);
      if(it != aigRefOfId.end()) {
        nodeValues[UIGET(Opt::indexOf(it->second))] = inputValues[i];
      }
    }
    for(unsigned i = 0; i < stateVars.size(); ++i) {
      Opt::IDRefMap::iterator it = aigRefOfId.find(stateVars[i]);
      if(it != aigRefOfId.end()) {
        nodeValues[UIGET(Opt::indexOf(it->second))] =
            inputValues[i + inputs.size()];
      }
    }

    //Evaluate node values according to the topological sort
    simulateAig(aig, nodeValues);

    model.constRelease(eat);
  }

  void sequentialSimulateRandom64(Model& model, unsigned numCycles,
      StateFunctor64& func, OutputsFunctor64& outFunc) {

    class RandomInputs : public StateAndInputsFunctor64 {
      public:
      RandomInputs(StateFunctor64& func) : stateFunc(func) {}
      bool operator()(vector<uint64_t>::const_iterator stateBegin,
                      vector<uint64_t>::const_iterator stateEnd,
                      vector<uint64_t>::iterator inputsBegin,
                      vector<uint64_t>::iterator inputsEnd) {
        bool ret = stateFunc(stateBegin, stateEnd);
        for(vector<uint64_t>::iterator it = inputsBegin; it != inputsEnd; ++it) {
          *it = Random::randomUint64();
        }
        return ret;
      }
      private:
      StateFunctor64& stateFunc;
    };

    RandomInputs random(func);

    sequentialSimulate64(model, numCycles, random, outFunc);
  }

  void sequentialSimulateRandom64(Model& model, unsigned numCycles,
      NodeValuesFunctor64& func) {

    class RandomInputs : public NodeValuesAndInputsFunctor64 {
      public:
      RandomInputs(NodeValuesFunctor64& func) : nodeValuesFunc(func) {}
      bool operator()(vector<uint64_t>& nodeValues,
                      vector<uint64_t>::iterator inputsBegin,
                      vector<uint64_t>::iterator inputsEnd) {
        bool ret = nodeValuesFunc(nodeValues);
        for(vector<uint64_t>::iterator it = inputsBegin; it != inputsEnd; ++it) {
          *it = Random::randomUint64();
        }
        return ret;
      }
      void indexToIDMap(vector<ID>& indexToID) {
        nodeValuesFunc.indexToIDMap(indexToID);
      }
      private:
      NodeValuesFunctor64& nodeValuesFunc;
    };

    RandomInputs random(func);

    sequentialSimulate64(model, numCycles, random);
  }


  void sequentialSimulate64(Model& model, unsigned numCycles,
      NodeValuesAndInputsFunctor64& func) {

    //Grab the AIG attachment (read-only)
    AIGAttachment const * const aat = (AIGAttachment const *) model.constAttachment(Key::AIG);
    //Create a reference to the AIG from the AIG attachment
    Opt::AIG const & aig = aat->aig;
    //Get the ID to AIG reference map
    Opt::IDRefMap const & aigRefOfId = aat->id2ref;
    //Get the AIG reference to ID map
    Opt::RefIDMap const & idOfAigRef = aat->ref2id;

    //Get the ExprAttachment (read-only)
    ExprAttachment const * const eat = (ExprAttachment const *) model.constAttachment(Key::EXPR);

    //Create a view of the model
    Expr::Manager::View* modelView = model.newView();

    vector<uint64_t> nodeValues(aig.size());
    //Set the node value for the constant false node
    nodeValues[0] = 0;

    //Keep track of which latches are specified in the initial conditions and
    //which are not
    unordered_set<ID> latchAssigned;

    //Get the initial conditions
    const vector<ID>& initialConditions = eat->initialConditions();
    //Set the latch values according to the initial conditions
    for(unsigned i = 0; i < initialConditions.size(); ++i) {
      //Check whether it is true or false by checking if it's a Expr::Var or an
      //Expr::Not
      Expr::Op op = modelView->op(initialConditions[i]);
      if(op == Expr::Var) {
        //For AIGER, we should never come here
        assert(aigRefOfId.find(initialConditions[i]) != aigRefOfId.end());
        //Set it's value to true
        nodeValues[UIGET(Opt::indexOf(aigRefOfId.at(initialConditions[i])))] =
            0xFFFFFFFFFFFFFFFFLL;
        //Mark this latch as assigned
        latchAssigned.insert(initialConditions[i]);
      }
      else {
        assert(op == Expr::Not);
        ID latch = modelView->apply(Expr::Not, initialConditions[i]);
        assert(aigRefOfId.find(latch) != aigRefOfId.end());
        nodeValues[UIGET(Opt::indexOf(aigRefOfId.at(latch)))] = 0;
        latchAssigned.insert(latch);
      }
    }
    delete modelView;
    model.constRelease(eat);

    //Generate random values for latches that have not been initialized
    for(unsigned i = 1 + aig.numInputs();
        i < 1 + aig.numInputs() + aig.numStateVars(); ++i) {
      //Check if this latch has not already been assigned
      if(latchAssigned.find(idOfAigRef.at(Opt::refOf(i, false))) == latchAssigned.end()) {
        //If not generate a random value for it
        nodeValues[i] = Random::randomUint64();
      }
    }

    const vector<uint64_t>::iterator inputsBegin = nodeValues.begin() + 1;
    const vector<uint64_t>::iterator inputsEnd = inputsBegin + aig.numInputs();
    const vector<uint64_t>::iterator stateVarsBegin = inputsEnd;

    //Construct an index to ID map
    vector<ID> indexToID(aig.size());
    for(unsigned i = 0; i < aig.size(); ++i) {
      assert(idOfAigRef.find(Opt::refOf(i, false)) != idOfAigRef.end());
      indexToID[i] = idOfAigRef.at(Opt::refOf(i, false));
    }

    func.indexToIDMap(indexToID);
 
    const vector<Opt::NodeRef>& nextStateFnRefs = aig.nextStateFnRefs();
    assert(nextStateFnRefs.size() == aig.numStateVars());
    //Simulate the circuit for numCycles clock cycles
    for(unsigned cycle = 0; cycle < numCycles; ++cycle) {
      //Call func to pass the current state and get the input values
      bool proceed = func(nodeValues, inputsBegin, inputsEnd);
      if(!proceed) break;
      //Evaluate node values according to the topological sort
      simulateAig64(aig, nodeValues);

      //Update current state values with next state ones
      vector<uint64_t> latchVals(nextStateFnRefs.size());
      for(unsigned i = 0; i < nextStateFnRefs.size(); ++i) {
        //Assign the value of the latch to the next state value
        latchVals[i] = Opt::isNot(nextStateFnRefs[i]) ?
            ~nodeValues[UIGET(Opt::indexOf(nextStateFnRefs[i]))] :
            nodeValues[UIGET(Opt::indexOf(nextStateFnRefs[i]))];
      }
      copy(latchVals.begin(), latchVals.end(), stateVarsBegin);
    }
    //Pass the final state reached
    func(nodeValues, inputsBegin, inputsEnd);

    model.constRelease(aat);
  }

  void sequentialSimulate64(Model& model, unsigned numCycles,
      StateAndInputsFunctor64& func, OutputsFunctor64& outFunc) {

    //Grab the AIG attachment (read-only)
    AIGAttachment const * const aat = (AIGAttachment const *) model.constAttachment(Key::AIG);
    //Create a reference to the AIG from the AIG attachment
    Opt::AIG const & aig = aat->aig;
    //Get the ID to AIG reference map
    Opt::IDRefMap const & aigRefOfId = aat->id2ref;
    //Get the AIG reference to ID map
    Opt::RefIDMap const & idOfAigRef = aat->ref2id;

    //Get the ExprAttachment (read-only)
    ExprAttachment const * const eat = (ExprAttachment const *) model.constAttachment(Key::EXPR);

    //Create a view of the model
    Expr::Manager::View* modelView = model.newView();

    vector<uint64_t> nodeValues(aig.size());
    //Set the node value for the constant false node
    nodeValues[0] = 0;

    //Keep track of which latches are specified in the initial conditions and
    //which are not
    unordered_set<ID> latchAssigned;

    //Get the initial conditions
    const vector<ID>& initialConditions = eat->initialConditions();
    //Set the latch values according to the initial conditions
    for(unsigned i = 0; i < initialConditions.size(); ++i) {
      //Check whether it is true or false by checking if it's a Expr::Var or an
      //Expr::Not
      Expr::Op op = modelView->op(initialConditions[i]);
      if(op == Expr::Var) {
        assert(aigRefOfId.find(initialConditions[i]) != aigRefOfId.end());
        //Set it's value to true
        nodeValues[UIGET(Opt::indexOf(aigRefOfId.at(initialConditions[i])))] =
            0xFFFFFFFFFFFFFFFFLL;
        //Mark this latch as assigned
        latchAssigned.insert(initialConditions[i]);
      }
      else {
        assert(op == Expr::Not);
        ID latch = modelView->apply(Expr::Not, initialConditions[i]);
        assert(aigRefOfId.find(latch) != aigRefOfId.end());
        nodeValues[UIGET(Opt::indexOf(aigRefOfId.at(latch)))] = 0;
        latchAssigned.insert(latch);
      }
    }
    delete modelView;
    model.constRelease(eat);

    //Generate random values for latches that have not been initialized
    for(unsigned i = 1 + aig.numInputs();
        i < 1 + aig.numInputs() + aig.numStateVars(); ++i) {
      //Check if this latch has not already been assigned
      if(latchAssigned.find(idOfAigRef.at(Opt::refOf(i, false))) == latchAssigned.end()) {
        //If not generate a random value for it
        nodeValues[i] = Random::randomUint64();
      }
    }

    const vector<uint64_t>::iterator inputsBegin = nodeValues.begin() + 1;
    const vector<uint64_t>::iterator inputsEnd = inputsBegin + aig.numInputs();
    const vector<uint64_t>::iterator stateVarsBegin = inputsEnd;
    const vector<uint64_t>::iterator stateVarsEnd = stateVarsBegin + aig.numStateVars();
 
    const vector<Opt::NodeRef>& nextStateFnRefs = aig.nextStateFnRefs();
    const vector<Opt::NodeRef>& outputFnRefs = aig.outputFnRefs();
    vector<uint64_t> outputValues(outputFnRefs.size());
    assert(nextStateFnRefs.size() == aig.numStateVars());
    //Simulate the circuit for numCycles clock cycles
    for(unsigned cycle = 0; cycle < numCycles; ++cycle) {
      //Call func to pass the current state and get the input values
      bool proceed = func(stateVarsBegin, stateVarsEnd, inputsBegin, inputsEnd);
      if(!proceed) break;
      //Evaluate node values according to the topological sort
      simulateAig64(aig, nodeValues);

      for(unsigned i = 0; i < outputFnRefs.size(); ++i) {
        outputValues[i] = Opt::isNot(outputFnRefs[i]) ?
            ~nodeValues[UIGET(Opt::indexOf(outputFnRefs[i]))] :
            nodeValues[UIGET(Opt::indexOf(outputFnRefs[i]))];
      }
      outFunc(outputValues);

      //Update current state values with next state ones
      vector<uint64_t> latchVals(nextStateFnRefs.size());
      for(unsigned i = 0; i < nextStateFnRefs.size(); ++i) {
        //Assign the value of the latch to the next state value
        latchVals[i] = Opt::isNot(nextStateFnRefs[i]) ?
            ~nodeValues[UIGET(Opt::indexOf(nextStateFnRefs[i]))] :
            nodeValues[UIGET(Opt::indexOf(nextStateFnRefs[i]))];
      }
      copy(latchVals.begin(), latchVals.end(), stateVarsBegin);
    }
    //Pass the final state reached
    func(stateVarsBegin, stateVarsEnd, inputsBegin, inputsEnd);

    model.constRelease(aat);
  }

  //void randomSimulate64(Opt::AIG& aig, vector<uint64_t>& nodeValues, vector<Opt::NodeIndex>& liveNodes) {
  void randomSimulate64(const Opt::AIG& aig, vector<uint64_t>& nodeValues) {

    //Generate random values and assign them to nodeValues directly
    for(unsigned i = 1; i <= aig.numInputs() + aig.numStateVars(); ++i) {
      nodeValues[i] = Random::randomUint64();
    }

    //simulateAig64(aig, nodeValues, liveNodes);
    simulateAig64(aig, nodeValues);
  }

  //void simulateAig64(const Opt::AIG& aig, vector<uint64_t>& nodeValues, vector<Opt::NodeIndex>& liveNodes) {
  void simulateAig64(const Opt::AIG& aig, vector<uint64_t>& nodeValues) {
    //for(unsigned i = 0; i <liveNodes.size(); ++i) {
    for(unsigned i = aig.numInputs() + aig.numStateVars() + 1; i < aig.size(); ++i) {
      
      //Lookup value of first fanin
      //Opt::NodeRef fanin1 = aig[liveNodes[i]][0];
      Opt::NodeRef fanin1 = aig[i][0];
      uint64_t fanin1val = Opt::isNot(fanin1) ?
          ~nodeValues[UIGET(Opt::indexOf(fanin1))] :
          nodeValues[UIGET(Opt::indexOf(fanin1))];

      //Lookup value of second fanin
      //Opt::NodeRef fanin2 = aig[liveNodes[i]][1];
      Opt::NodeRef fanin2 = aig[i][1];
      uint64_t fanin2val = Opt::isNot(fanin2) ?
          ~nodeValues[UIGET(Opt::indexOf(fanin2))] :
          nodeValues[UIGET(Opt::indexOf(fanin2))];

      //Compute the value of the node and add it to the map
      //nodeValues[UIGET(liveNodes[i])] = fanin1val & fanin2val;
      nodeValues[i] = fanin1val & fanin2val;
    }
  }

  void simulateAig64(const Opt::AIG& aig, vector<uint64_t>& nodeValues, vector<Opt::NodeIndex>& relevantIndices) {
    for(unsigned i = 0; i < relevantIndices.size(); ++i) {
      
      //Lookup value of first fanin
      Opt::NodeRef fanin1 = aig[relevantIndices[i]][0];
      uint64_t fanin1val = Opt::isNot(fanin1) ?
          ~nodeValues[UIGET(Opt::indexOf(fanin1))] :
          nodeValues[UIGET(Opt::indexOf(fanin1))];

      //Lookup value of second fanin
      Opt::NodeRef fanin2 = aig[relevantIndices[i]][1];
      uint64_t fanin2val = Opt::isNot(fanin2) ?
          ~nodeValues[UIGET(Opt::indexOf(fanin2))] :
          nodeValues[UIGET(Opt::indexOf(fanin2))];

      //Compute the value of the node and add it to the map
      nodeValues[UIGET(relevantIndices[i])] = fanin1val & fanin2val;
    }
  }


}

