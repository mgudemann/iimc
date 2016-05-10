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

#include <iostream>
#include <bitset>
#include <algorithm>

#include "SATSweep.h"
#include "Model.h"
#include "AIG.h"
#include "Expr.h"
#include "AIGUtil.h"
#include "ExprAttachment.h"
#include "Error.h"
#include "AIGAttachment.h"
#include "Sim.h"
#include "SimUtil.h"
#include "SAT.h"
#include "options.h"
#include "Util.h"
#include "CombAttachment.h"

using namespace std;
using namespace Opt;

namespace {

void printStats(Stats& stats, Options::Verbosity verbosity) {
  const string ss = "SAT Sweeping: ";
  cout << ss << "Merged a total of " << stats.numMerges << " nodes." << endl;
  cout << ss << "New AIG has " << stats.finalNodes << " nodes" << endl;
  cout << ss << stats.sweepTime << "s spent in sweeping" << endl;
  if(verbosity >= Options::Informative) {
    streamsize ssize = cout.precision(3);
    cout << ss << "Percentage Reduction = "
         << ((double) (stats.initialNodes - stats.finalNodes) /
             (double) stats.initialNodes) * 100.0 << "%" << endl;
    cout.precision(ssize);
    cout << ss << "Number of SAT checks = " << stats.numSatQueries << " ("
         << stats.numSatSatQueries << " SAT/" << stats.numUnsatSatQueries
         << " UNSAT/" << stats.numSatQueries - stats.numSatSatQueries -
         stats.numUnsatSatQueries << " Timed Out)" <<  endl;
    cout << ss << "Number of ignored candidate equivalences due to SAT solver "
         << "timeout = " << stats.numIgnoredEquivs << endl;
    if(stats.timeout > 0) {
      int64_t lagTime = stats.totalTime - stats.timeout;
      if(lagTime > 0) {
        cout << ss << "Lag time = " << lagTime / 1000000.0 << "s" << endl;
      }
    }
  }
}

/**
 * An equivalence class is a list of nodes associated with a signature
 */
typedef pair<list<NodeIndex>, uint64_t> EquivClass;

class IsShallower {
public:
  IsShallower(const AIG& aig): _aig(aig) { }
  bool operator()(NodeIndex node1, NodeIndex node2) {
    return (_aig.depth(node1) < _aig.depth(node2));
  }
private:
  const AIG& _aig;
};

bool checkEquivalence(Model& model, AIG& aig1, AIG& aig2, RefIDMap& idOfAigRef1, RefIDMap& idOfAigRef2) {

  if(model.verbosity() >= Options::Informative) {
    cout << "Performing equivalence check of the 2 AIGs" << endl;
  }

  const vector<NodeRef>& outputFns1 = aig1.outputFnRefs();
  const vector<NodeRef>& outputFns2 = aig2.outputFnRefs();
  const vector<NodeRef>& nextStateFns1 = aig1.nextStateFnRefs();
  const vector<NodeRef>& nextStateFns2 = aig2.nextStateFnRefs();

  if(outputFns1.size() != outputFns2.size()) {
    if(model.verbosity() > Options::Silent)
      cout << "Number of outputs is not equal" << endl;
    return false;
  }

  if(nextStateFns1.size() != nextStateFns2.size()) {
    if(model.verbosity() > Options::Silent)
      cout << "Number of next state functions is not equal" << endl;
    return false;
  }

  SAT::Manager* satMgr = model.newSATManager();

  Expr::Manager::View* modelView = model.newView();

  modelView->begin_local();

  for(unsigned i = 0; i < outputFns1.size(); ++i) {
    SAT::Manager::View* satView = satMgr->newView(*modelView);
    RefIDMap* satIdOfRef1 = new RefIDMap;
    RefIDMap* satIdOfRef2 = new RefIDMap;
    vector<vector<ID> > clauses;
    tseitin(aig1, outputFns1[i], *modelView, clauses, idOfAigRef1, satIdOfRef1, false);
    tseitin(aig2, outputFns2[i], *modelView, clauses, idOfAigRef2, satIdOfRef2, false);
    //Get the SAT IDs of the two output functions
    ID satID1, satID2;
    if(isNot(outputFns1[i])) {
      assert(satIdOfRef1->find(invert(outputFns1[i])) != satIdOfRef1->end());
      satID1 = (*satIdOfRef1)[invert(outputFns1[i])];
    }
    else {
      assert(satIdOfRef1->find(outputFns1[i]) != satIdOfRef1->end());
      satID1 = (*satIdOfRef1)[outputFns1[i]];
    }
    if(isNot(outputFns2[i])) {
      assert(satIdOfRef2->find(invert(outputFns2[i])) != satIdOfRef2->end());
      satID2 = (*satIdOfRef2)[invert(outputFns2[i])];
    }
    else {
      assert(satIdOfRef2->find(outputFns2[i]) != satIdOfRef2->end());
      satID2 = (*satIdOfRef2)[outputFns2[i]];
    }
    //Add their XOR
    SAT::Clauses equiv;
    equiv.resize(2);
    if(isNot(outputFns1[i])) {
      equiv[0].push_back(modelView->apply(Expr::Not, satID1));
      equiv[1].push_back(satID1);
    }
    else {
      equiv[0].push_back(satID1);
      equiv[1].push_back(modelView->apply(Expr::Not, satID1));
    }
    if(isNot(outputFns2[i])) {
      equiv[0].push_back(modelView->apply(Expr::Not, satID2));
      equiv[1].push_back(satID2);
    }
    else {
      equiv[0].push_back(satID2);
      equiv[1].push_back(modelView->apply(Expr::Not, satID2));
    }
    clauses.push_back(equiv[0]);
    clauses.push_back(equiv[1]);
    try {
      satView->add(clauses);
    }
    catch(SAT::Trivial tr) {
      //If UNSAT
      delete satView;
      if(tr.value() == false) continue;
      else {
        if(model.verbosity() > Options::Silent)
          cout << "Outputs " << i << " are not equivalent" << endl;
        return false;
      }
    }
    if(satView->sat()) {
      delete satView;
      if(model.verbosity() > Options::Silent)
        cout << "Outputs " << i << " are not equivalent" << endl;
      return false;
    }
    delete satView;
    delete satIdOfRef1;
    delete satIdOfRef2;
  }

  for(unsigned i = 0; i < nextStateFns1.size(); ++i) {
    SAT::Manager::View* satView = satMgr->newView(*modelView);
    RefIDMap* satIdOfRef1 = new RefIDMap;
    RefIDMap* satIdOfRef2 = new RefIDMap;
    vector<vector<ID> > clauses;
    tseitin(aig1, nextStateFns1[i], *modelView, clauses, idOfAigRef1, satIdOfRef1, false);
    tseitin(aig2, nextStateFns2[i], *modelView, clauses, idOfAigRef2, satIdOfRef2, false);
    //Get the SAT IDs of the two next state functions functions
    ID satID1, satID2;
    if(isNot(nextStateFns1[i])) {
      assert(satIdOfRef1->find(invert(nextStateFns1[i])) != satIdOfRef1->end());
      satID1 = (*satIdOfRef1)[invert(nextStateFns1[i])];
    }
    else {
      assert(satIdOfRef1->find(nextStateFns1[i]) != satIdOfRef1->end());
      satID1 = (*satIdOfRef1)[nextStateFns1[i]];
    }
    if(isNot(nextStateFns2[i])) {
      assert(satIdOfRef2->find(invert(nextStateFns2[i])) != satIdOfRef2->end());
      satID2 = (*satIdOfRef2)[invert(nextStateFns2[i])];
    }
    else {
      assert(satIdOfRef2->find(nextStateFns2[i]) != satIdOfRef2->end());
      satID2 = (*satIdOfRef2)[nextStateFns2[i]];
    }
    //Add their XOR
    SAT::Clauses equiv;
    equiv.resize(2);
    if(isNot(nextStateFns1[i])) {
      equiv[0].push_back(modelView->apply(Expr::Not, satID1));
      equiv[1].push_back(satID1);
    }
    else {
      equiv[0].push_back(satID1);
      equiv[1].push_back(modelView->apply(Expr::Not, satID1));
    }
    if(isNot(nextStateFns2[i])) {
      equiv[0].push_back(modelView->apply(Expr::Not, satID2));
      equiv[1].push_back(satID2);
    }
    else {
      equiv[0].push_back(satID2);
      equiv[1].push_back(modelView->apply(Expr::Not, satID2));
    }
    clauses.push_back(equiv[0]);
    clauses.push_back(equiv[1]);
    try {
      satView->add(clauses);
    }
    catch(SAT::Trivial tr) {
      //IF UNSAT
      delete satView;
      if(tr.value() == false) continue;
      else {
        if(model.verbosity() > Options::Silent)
          cout << "Next state functions " << i << " are not equivalent" << endl;
        return false;
      }
    }
    if(satView->sat()) {
      delete satView;
      if(model.verbosity() > Options::Silent)
        cout << "Next state functions " << i << " are not equivalent" << endl;
      return false;
    }
    delete satView;
    delete satIdOfRef1;
    delete satIdOfRef2;
  }

  if(model.verbosity() >= Options::Informative) {
    cout << "Models are equivalent" << endl;
  }
  delete modelView;
  delete satMgr;
  return true;
}

void tr(AIG& aig, NodeRef ref, vector<NodeIndex>& liveVars, vector<NodeIndex>& liveNodes, vector<char>& visited) {
  
  if(isNot(ref))
    tr(aig, invert(ref), liveVars, liveNodes, visited);

  NodeIndex index = indexOf(ref);
  if(visited[UIGET(index)] == 1)
    return;

  visited[UIGET(index)] = 1;

  if(index == 0 || aig[index].isVar()) {
    liveVars.push_back(index);
    return;
  }

  NodeRef fanin1ref = aig[index][0];
  bool isInverted = false;
  if(isNot(fanin1ref))  {
    fanin1ref = invert(fanin1ref);
    isInverted = true;
  }
  while(fanin1ref != aig.merged(indexOf(fanin1ref))) {
    fanin1ref = aig.merged(indexOf(fanin1ref));
    if(isNot(fanin1ref)) {
      fanin1ref = invert(fanin1ref);
      isInverted ^= true;
    }
  }
  aig[index][0] = isInverted ? invert(fanin1ref) : fanin1ref;
  tr(aig, fanin1ref, liveVars, liveNodes, visited);

  NodeRef fanin2ref = aig[index][1];
  isInverted = false;
  if(isNot(fanin2ref)) {
    fanin2ref = invert(fanin2ref);
    isInverted = true;
  }
  while(fanin2ref != aig.merged(indexOf(fanin2ref))) {
    fanin2ref = aig.merged(indexOf(fanin2ref));
    if(isNot(fanin2ref)) {
      fanin2ref = invert(fanin2ref);
      isInverted ^= true;
    }
  }
  aig[index][1] = isInverted ? invert(fanin2ref) : fanin2ref;
  tr(aig, fanin2ref, liveVars, liveNodes, visited);
 
  liveNodes.push_back(index);
}

void findLiveNodes(AIG& aig, vector<NodeIndex>& liveVars, vector<NodeIndex>& liveNodes) {
  liveVars.clear();
  liveNodes.clear();
  vector<char> visited(aig.size(), 0);

  for(unsigned i = 0; i < aig.nextStateFnRefs().size(); ++i) {
    //Get the AIG reference corresponding to this next state function
    NodeRef ref = aig.nextStateFnRefs()[i];
    if(isNot(ref))
      ref = invert(ref);
    //Get the AIG reference of the node it has been merged with: keep looping
    //until we hit a node that is merged with itself (i.e. not merged)
    while(ref != aig.merged(indexOf(ref))){
      //Get the AIG reference of the node it has been merged with
      ref = aig.merged(indexOf(ref));
      if(isNot(ref))
        ref = invert(ref);
    }
    tr(aig, ref, liveVars, liveNodes, visited);
  }

  for(unsigned i = 0; i < aig.outputFnRefs().size(); ++i) {
    //Get the AIG reference corresponding to this next state function
    NodeRef ref = aig.outputFnRefs()[i];
    if(isNot(ref))
      ref = invert(ref);
    //Get the AIG reference of the node it has been merged with: keep looping
    //until we hit a node that is merged with itself (i.e. not merged)
    while(ref != aig.merged(indexOf(ref))) {
      //Get the AIG reference of the node it has been merged with
      ref = aig.merged(indexOf(ref));
      if(isNot(ref))
        ref = invert(ref);
    }
    tr(aig, ref, liveVars, liveNodes, visited);
  }
}

/*
 * Get the indices of AIG nodes in the cone with the root "index". Only adds
 * the indices of intermediate nodes (variables are not added)
 */
void getConeIndices(const AIG& aig, NodeIndex index,
    vector<NodeIndex>& outputConesIndices, vector<char>& visited) {
  if(visited[UIGET(index)] == 1)
    return;

  visited[UIGET(index)] = 1;

  if(index == 0 || aig[index].isVar())
    return;

  NodeIndex lchild = indexOf(aig[index][0]);
  getConeIndices(aig, lchild, outputConesIndices, visited);
  NodeIndex rchild = indexOf(aig[index][1]);
  getConeIndices(aig, rchild, outputConesIndices, visited);

  outputConesIndices.push_back(index);
}

void getOutputConesIndices(const AIG& aig, vector<NodeIndex>& outputConesIndices) {
  vector<char> visited(aig.size(), 0);
  for(unsigned i = 0; i < aig.outputFnRefs().size(); ++i) {
    getConeIndices(aig, indexOf(aig.outputFnRefs()[i]), outputConesIndices,
        visited);
  }
}

void getSupport(const AIG& aig, NodeIndex index, unordered_set<NodeIndex>& supportVars,
    vector<char>& visited) {

  if(visited[UIGET(index)] == 1)
    return;

  visited[UIGET(index)] = 1;

  if(index == 0)
    return;

  if(aig[index].isVar()) {
    supportVars.insert(index);
    return;
  }

  NodeIndex lchild = indexOf(aig[index][0]);
  getSupport(aig, lchild, supportVars, visited);
  NodeIndex rchild = indexOf(aig[index][1]);
  getSupport(aig, rchild, supportVars, visited);
}

void getStructuralSupport(const AIG& aig, NodeIndex index, unordered_set<NodeIndex>& supportVars) {
  vector<char> visited(aig.size(), 0);
  getSupport(aig, index, supportVars, visited);
}

void getStructuralSupport(const AIG& aig, list<NodeIndex>::const_iterator first, unsigned numNodes, unordered_set<NodeIndex>& supportVars) {
  vector<char> visited(aig.size(), 0);
  unsigned i = 0;
  for(list<NodeIndex>::const_iterator it = first; i < numNodes; ++it, ++i) {
    getSupport(aig, *it, supportVars, visited);
  }
}

void refineEquivClassesUsingSimulation(list<EquivClass>& eqvClasses,
    //Model& model, AIG& aig, vector<char>& inverted, vector<NodeIndex>& liveNodes,
    Model& model, const AIG& aig, vector<char>& inverted,
    vector<uint64_t>* inputValues = NULL) {

  //Perform random simulation
  vector<uint64_t> nodeValues(aig.size());
  nodeValues[0] = 0;
  uint64_t mask = 0;
  if(inputValues == NULL) {
    //Sim::randomSimulate64(aig, nodeValues, liveNodes);
    Sim::randomSimulate64(aig, nodeValues);
    if(model.options().count("satsweep_assumeProperty")) {
      for(unsigned i = 0; i < aig.outputFnRefs().size(); ++i) {
        NodeIndex index = indexOf(aig.outputFnRefs()[i]);
        uint64_t val = isNot(aig.outputFnRefs()[i]) ?
            ~nodeValues[UIGET(index)] : nodeValues[UIGET(index)];
        if(val == 0xFFFFFFFFFFFFFFFFLL) {
          //Reject the 64 vectors
          return;
        }
        else if(val != 0) {
          mask |= val;
        }
      }
    }
  }
  else {
    assert(inputValues->size() == aig.numInputs() + aig.numStateVars());
    copy(inputValues->begin(), inputValues->end(), nodeValues.begin() + 1);
    //Sim::simulateAig64(aig, nodeValues, liveNodes);
    Sim::simulateAig64(aig, nodeValues);
  }

  static bool firstTime = true;

  if(model.options().count("satsweep_assumeProperty") && inputValues == NULL) {
    if(firstTime) {
      //We have a single equivalence class
      list<NodeIndex>& nodes = eqvClasses.front().first;
      uint64_t& classSig = eqvClasses.front().second;
      //Update the class's signature with the signature of the first node
      classSig = (nodeValues[UIGET(nodes.front())] | mask);
      //Loop over all other nodes
      unordered_map<uint64_t, list<EquivClass>::iterator> iterOfSig;
      list<NodeIndex>::iterator nodeIter = nodes.begin();
      for(++nodeIter; nodeIter != nodes.end();) {
        if((nodeValues[UIGET(*nodeIter)] | mask) == classSig) {
          //If it matches the signature then it gets to stay
          ++nodeIter;
        }
        else if((~nodeValues[UIGET(*nodeIter)] | mask) == classSig) {
          //If its 1's complement matches the signature, it also gets to stay,
          //but inverted
          inverted[UIGET(*nodeIter)] = 1;
          ++nodeIter;
        }
        else {
          //Moves to a new class or to an existing one
          unordered_map<uint64_t, list<EquivClass>::iterator>::iterator mapIt =
            iterOfSig.find(nodeValues[UIGET(*nodeIter)] | mask);
          unordered_map<uint64_t, list<EquivClass>::iterator>::iterator mapItFlipped =
            iterOfSig.find(~nodeValues[UIGET(*nodeIter)] | mask);
          if(mapIt != iterOfSig.end()) {
            //Move it to this class
            mapIt->second->first.push_back(*nodeIter);
          }
          else if(mapItFlipped != iterOfSig.end()) {
            //Move it to this class
            mapItFlipped->second->first.push_back(*nodeIter);
            inverted[UIGET(*nodeIter)] = 1;
          }
          else {
            //Add a new class and insert it there
            eqvClasses.push_back(EquivClass(list<NodeIndex>(1, *nodeIter),
                (nodeValues[UIGET(*nodeIter)] | mask)));
            //Add this class to the map
            list<EquivClass>::iterator tempIter = eqvClasses.end();
            iterOfSig.insert(unordered_map<uint64_t, list<EquivClass>::iterator>::value_type(
                (nodeValues[UIGET(*nodeIter)] | mask), --tempIter));
          }
          nodes.erase(nodeIter++);
        }
      }
      firstTime = false;
    }
    else {
      //Refine the equivalence classes
      //A class with a signature will also include the nodes with inverted
      //signature (i.e. a class whose signature is 01001 will also include
      //nodes whose signature is 10110). 
      
      for(list<EquivClass>::iterator classIter = eqvClasses.begin(); 
          classIter != eqvClasses.end(); ++classIter) {
        list<NodeIndex>& nodes = classIter->first;
        uint64_t& classSig = classIter->second;
        //Update the class's signature with the signature of the first node
        //Update the class's signature
        classSig = (nodeValues[UIGET(nodes.front())] | mask);
        //Update the first node's signature
        inverted[UIGET(nodes.front())] = 0;
        //Loop over all other nodes in the class, and move them to a different
        //class if they don't match the signature
        //Create a map between a signature and a class's iterator
        unordered_map<uint64_t, list<EquivClass>::iterator> iterOfSig;
        list<NodeIndex>::iterator nodeIter = nodes.begin();
        for(++nodeIter; nodeIter != nodes.end();) {
          //Update the node's signature
          //Check if it matches the signature of the class it's currently in
          uint64_t fullSignature;
          if(inverted[UIGET(*nodeIter)] == 1)
            fullSignature = ~nodeValues[UIGET(*nodeIter)] | mask;
          else
            fullSignature = nodeValues[UIGET(*nodeIter)] | mask;
          if(fullSignature == classSig) {
            inverted[UIGET(*nodeIter)] = !((nodeValues[UIGET(*nodeIter)] | mask)
                == (nodeValues[UIGET(nodes.front())] | mask));
            ++nodeIter;
          }
          else {
            //If not, create another class with this signature, and insert it at
            //the beginning of the classes list, and insert it in the map
            //First check if this class is already there
            unordered_map<uint64_t, list<EquivClass>::iterator>::iterator mapIt =
                iterOfSig.find(fullSignature);
            if(mapIt != iterOfSig.end()) {
              //Move it to the other class
              mapIt->second->first.push_back(*nodeIter);
              assert(fullSignature == mapIt->second->second);
              inverted[UIGET(*nodeIter)] = !(
                (nodeValues[UIGET(*nodeIter)] | mask) == 
                (nodeValues[UIGET(mapIt->second->first.front())] | mask));
            }
            else {
              //Otherwise, add this new class and insert the node there
              eqvClasses.push_back(EquivClass(list<NodeIndex>(1, *nodeIter),
                  fullSignature));
              inverted[UIGET(*nodeIter)] = 0;
              //Add this class to the map
              list<EquivClass>::iterator tempIter = eqvClasses.end();
              iterOfSig.insert(map<uint64_t, list<EquivClass>::iterator>::value_type(
                fullSignature, --tempIter));
            }
            //Remove the node from this class
            nodes.erase(nodeIter++);
          }
        }
      }
    }
  }
  else {
    if(firstTime) {
      //We have a single equivalence class
      list<NodeIndex>& nodes = eqvClasses.front().first;
      uint64_t& classSig = eqvClasses.front().second;
      //Update the class's signature with the signature of the first node
      classSig = nodeValues[UIGET(nodes.front())];
      //Loop over all other nodes
      unordered_map<uint64_t, list<EquivClass>::iterator> iterOfSig;
      list<NodeIndex>::iterator nodeIter = nodes.begin();
      for(++nodeIter; nodeIter != nodes.end();) {
        if(nodeValues[UIGET(*nodeIter)] == classSig) {
          //If it matches the signature then it gets to stay
          ++nodeIter;
        }
        else if(~nodeValues[UIGET(*nodeIter)] == classSig) {
          //If its 1's complement matches the signature, it also gets to stay,
          //but inverted
          inverted[UIGET(*nodeIter)] = 1;
          ++nodeIter;
        }
        else {
          //Moves to a new class or to an existing one
          unordered_map<uint64_t, list<EquivClass>::iterator>::iterator mapIt =
            iterOfSig.find(nodeValues[UIGET(*nodeIter)]);
          unordered_map<uint64_t, list<EquivClass>::iterator>::iterator mapItFlipped =
            iterOfSig.find(~nodeValues[UIGET(*nodeIter)]);
          if(mapIt != iterOfSig.end()) {
            //Move it to this class
            mapIt->second->first.push_back(*nodeIter);
            assert(nodeValues[UIGET(*nodeIter)] == mapIt->second->second);
          }
          else if(mapItFlipped != iterOfSig.end()) {
            //Move it to this class
            mapItFlipped->second->first.push_back(*nodeIter);
            assert(~nodeValues[UIGET(*nodeIter)] == mapItFlipped->second->second);
            inverted[UIGET(*nodeIter)] = 1;
          }
          else {
            //Add a new class and insert it there
            eqvClasses.push_back(EquivClass(list<NodeIndex>(1, *nodeIter),
                nodeValues[UIGET(*nodeIter)]));
            //Add this class to the map
            list<EquivClass>::iterator tempIter = eqvClasses.end();
            iterOfSig.insert(unordered_map<uint64_t, list<EquivClass>::iterator>::value_type(
                nodeValues[UIGET(*nodeIter)], --tempIter));
          }
          nodes.erase(nodeIter++);
        }
      }
      firstTime = false;
    }
    else {
      //Refine the equivalence classes
      //A class with a signature will also include the nodes with inverted
      //signature (i.e. a class whose signature is 01001 will also include
      //nodes whose signature is 10110). 
      
      for(list<EquivClass>::iterator classIter = eqvClasses.begin(); 
          classIter != eqvClasses.end(); ++classIter) {
        list<NodeIndex>& nodes = classIter->first;
        uint64_t& classSig = classIter->second;
        //Update the class's signature with the signature of the first node
        //Update the class's signature
        classSig = nodeValues[UIGET(nodes.front())];
        //Update the first node's signature
        inverted[UIGET(nodes.front())] = 0;
        //Loop over all other nodes in the class, and move them to a different
        //class if they don't match the signature
        //Create a map between a signature and a class's iterator
        unordered_map<uint64_t, list<EquivClass>::iterator> iterOfSig;
        list<NodeIndex>::iterator nodeIter = nodes.begin();
        for(++nodeIter; nodeIter != nodes.end();) {
          //Update the node's signature
          //Check if it matches the signature of the class it's currently in
          uint64_t fullSignature;
          if(inverted[UIGET(*nodeIter)] == 1)
            fullSignature = ~nodeValues[UIGET(*nodeIter)];
          else
            fullSignature = nodeValues[UIGET(*nodeIter)];
          if(fullSignature == classSig) {
            inverted[UIGET(*nodeIter)] = !(nodeValues[UIGET(*nodeIter)]
                == nodeValues[UIGET(nodes.front())]);
            ++nodeIter;
          }
          else {
            //If not, create another class with this signature, and insert it at
            //the beginning of the classes list, and insert it in the map
            //First check if this class is already there
            unordered_map<uint64_t, list<EquivClass>::iterator>::iterator mapIt =
                iterOfSig.find(fullSignature);
            if(mapIt != iterOfSig.end()) {
              //Move it to the other class
              mapIt->second->first.push_back(*nodeIter);
              assert(fullSignature == mapIt->second->second);
              inverted[UIGET(*nodeIter)] = !(
                nodeValues[UIGET(*nodeIter)] == 
                nodeValues[UIGET(mapIt->second->first.front())]);
            }
            else {
              //Otherwise, add this new class and insert the node there
              eqvClasses.push_back(EquivClass(list<NodeIndex>(1, *nodeIter),
                  fullSignature));
              inverted[UIGET(*nodeIter)] = 0;
              //Add this class to the map
              list<EquivClass>::iterator tempIter = eqvClasses.end();
              iterOfSig.insert(map<uint64_t, list<EquivClass>::iterator>::value_type(
                fullSignature, --tempIter));
            }
            //Remove the node from this class
            nodes.erase(nodeIter++);
          }
        }
      }
    }
  }

  //Delete singleton classes (the node is not equivalent to any other node)
  for(list<EquivClass>::iterator classIter = eqvClasses.begin();
      classIter != eqvClasses.end();) {
    if(classIter->first.size() == 1) {
      eqvClasses.erase(classIter++);
    }
    else {
      ++classIter;
    }
  }
}

inline unsigned nodesInClasses(list<EquivClass>& eqvClasses) {
  unsigned count = 0;
  for(list<EquivClass>::iterator classIter = eqvClasses.begin(); classIter != eqvClasses.end(); ++classIter) {
    count += classIter->first.size(); 
  }
  return count;
}

void printEquivClasses(list<EquivClass>& classes, vector<char>& sig,
    unsigned iteration, const AIG& aig) {

  const string ss = "SAT Sweeping: ";

  cout << ss << endl << ss << "Iteration " << iteration
       << ":" << endl;
  cout << ss << "Current # of equivalence classes = "
       << classes.size() << endl;
  list<EquivClass>::iterator it;
  int i;
  for(it = classes.begin(), i = 1; it != classes.end(); ++it, ++i) {
    cout << ss << "Class " << i << ": # of nodes = " << (it->first).size();
    cout << " Signature = " << it->second;
    cout << endl << ss << "Nodes: ";
    for(list<NodeIndex>::iterator it2 = it->first.begin();
        it2 != it->first.end(); ++it2) {
      cout << "(" << *it2 << "," << static_cast<int>(sig[UIGET(*it2)])
           << "," << aig.depth(*it2) << ")";
    }
    cout << endl;
  }
}

void updateAIGAttachment(Model& model, vector<pair<NodeIndex, NodeRef> >& merges, Stats& stats) {
  if(stats.numMerges != 0) {
    AIGAttachment * aatUpdate = (AIGAttachment*) model.attachment(Key::AIG);
    for(unsigned i = 0; i < merges.size(); ++i) {
      aatUpdate->aig.merge(merges[i].first, merges[i].second, false);
    }
    if(model.options().count("satsweep_verify")) {
      //Copy the old AIG
      AIG newAig = aatUpdate->aig;
      //Copy the old ref2id
      RefIDMap newIdOfAigRef = aatUpdate->ref2id;
      //Update the old one
      aatUpdate->aig.update(model);
      //Check their equivalence
      checkEquivalence(model, aatUpdate->aig, newAig, aatUpdate->ref2id, newIdOfAigRef);
    }
    else {
      aatUpdate->aig.update(model);
    }
    stats.finalNodes = nodeCount(aatUpdate->aig);
    model.release(aatUpdate);
  }
}

void updateCombAttachment(Model& model, Stats& stats) {
  if(stats.complete || stats.numMerges != 0) {
    CombAttachment * cat = (CombAttachment*) model.attachment(Key::COMB);
    if(stats.complete) {
      cat->simplificationEffort() = CombAttachment::Complete;
    }
    cat->numEquivalences() += stats.numMerges;
    if(stats.timeout > 0) {
      if(stats.totalTime < stats.timeout)
        cat->unusedTime() = stats.timeout - stats.totalTime;
      else 
        cat->unusedTime() = 0;
    }
    model.release(cat);
  }
}

} //unnamed namespace

namespace Opt {

void satSweep(Model& model, AIGAttachment const * const aat,
    vector<pair<NodeIndex, NodeRef> >& merges, Stats& stats) {
  
  const string ss = "SAT Sweeping: ";

  //Create a reference to the AIG from the AIG attachment
  const AIG& aig = aat->aig;

  //Check for trivial AIG
  if(aig.size() == 1) {
    return;
  }

  CombAttachment const * const cat = (CombAttachment*)
      model.constAttachment(Key::COMB);

  //Get the global verbosity level, and the module-specific verbosity level
  Options::Verbosity verbosity = model.verbosity();
  Options::Verbosity satsweep_verbosity = static_cast<Options::Verbosity>(0);

  //Check if the SAT sweeping verbosity level is set
  if((model.options()).count("satsweep_verbosity")) {
    satsweep_verbosity = static_cast<Options::Verbosity>(
        model.options()["satsweep_verbosity"].as<int>());
    //If so, override the global verbosity level
    verbosity = satsweep_verbosity;
  }


  if(cat->simplificationEffort() == CombAttachment::Complete) {
    if(verbosity >= Options::Verbose)
      cout << ss << "Model has already been fully swept" << endl;
    model.constRelease(cat);
    return;
  }

  //Grab the unused time
  int64_t unusedTime = cat->unusedTime();

  model.constRelease(cat);

  //Seed the RNGs (rand and Sim::RandomGenerator::generator)
  int rseed = model.options()["rand"].as<int>();
  if(rseed != -1) {
    srand(rseed);
    Sim::RandomGenerator::generator.seed(static_cast<unsigned int>(rseed));
  }

  //Get the timeout
  int64_t timeout = model.options()["satsweep_timeout"].as<int>() * 1000000;

  if(verbosity >= Options::Informative) {
    if(timeout > 0) {
      cout << ss << "Running with a timeout of " << timeout / 1000000 << " seconds + "
           << unusedTime / 1000000.0 << " seconds of relayed time" << endl;
    }
    else {
      cout << ss << "Running with no timeout." << endl;
    }
  }

  if(timeout > 0) {
    timeout += unusedTime;
  }
  stats.timeout = timeout;

  int64_t startTime = Util::get_user_cpu_time(); 
  stats.startTime = startTime;
 
  //Get from the options the number of iterations after which to terminate if
  //no changes in node equivalence classes occurs
  unsigned numIters = model.options()["satsweep_numIters"].as<unsigned>();

  //Create equivalence classes for the AIG nodes using a list of EquivClass
  //Initially, all nodes are assumed to be equivalent, so there's a single
  //class
  list<EquivClass> eqvClasses(1);
  for(unsigned i = 0; i < aig.size(); ++i) {
    eqvClasses.front().first.push_back(i);
  }
 
  //Sort the nodes in this equivalence class by depth. This is the right time
  //to do that so that equivalence classes are invariantly ordered
  //ascendingly by depth
  IsShallower isShallower(aig);
  eqvClasses.front().first.sort(isShallower);
  vector<unsigned> depths(aig.size());
  unsigned idx = 0;
  for(list<NodeIndex>::iterator it = eqvClasses.front().first.begin();
      it != eqvClasses.front().first.end(); ++it) {
    depths[idx++] = aig.depth(*it);
  }

  //A vector to indicate if each node's signature is inverted relative to the
  //signature of the equivalence class it's in or not
  vector<char> inverted(aig.size(), 0);

  unsigned iteration = 0;
  if(satsweep_verbosity >= Options::Logorrheic) {
    //Print out the info on equivalence classes
    printEquivClasses(eqvClasses, inverted, iteration, aig);
  }

  //Perform random simulation of the model to refine the equivalence classes
  unsigned numNodesBefore = 0;
  unsigned numNodesAfter = nodesInClasses(eqvClasses);
  unsigned numClassesBefore = 0;
  unsigned numClassesAfter = eqvClasses.size();
  unsigned persist = 0;
  unsigned numVectorsUsed = 0;

  if(verbosity >= Options::Verbose) {
    cout << ss << "Performing initial refinement of classes" << endl;
  }

  while(!eqvClasses.empty() && ((numNodesAfter != numNodesBefore) || (numClassesAfter != numClassesBefore) || persist < numIters)) {
    ++numVectorsUsed;
    numNodesBefore = numNodesAfter;
    numClassesBefore = numClassesAfter;
    ++iteration;
    //refineEquivClassesUsingSimulation(eqvClasses, model, aig, inverted, liveNodes);
    refineEquivClassesUsingSimulation(eqvClasses, model, aig, inverted);
    if(satsweep_verbosity >= Options::Logorrheic) {
      printEquivClasses(eqvClasses, inverted, iteration, aig);
    }
    numNodesAfter = nodesInClasses(eqvClasses);
    numClassesAfter = eqvClasses.size();
    if(verbosity >= Options::Logorrheic) {
      cout << "Remaining number of nodes = " << nodesInClasses(eqvClasses)
           << " in " << eqvClasses.size() << " classes" << endl;
    }
    //Check for timeout
    if(timeout > 0) {
      int64_t elapsedTime = Util::get_user_cpu_time() - startTime;
      if(elapsedTime >= timeout) {
        if(verbosity >= Options::Informative) {
          cout << ss << "timeout";
          if(verbosity >= Options::Verbose)
            cout << " in initial refinement";
          cout << endl;
        }
        stats.sweepTime = elapsedTime / 1000000.0;
        return;
      }
    }
    if(numNodesAfter != numNodesBefore || numClassesBefore != numClassesBefore)
      persist = 0;
    else
      ++persist;
  }

  //Check for absence of equivalences
  if(eqvClasses.empty()) {
    //Indicate that the model was fully swept
    stats.complete = true;
    stats.sweepTime = (Util::get_user_cpu_time() - startTime) / 1000000.0;
    return;
  }

  if(verbosity >= Options::Verbose) {
    cout << ss << "Done with initial refinement" << endl;
    cout << ss << "Simulated " << numVectorsUsed << " random vectors" << endl;
  }

  //Get the AIG reference to ID map
  const RefIDMap& idOfAigRef = aat->ref2id;

  //Create a SAT manager
  SAT::Manager* satMgr = model.newSATManager();

  //Get a view of the model
  Expr::Manager::View* modelView = model.newView();

  modelView->begin_local();

  //Create clauses for the whole AIG
  vector<vector<ID> > clauses;
  RefIDMap satIdOfRef;
  //First create clauses for all next state functions
  tseitin(aig, aig.nextStateFnRefs(), *modelView, clauses, idOfAigRef,
      &satIdOfRef, false);
  //Second create clauses for all output functions
  vector<ID> ids = tseitin(aig, aig.outputFnRefs(), *modelView, clauses,
      idOfAigRef, &satIdOfRef, false);
  //If property assumption is set, assert the property
  vector<NodeIndex> outputConesIndices;
  if(model.options().count("satsweep_assumeProperty")) {
    for(unsigned i = 0; i < ids.size(); ++i) {
      //Add clauses that assert the property(s)
      clauses.push_back(vector<ID>(1, modelView->apply(Expr::Not, ids[i])));
    }
    getOutputConesIndices(aig, outputConesIndices);
  }

  //Collect the satIdOfRefs in a vector
  vector<ID> satId(aig.size());
  for(RefIDMap::iterator it = satIdOfRef.begin(); it != satIdOfRef.end();
      ++it) {
    assert(!isNot(it->first));
    assert(indexOf(it->first) < aig.size());
    satId[UIGET(indexOf(it->first))] = it->second;
  }

  //Only care about values for the inputs and state variables. Also collect
  //them in a vector (assignIterators) to avoid hashtable lookups during the
  //main SAT sweeping loop
  SAT::Assignment assign;
  vector<SAT::Assignment::iterator> assignIterators(
    aig.numInputs() + aig.numStateVars());
  for(unsigned i = 1; i <= aig.numInputs() + aig.numStateVars(); ++i) {
    NodeRef ref = refOf(i, false);
    assert(idOfAigRef.find(ref) != idOfAigRef.end());
    //ID id = idOfAigRef[ref];
    ID id = idOfAigRef.find(ref)->second;
    assignIterators[i - 1] =
        assign.insert(SAT::Assignment::value_type(id, SAT::Unknown)).first;
  }

  //Create a view of the SAT manager
  SAT::Manager::View* satView = satMgr->newView(*modelView);
  //Add all clauses to the view
  satView->add(clauses);

  double satTimeout;
  if(model.options().count("satsweep_satTimeout"))
    satTimeout = model.options()["satsweep_satTimeout"].as<double>();
  else {
    if(timeout > 0) {
      satTimeout = timeout / 128000000.0;
    }
    else {
      satTimeout = 1.0;
    }
  }
  
  if(timeout <= 0) {
    satView->timeout(satTimeout);
  }
  
  unsigned numQuantiles = model.options()["satsweep_depthQuantiles"].
      as<unsigned>();
  double indexDouble = (aig.size() - aig.numInputs() - aig.numStateVars() - 1)
      / (double)(numQuantiles) + aig.numInputs() + aig.numStateVars();
  assert((size_t)(indexDouble) < depths.size());
  double depthThreshold = depths[((size_t)(indexDouble))];
  unsigned maxDepth = depths.back();
  //Loop until no more equivalence classes remain or a timeout is reached
  bool terminate = false;
  while(!eqvClasses.empty() && !terminate) {

    if(verbosity >= Options::Logorrheic) {
      cout << "Current SAT Solver timeout = " << satTimeout << endl;
      cout << "Current depth threshold = " << depthThreshold << endl;
    }

    bool foundShallowNodes = false;
    bool foundEasySatQueries = false;

    //Simulation vectors
    vector<vector<uint64_t> > inputValues;
    unordered_set<NodeIndex> supportVars;
    unsigned numCounterexamples = 0;

    bool clustered = true;
    //Loop over all equivalence classes and do SAT checks for node equivalences
    for(list<EquivClass>::iterator classIter = eqvClasses.begin();
        classIter != eqvClasses.end();) {

      //Check for timeout
      if(timeout > 0) {
        int64_t elapsedTime = Util::get_user_cpu_time() - startTime;
        if(elapsedTime >= timeout) {
          if(verbosity >= Options::Informative) {
            cout << ss << "timeout";
            if(verbosity >= Options::Verbose)
              cout << " in SAT/refinement loop";
            cout << endl;
          }
          terminate = true;
          break;
        }
      }
      
      list<NodeIndex>& nodes = classIter->first;
      list<NodeIndex>::const_iterator nodeIter = nodes.begin();
      ++nodeIter;
      //Check if at least two nodes in this class satisfy the depth threshold
      if(aig.depth(*nodeIter) > (size_t)(depthThreshold)) {
        //Skip this class
        ++classIter;
        continue;
      }

      //Allocate a new group ID
      SAT::GID gid = satView->newGID();
      SAT::Clauses equiv(2);
      vector<char> negated;

      //Keep the shallowest node as the representative for the class
      NodeIndex rep = nodes.front();

      //Count the number of ndoes considered for equivalence
      unsigned numNodes = 0;
      for(nodeIter = nodes.begin(); nodeIter != nodes.end(); ++nodeIter) {

        NodeIndex nodeIndex = *nodeIter;
        //Skip checking if depth is larger than current depth threshold
        if(aig.depth(nodeIndex) > (size_t)(depthThreshold) ||
            (numNodes == 2 && !clustered) || numNodes == MAX_LITS - 1) {
          break;
        }
        ++numNodes;
        
        //Get the SAT ID corresponding to this AIG index
        ID satNodeID = satId[UIGET(nodeIndex)];

        //Check if it is inverted relative to the representative
        if(inverted[UIGET(nodeIndex)] == inverted[UIGET(rep)]) {
          equiv[0].push_back(satNodeID);
          equiv[1].push_back(modelView->apply(Expr::Not, satNodeID));
          negated.push_back(0);
        }
        else {
          equiv[0].push_back(modelView->apply(Expr::Not, satNodeID));
          equiv[1].push_back(satNodeID);
          negated.push_back(1);
        }
      }

      try {
        satView->add(equiv, gid);
      }
      catch(SAT::Trivial tr) {
      }

      if(verbosity >= Options::Logorrheic) {
        cout << ss << "Performing " << numNodes - 1
             << " simultaneous equivalence checks" << endl;
      }

      if(numNodes == 2)
        clustered = false;

      foundShallowNodes = true;

      //Set the timeout of the SAT solver to the remaining time
      double remainingTime = 0.0;
      if(timeout > 0) {
        remainingTime = (double) (timeout -
            (Util::get_user_cpu_time() - startTime)) / 1000000.0;
        satView->timeout(min(satTimeout, remainingTime));
      }
      bool failed = false;
      bool satisfiable = true;
      //Run the SAT check
      ++stats.numSatQueries;
      try {
        satisfiable = satView->sat(NULL, &assign);
      }
      catch(Timeout excep) {
        if(timeout > 0 && remainingTime < satTimeout) {
          if(verbosity >= Options::Informative) {
            cout << ss << "timeout";
            if(verbosity >= Options::Verbose)
              cout << " in SAT solver";
            cout << endl;
          }
          terminate = true;
          break;
        }
        if(clustered) {
          if(verbosity >= Options::Logorrheic) {
            cout << ss << "timeout in SAT solver, retrying with clustering "
                 << "disabled" << endl;
          }
          clustered = false;
        }
        else {
          if(satTimeout >= MAX_SATSOLVER_TIMEOUT) {
            if(verbosity >= Options::Logorrheic) {
              cout << ss << "timeout in SAT solver with clustering disabled, "
                   << "deleting node" << endl;
            }
            ++stats.numIgnoredEquivs;
            //Delete second node of class
            list<NodeIndex>::iterator deleteIt = nodes.begin();
            classIter->first.erase(++deleteIt);
            if(classIter->first.size() == 1)
              eqvClasses.erase(classIter++);
          }
          else {
            if(verbosity >= Options::Logorrheic) {
              cout << ss << "timeout in SAT solver with clustering disabled, "
                   << "reenabling clustering and moving to next class" << endl;
            }

            clustered = true;
            ++classIter;
          }
        }
        failed = true;
      }
      //Remove the added clauses
      satView->remove(gid);
      if(!failed) {
        foundEasySatQueries = true;
        if(satisfiable) {
          ++stats.numSatSatQueries;
          if(verbosity >= Options::Logorrheic) {
            cout << ss << "Nodes are not equivalent" << endl;
          }
          inputValues.push_back(vector<uint64_t>(aig.numInputs() +
              aig.numStateVars(), 0));
          vector<uint64_t> outputConesVals;
          if(model.options().count("satsweep_assumeProperty")) {
            outputConesVals.resize(aig.size(), 0);
          }
          for(unsigned i = 0; i < aig.numInputs() + aig.numStateVars(); ++i) {
            if(assignIterators[i]->second == SAT::True) {
              inputValues.back()[i] = 0xFFFFFFFFFFFFFFFFLL;
              if(model.options().count("satsweep_assumeProperty")) {
                outputConesVals[i + 1] = 0xFFFFFFFFFFFFFFFFLL;
              }
            }
            else if(assignIterators[i]->second == SAT::Unknown) {
              if(Sim::RandomGenerator::randomBool()) {
                inputValues.back()[i] = 0xFFFFFFFFFFFFFFFFLL;
                if(model.options().count("satsweep_assumeProperty")) {
                  outputConesVals[i + 1] = 0xFFFFFFFFFFFFFFFFLL;
                }
              }
            }
          }
          //Intelligent simulation: The 64th bit will hold the actual
          //counterexample. Other bits will hold distance-1 vectors
          //The number of vectors needed = (number of variables / 63)
          //Get the current size of inputValues
          unsigned curSize = inputValues.size();
          getStructuralSupport(aig, nodes.begin(), numNodes, supportVars);

          //Get the number of extra vectors needed
          unsigned numExtraVecs = supportVars.size() / 63; 
          if(supportVars.size() % 63 == 0)
            --numExtraVecs;
          inputValues.insert(inputValues.end(), numExtraVecs, inputValues.back());
          unordered_set<NodeIndex>::iterator supportVarsIter = supportVars.begin();
          unsigned numRejectedVectors = 0;
          for(unsigned i = 0; i <= numExtraVecs; ++i) {
            /*
            if(supportVarsIter == supportVars.end())
              inputValues.pop_back();
            */
            unordered_set<NodeIndex>::iterator supportVarsBegin = supportVarsIter;
            for(unsigned j = 0; supportVarsIter != supportVars.end() &&
                j < 63; ++supportVarsIter, ++j) {
              //Flip the jth bit in the variable
              inputValues[curSize - 1 + i][UIGET(*supportVarsIter) - 1] ^= (1LL << j);
              if(model.options().count("satsweep_assumeProperty")) {
                outputConesVals[UIGET(*supportVarsIter)] ^= (1LL << j);
              }
            }
            if(model.options().count("satsweep_assumeProperty")) {
              //Drop vectors that violate the property
              Sim::simulateAig64(aig, outputConesVals, outputConesIndices);
              for(unsigned k = 0; k < aig.outputFnRefs().size(); ++k) {
                NodeIndex index = indexOf(aig.outputFnRefs()[k]);
                uint64_t val = isNot(aig.outputFnRefs()[k]) ?
                    ~outputConesVals[UIGET(index)] :
                    outputConesVals[UIGET(index)];
                if(val != 0) {
                  unordered_set<NodeIndex>::iterator temp = supportVarsBegin;
                  //Undo bit flipping for vectors that violate the property
                  uint64_t mask = 0x1;
                  for(unsigned j = 0; j < 63 && temp != supportVars.end(); ++j, ++temp) {
                    if((val & mask) != 0) {
                      inputValues[curSize - 1 + i][UIGET(*temp) - 1] ^= (1LL << j);
                      ++numRejectedVectors;
                    }
                    mask <<= 1;
                  }
                }
              }
              //Flip the bits back
              unsigned bitIndex = 0;
              for(unordered_set<NodeIndex>::iterator it = supportVarsBegin; it != supportVarsIter; ++it, ++bitIndex) {
                outputConesVals[UIGET(*it)] ^= (1LL << bitIndex);
              }

              /*
              if(!rejected) {
                ++i;
              }
              */
            }
            /*
            else {
              ++i;
            }
            */
          }
          /*
          if(model.options().count("satsweep_assumeProperty")) {
            //Delete unneeded vectors
            //cout << "Rejected " << numRejectedVectors << " out of "
            //     << supportVars.size()  + 1 << " vectors" << endl;
            unsigned numActualVecs = (supportVars.size() - numRejectedVectors) / 63 + 1;
            if(numActualVecs > 1 && (supportVars.size() - numRejectedVectors) % 63 == 0) {
              --numActualVecs;
            }
            for(unsigned i = numActualVecs; i < numExtraVecs + 1; ++i) {
              inputValues.pop_back();
            }
          }
          */
          break;
          //++numCounterexamples;
          //++classIter;
        }
        else {
          ++stats.numUnsatSatQueries;
          if(verbosity >= Options::Logorrheic) {
            cout << ss << "Nodes are equivalent" << endl;
          }
          //Indicate their equivalence in the SAT database
          list<NodeIndex>::iterator nodeIt = nodes.begin();
          unsigned negIdx= 1;
          for(++nodeIt; nodeIt != nodeIter; ++negIdx) {
            SAT::Clauses merge(2);
            merge[0].push_back(satId[UIGET(rep)]);
            merge[1].push_back(modelView->apply(Expr::Not,
                satId[UIGET(rep)]));
            if(negated[negIdx] == 0) {
              //nodes 1 and 2 are equivalent
              merge[0].push_back(modelView->apply(Expr::Not,
                  satId[UIGET(*nodeIt)]));
              merge[1].push_back(satId[UIGET(*nodeIt)]);
            }
            else {
              //nodes 1 and 2 are equivalent under negation
              merge[0].push_back(satId[UIGET(*nodeIt)]);
              merge[1].push_back(modelView->apply(Expr::Not,
                  satId[UIGET(*nodeIt)]));
            }
            try { 
              satView->add(merge);
            }
            catch(SAT::Trivial tr) {
            }
            if(verbosity >= Options::Verbose) {
              cout << ss << "Merging node " << *nodeIt << " with "
                   << rep << endl;
            }
            //Indicate the merging
            //aig.merge(*nodeIt, refOf(rep, negated[negIdx]), false);
            merges.push_back(pair<NodeIndex, NodeRef>(*nodeIt, 
                refOf(rep, negated[negIdx])));

            //Remove the merged node from the equivalence classes
            classIter->first.erase(nodeIt++);
          }

          stats.numMerges += numNodes - 1;

          //Delete this class entirely if it now contains a single node
          if(classIter->first.size() == 1) {
            eqvClasses.erase(classIter++);
          }
          else {
            ++classIter;
          }
          clustered = true;
          //findLiveNodes(aig, liveVars, liveNodes);
        }
      }
    }

    /*
    for(list<EquivClass>::iterator classIter = eqvClasses.begin(); classIter != eqvClasses.end();) {
      for(list<NodeIndex>::iterator nodeIter = classIter->first.begin(); nodeIter != classIter->first.end();) {
        if(liveNodes.find(*nodeIter) == liveNodes.end() && liveVars.find(*nodeIter) == liveVars.end()) {
          //cout << "Removing node " << *nodeIter << endl;
          classIter->first.erase(nodeIter++); 
        }
        else
         ++nodeIter;
      }
      if(classIter->first.size() < 2)
        eqvClasses.erase(classIter++);
      else
        ++classIter;
    }
    */

    if(terminate) break;

    //Refine equivalence classes using the vectors learned
    if(verbosity >= Options::Logorrheic) {
      unsigned totalCounterexamples;
      totalCounterexamples = inputValues.empty() ? 0 :
          (inputValues.size() - 1) * 64 + numCounterexamples;
      if(totalCounterexamples > 0) {
        cout << ss << "Refining equivalence classes using "
             << totalCounterexamples << " derived counterexamples" << endl;
      }
    }
    for(unsigned i = 0; i < inputValues.size() && !eqvClasses.empty(); ++i) {
      ++iteration;
      //unsigned numNodesBefore = nodesInClasses(eqvClasses);
      refineEquivClassesUsingSimulation(eqvClasses, model, aig,
          inverted, &(inputValues[i]));
      if(satsweep_verbosity >= Options::Logorrheic) {
        printEquivClasses(eqvClasses, inverted, iteration, aig);
      }
      if(verbosity >= Options::Logorrheic) {
        cout << "Remaining number of nodes = " << nodesInClasses(eqvClasses)
             << " in " << eqvClasses.size() << " classes" << endl;
      }
      //unsigned numNodesAfter = nodesInClasses(eqvClasses);

      //Check if this vector was successful
      /*
      cout  << (numNodesBefore - numNodesAfter)/(double)(numNodesBefore) << endl;
      if((numNodesBefore - numNodesAfter)/(double)(numNodesBefore) > 0.002) {
        //Generate all distance-1 vectors from it
        cout << "Generating more vectors" << endl;
        unsigned curNumVecs = inputValues.size();
        //inputValues.insert(inputValues.end(), supportVars.size(), inputValues[i]);
        inputValues.insert(inputValues.end(), 50, inputValues[i]);
        unordered_set<NodeIndex>::iterator supportVarsIter = supportVars.begin();
        //for(unsigned j = curNumVecs; j < supportVars.size(); ++j, ++supportVarsIter) {
        for(unsigned j = curNumVecs; j < 50; ++j, ++supportVarsIter) {
          inputValues[j][supportVarsIter->getValue() - 1] = ~inputValues[j][supportVarsIter->getValue() - 1];
        }
      }
      */

      //Check for timeout
      if(timeout > 0) {
        int64_t elapsedTime = Util::get_user_cpu_time() - startTime;
        if(elapsedTime >= timeout) {
          if(verbosity >= Options::Informative) {
            cout << ss << "timeout";
            if(verbosity >= Options::Verbose)
              cout << " in counterexample simulation";
            cout << endl;
          }
          terminate = true;
          break;
        }
      }
    }

    if(verbosity >= Options::Logorrheic) {
      if(!inputValues.empty()) {
        cout << ss << "Done with refinement" << endl;
      }
    }
    
    if(!foundShallowNodes) {
      //Increase the depth threshold
      if(depthThreshold < maxDepth) {
        indexDouble += (aig.size() - aig.numInputs() - aig.numStateVars() - 1) /
            (double)(numQuantiles);
        if(indexDouble >= aig.size() - 1) {
          depthThreshold = maxDepth;
        }
        else {
          assert((size_t)(indexDouble) < aig.size() - 1);
          depthThreshold = depths[(size_t)(indexDouble)];
        }
      }
    }
    else if(!foundEasySatQueries) {
      //Increase the SAT solver timeout
      if(satTimeout < MAX_SATSOLVER_TIMEOUT) {
        satTimeout *= 2.0;
        if(satTimeout > MAX_SATSOLVER_TIMEOUT)
          satTimeout = MAX_SATSOLVER_TIMEOUT;
      }
    }
  }

  modelView->end_local();
  delete modelView;
  delete satView;
  delete satMgr;

  stats.sweepTime = (Util::get_user_cpu_time() - startTime) / 1000000.0;
  stats.complete = eqvClasses.empty();
}

}

namespace Action {

void SATSweepAction::exec() {

  Stats stats;

  //Get read-only access to the AIG attachment
  AIGAttachment const * const aat = (AIGAttachment*) model().constAttachment(Key::AIG);
  stats.initialNodes = nodeCount(aat->aig);
  stats.finalNodes = stats.initialNodes;
  if(model().verbosity() > Options::Silent) {
    //Print out the current number of nodes in the AIG
    cout << "SAT Sweeping: Number of AIG nodes = " << stats.initialNodes << endl;
  }
  vector<pair<NodeIndex, NodeRef> > merges;
  Opt::satSweep(model(), aat, merges, stats);
  model().constRelease(aat);
  updateAIGAttachment(model(), merges, stats);
  if(stats.timeout > 0)
    stats.totalTime = Util::get_user_cpu_time() - stats.startTime;
  updateCombAttachment(model(), stats);
  if(model().verbosity() > Options::Silent) {
    printStats(stats, model().verbosity());
  }
}

} //namespace Opt

