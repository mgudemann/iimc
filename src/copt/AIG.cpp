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

#include <algorithm>
#include <sstream>
#include <iostream>
#include <iomanip>

#include "AIG.h"
#include "ExprAttachment.h"
#include "AIGAttachment.h"

using namespace std;

namespace
{

using namespace Opt;

void getCone(AIG* aig, NodeIndex index, set<NodeIndex>& cone) {
  if(index == 0 || (*aig)[index].isVar()) {
    cone.insert(index);
    return;
  }

  NodeIndex lchild = indexOf((*aig)[index][0]);
  getCone(aig, lchild, cone);
  NodeIndex rchild = indexOf((*aig)[index][1]);
  getCone(aig, rchild, cone);

  cone.insert(index);
}

void traverse(AIG* aig, NodeIndex index, set<NodeIndex>& vars) {
  if(index == 0 || (*aig)[index].isVar()) {
    vars.insert(index);
    return;
  }

  NodeIndex lchild = indexOf((*aig)[index][0]);
  traverse(aig, lchild, vars);
  NodeIndex rchild = indexOf((*aig)[index][1]);
  traverse(aig, rchild, vars);
}

} // namespace

namespace Opt
{

AIGNode::AIGNode()
{
  args[0] = ULONG_MAX;
  args[1] = ULONG_MAX;
}

AIGNode::AIGNode(NodeRef arg0, NodeRef arg1)
{
  args[0] = arg0;
  args[1] = arg1;
}

} // namespace Opt

namespace Opt
{

AIG::AIG()
{
  _nodes.push_back(AIGNode(0, 0));
  _depth.push_back(0);
  _merged.push_back(NodeRef(0));
  _fanouts.push_back(unordered_set<NodeIndex>());
}

void AIG::clear()
{
  _nodes.clear();
  _merged.clear();
  _depth.clear();
  _fanouts.clear();
  _nextStateFnRefs.clear();
  _outputFnRefs.clear();
  _badFnRefs.clear();
  _constraintFnRefs.clear();
  _justiceFnSetRefs.clear();
  _fairnessFnRefs.clear();

  _nodes.push_back(AIGNode(0, 0));
  _depth.push_back(0);
  _merged.push_back(NodeRef(0));
  _fanouts.push_back(unordered_set<NodeIndex>());
}

NodeIndex AIG::addNode()
{
  AIGNode n(ULONG_MAX, ULONG_MAX);
  _nodes.push_back(n);
  _depth.push_back(0);

  NodeIndex index = _nodes.size() - 1;
  _merged.push_back(refOf(index, false));

  _fanouts.push_back(unordered_set<NodeIndex>());

  return index;
}

NodeIndex AIG::addNode(NodeRef arg0, NodeRef arg1)
{
//  assert(arg0 != ULONG_MAX && arg1 != ULONG_MAX);

  AIGNode n(arg0, arg1);
  _nodes.push_back(n);

  if(!(UIGET(indexOf(arg0)) == 0 && UIGET(indexOf(arg1)) == 0)) {
    size_t d = max(_depth[UIGET(indexOf(arg0))], _depth[UIGET(indexOf(arg1))]);
    _depth.push_back(1 + d);
  } else _depth.push_back(0);

  NodeIndex index = _nodes.size() - 1;
  _merged.push_back(refOf(index, false));

  _fanouts[UIGET(indexOf(arg0))].insert(index);
  _fanouts[UIGET(indexOf(arg1))].insert(index);
  _fanouts.push_back(unordered_set<NodeIndex>());

  return index;
} 

void AIG::merge(NodeIndex index, NodeRef with, bool updateFanouts)
{
  _merged[UIGET(index)] = with;

  if(updateFanouts) {
    updateFanout(index);

    const unordered_set<NodeIndex> &ifanout = _fanouts[UIGET(index)];
    _fanouts[UIGET(indexOf(with))].insert(ifanout.begin(), ifanout.end());
    _fanouts[UIGET(index)].clear();
  }
}

void AIG::resetMerged()
{
  for(unsigned i = 0; i < _nodes.size(); ++i)
    _merged[i] = refOf(i, false);
}

void AIG::traverse(NodeRef ref, AIG &newAig,
                   vector<NodeRef> &oldRefToNewRef,
                   IDRefMap &oldRefOfId, RefIDMap &oldIdOfRef,
                   IDRefMap &newRefOfId, RefIDMap &newIdOfRef)
{
  //Terminal cases: false, true, already visited
  if(ref == 0 || ref == 1 ||
      oldRefToNewRef[UIGET(ref)] != ULONG_MAX) return;

  //Get the index of this reference
  NodeIndex index = indexOf(ref);
  //Get the AIG node
  AIGNode& node = _nodes[UIGET(index)];
  
  //Get the children of this node
  NodeRef fanin1ref = node[0];
  bool isInverted1 = false;
  if(isNot(fanin1ref)) {
    fanin1ref = invert(fanin1ref);
    isInverted1 = true;
  }
  //Get the AIG reference of the node it has been merged with
  while(fanin1ref != _merged[UIGET(indexOf(fanin1ref))]) {
    fanin1ref = _merged[UIGET(indexOf(fanin1ref))];
    if(isNot(fanin1ref)) {
      fanin1ref = invert(fanin1ref);
      isInverted1  ^= true;
    }
  }
  traverse(fanin1ref, newAig, oldRefToNewRef,
      oldRefOfId, oldIdOfRef, newRefOfId, newIdOfRef);

  NodeRef fanin2ref = node[1];
  bool isInverted2 = false;
  if(isNot(fanin2ref)) {
    fanin2ref = invert(fanin2ref);
    isInverted2 = true;
  }
  //Get the AIG reference of the node it has been merged with
  while(fanin2ref != _merged[UIGET(indexOf(fanin2ref))]) {
    fanin2ref = _merged[UIGET(indexOf(fanin2ref))];
    if(isNot(fanin2ref)) {
      fanin2ref = invert(fanin2ref);
      isInverted2  ^= true;
    }
  }
  traverse(fanin2ref, newAig, oldRefToNewRef,
      oldRefOfId, oldIdOfRef, newRefOfId, newIdOfRef);

  //Add the AIG node
  assert(oldRefToNewRef[UIGET(fanin1ref)] != ULONG_MAX);
  NodeRef newFanin1ref = oldRefToNewRef[UIGET(fanin1ref)];
  assert(oldRefToNewRef[UIGET(fanin2ref)] != ULONG_MAX);
  NodeRef newFanin2ref = oldRefToNewRef[UIGET(fanin2ref)];
  if(isInverted1) newFanin1ref = invert(newFanin1ref);
  if(isInverted2) newFanin2ref = invert(newFanin2ref);
  NodeIndex newIndex = newAig.addNode(newFanin1ref, newFanin2ref);
  //Add it to the map
  assert(!isNot(ref));
  oldRefToNewRef[UIGET(ref)] = refOf(newIndex, false);
  newRefOfId.insert(IDRefMap::value_type(oldIdOfRef[ref],
      refOf(newIndex, false)));
  newIdOfRef.insert(RefIDMap::value_type(refOf(newIndex, false),
      oldIdOfRef[ref]));
}

void AIG::update(AIGAttachment * aat)
{
  IDRefMap& oldRefOfId = aat->id2ref;
  RefIDMap& oldIdOfRef = aat->ref2id;

  //Create a new AIG
  AIG newAig;

  //Create a map from the old AIG reference to the new AIG reference
  vector<NodeRef> oldRefToNewRef(2 * size(), ULONG_MAX);
  oldRefToNewRef[0] = 0;
  oldRefToNewRef[1] = 1;

  //Create new id2ref and ref2id maps
  IDRefMap newRefOfId;
  RefIDMap newIdOfRef;
  //Insert the false and true nodes (AIG ref 0 = false, ref 1 = true)
  newRefOfId.insert(IDRefMap::value_type(oldIdOfRef[0], 0));
  newRefOfId.insert(IDRefMap::value_type(oldIdOfRef[1], 1));
  newIdOfRef.insert(RefIDMap::value_type(0, oldIdOfRef[0]));
  newIdOfRef.insert(RefIDMap::value_type(1, oldIdOfRef[1]));

  //Add all inputs and state variables to the new AIG
  for(unsigned i = 1; i <= _numInputs + _numStateVars; ++i) {
    NodeIndex index = newAig.addNode();
    assert(i == index);
    NodeRef newRef = refOf(index, false);
    NodeRef oldRef = refOf(i, false);
    //They should be equal
    assert(oldRef == newRef);
    oldRefToNewRef[UIGET(oldRef)] = newRef;
    assert(oldIdOfRef.find(oldRef) != oldIdOfRef.end());
    newRefOfId.insert(IDRefMap::value_type(oldIdOfRef[oldRef], newRef));
    newIdOfRef.insert(RefIDMap::value_type(newRef, oldIdOfRef[oldRef]));
  }
  //Set the number of inputs and state variables in the AIG
  newAig._numInputs = _numInputs;
  newAig._numStateVars = _numStateVars;

  for(unsigned i = 0; i < _nextStateFnRefs.size(); ++i) {
    //Get the AIG reference corresponding to this next state function
    NodeRef ref = _nextStateFnRefs[i];
    bool isInverted = false;
    if(isNot(ref)) {
      ref = invert(ref);
      isInverted = true;
    }
    //Get the AIG reference of the node it has been merged with: keep looping
    //until we hit a node that is merged with itself (i.e. not merged)
    while(ref != _merged[UIGET(indexOf(ref))]) {
      //Get the AIG reference of the node it has been merged with
      ref = _merged[UIGET(indexOf(ref))];
      if(isNot(ref)) {
        ref = invert(ref);
        //Flip the isInverted flag
        isInverted ^= true;
      }
    }

    //Recursively build the AIG for this node
    traverse(ref, newAig, oldRefToNewRef, oldRefOfId, oldIdOfRef, newRefOfId,
        newIdOfRef);
   
    //Update the id2ref and nextStateFnRefs
    assert(oldIdOfRef.find(_nextStateFnRefs[i]) != oldIdOfRef.end());
    assert(oldRefToNewRef[UIGET(ref)] != ULONG_MAX);
    if(isInverted) {
      newAig._nextStateFnRefs.push_back(invert(oldRefToNewRef[UIGET(ref)]));
      newRefOfId.insert(IDRefMap::value_type(oldIdOfRef[_nextStateFnRefs[i]],
          invert(oldRefToNewRef[UIGET(ref)])));
      newIdOfRef.insert(RefIDMap::value_type(
          invert(oldRefToNewRef[UIGET(ref)]),
          oldIdOfRef[_nextStateFnRefs[i]]));
    }
    else {
      newAig._nextStateFnRefs.push_back(oldRefToNewRef[UIGET(ref)]);
      newRefOfId.insert(IDRefMap::value_type(oldIdOfRef[_nextStateFnRefs[i]],
          oldRefToNewRef[UIGET(ref)]));
      newIdOfRef.insert(RefIDMap::value_type(oldRefToNewRef[UIGET(ref)],
          oldIdOfRef[_nextStateFnRefs[i]]));
    }
  }
  assert(newAig._nextStateFnRefs.size() == _nextStateFnRefs.size());

  //Outputs
  for(unsigned i = 0; i < _outputFnRefs.size(); ++i) {
    //Get the AIG reference corresponding to this output function
    NodeRef ref = _outputFnRefs[i];
    bool isInverted = false;
    if(isNot(ref)) {
      ref = invert(ref);
      isInverted = true;
    }
    //Get the AIG reference of the node it has been merged with
    //Keep looping until we hit a node that is merged with itself (i.e. not
    //merged)
    while(ref != _merged[UIGET(indexOf(ref))]) {
      //Get the AIG reference of the node it has been merged with
      ref = _merged[UIGET(indexOf(ref))];
      if(isNot(ref)) {
        ref = invert(ref);
        //Flip the isInverted flag
        isInverted ^= true;
      }
    }
    //Recursively build the AIG for this node
    traverse(ref, newAig, oldRefToNewRef, oldRefOfId, oldIdOfRef, newRefOfId,
        newIdOfRef);
    
    //Update the id2ref and outputFnRefs
    assert(oldIdOfRef.find(_outputFnRefs[i]) != oldIdOfRef.end());
    assert(oldRefToNewRef[UIGET(ref)] != ULONG_MAX);
    if(isInverted) {
      newAig._outputFnRefs.push_back(invert(oldRefToNewRef[UIGET(ref)]));
      newRefOfId.insert(IDRefMap::value_type(oldIdOfRef[_outputFnRefs[i]],
          invert(oldRefToNewRef[UIGET(ref)])));
      newIdOfRef.insert(RefIDMap::value_type(
          invert(oldRefToNewRef[UIGET(ref)]),
          oldIdOfRef[_outputFnRefs[i]]));
    }
    else {
      newAig._outputFnRefs.push_back(oldRefToNewRef[UIGET(ref)]);
      newRefOfId.insert(IDRefMap::value_type(oldIdOfRef[_outputFnRefs[i]],
          oldRefToNewRef[UIGET(ref)]));
      newIdOfRef.insert(RefIDMap::value_type(oldRefToNewRef[UIGET(ref)],
          oldIdOfRef[_outputFnRefs[i]]));
    }
  }
  assert(newAig._outputFnRefs.size() == _outputFnRefs.size());

  //Bad state properties
  for(unsigned i = 0; i < _badFnRefs.size(); ++i) {
    //Get the AIG reference corresponding to this output function
    NodeRef ref = _badFnRefs[i];
    bool isInverted = false;
    if(isNot(ref)) {
      ref = invert(ref);
      isInverted = true;
    }
    //Get the AIG reference of the node it has been merged with
    //Keep looping until we hit a node that is merged with itself (i.e. not
    //merged)
    while(ref != _merged[UIGET(indexOf(ref))]) {
      //Get the AIG reference of the node it has been merged with
      ref = _merged[UIGET(indexOf(ref))];
      if(isNot(ref)) {
        ref = invert(ref);
        //Flip the isInverted flag
        isInverted ^= true;
      }
    }
    //Recursively build the AIG for this node
    traverse(ref, newAig, oldRefToNewRef, oldRefOfId, oldIdOfRef, newRefOfId,
        newIdOfRef);
    
    //Update the id2ref and badFnRefs
    assert(oldIdOfRef.find(_badFnRefs[i]) != oldIdOfRef.end());
    assert(oldRefToNewRef[UIGET(ref)] != ULONG_MAX);
    if(isInverted) {
      newAig._badFnRefs.push_back(invert(oldRefToNewRef[UIGET(ref)]));
      newRefOfId.insert(IDRefMap::value_type(oldIdOfRef[_badFnRefs[i]],
          invert(oldRefToNewRef[UIGET(ref)])));
      newIdOfRef.insert(RefIDMap::value_type(
          invert(oldRefToNewRef[UIGET(ref)]),
          oldIdOfRef[_badFnRefs[i]]));
    }
    else {
      newAig._badFnRefs.push_back(oldRefToNewRef[UIGET(ref)]);
      newRefOfId.insert(IDRefMap::value_type(oldIdOfRef[_badFnRefs[i]],
          oldRefToNewRef[UIGET(ref)]));
      newIdOfRef.insert(RefIDMap::value_type(oldRefToNewRef[UIGET(ref)],
          oldIdOfRef[_badFnRefs[i]]));
    }
  }

  //Invariant constraints
  for(unsigned i = 0; i < _constraintFnRefs.size(); ++i) {
    //Get the AIG reference corresponding to this output function
    NodeRef ref = _constraintFnRefs[i];
    bool isInverted = false;
    if(isNot(ref)) {
      ref = invert(ref);
      isInverted = true;
    }
    //Get the AIG reference of the node it has been merged with
    //Keep looping until we hit a node that is merged with itself (i.e. not
    //merged)
    while(ref != _merged[UIGET(indexOf(ref))]) {
      //Get the AIG reference of the node it has been merged with
      ref = _merged[UIGET(indexOf(ref))];
      if(isNot(ref)) {
        ref = invert(ref);
        //Flip the isInverted flag
        isInverted ^= true;
      }
    }
    //Recursively build the AIG for this node
    traverse(ref, newAig, oldRefToNewRef, oldRefOfId, oldIdOfRef, newRefOfId,
        newIdOfRef);
    
    //Update the id2ref and constraintFnRefs
    assert(oldIdOfRef.find(_constraintFnRefs[i]) != oldIdOfRef.end());
    assert(oldRefToNewRef[UIGET(ref)] != ULONG_MAX);
    if(isInverted) {
      newAig._constraintFnRefs.push_back(invert(oldRefToNewRef[UIGET(ref)]));
      newRefOfId.insert(IDRefMap::value_type(oldIdOfRef[_constraintFnRefs[i]],
          invert(oldRefToNewRef[UIGET(ref)])));
      newIdOfRef.insert(RefIDMap::value_type(
          invert(oldRefToNewRef[UIGET(ref)]),
          oldIdOfRef[_constraintFnRefs[i]]));
    }
    else {
      newAig._constraintFnRefs.push_back(oldRefToNewRef[UIGET(ref)]);
      newRefOfId.insert(IDRefMap::value_type(oldIdOfRef[_constraintFnRefs[i]],
          oldRefToNewRef[UIGET(ref)]));
      newIdOfRef.insert(RefIDMap::value_type(oldRefToNewRef[UIGET(ref)],
          oldIdOfRef[_constraintFnRefs[i]]));
    }
  }

  //Justice properties
  for(unsigned i = 0; i < _justiceFnSetRefs.size(); ++i) {
    newAig._justiceFnSetRefs.push_back(vector<NodeRef>());
    for(unsigned j = 0; j < _justiceFnSetRefs[i].size(); ++j) {
      //Get the AIG reference corresponding to this output function
      NodeRef ref = _justiceFnSetRefs[i][j];
      bool isInverted = false;
      if(isNot(ref)) {
        ref = invert(ref);
        isInverted = true;
      }
      //Get the AIG reference of the node it has been merged with
      //Keep looping until we hit a node that is merged with itself (i.e. not
      //merged)
      while(ref != _merged[UIGET(indexOf(ref))]) {
        //Get the AIG reference of the node it has been merged with
        ref = _merged[UIGET(indexOf(ref))];
        if(isNot(ref)) {
          ref = invert(ref);
          //Flip the isInverted flag
          isInverted ^= true;
        }
      }
      //Recursively build the AIG for this node
      traverse(ref, newAig, oldRefToNewRef, oldRefOfId, oldIdOfRef, newRefOfId,
          newIdOfRef);
      
      //Update the id2ref and justiceFnSetRefs
      assert(oldIdOfRef.find(_justiceFnSetRefs[i][j]) != oldIdOfRef.end());
      assert(oldRefToNewRef[UIGET(ref)] != ULONG_MAX);
      if(isInverted) {
        newAig._justiceFnSetRefs[i].push_back(invert(oldRefToNewRef[UIGET(ref)]));
        newRefOfId.insert(IDRefMap::value_type(oldIdOfRef[_justiceFnSetRefs[i][j]],
            invert(oldRefToNewRef[UIGET(ref)])));
        newIdOfRef.insert(RefIDMap::value_type(
            invert(oldRefToNewRef[UIGET(ref)]),
            oldIdOfRef[_justiceFnSetRefs[i][j]]));
      }
      else {
        newAig._justiceFnSetRefs[i].push_back(oldRefToNewRef[UIGET(ref)]);
        newRefOfId.insert(IDRefMap::value_type(oldIdOfRef[_justiceFnSetRefs[i][j]],
            oldRefToNewRef[UIGET(ref)]));
        newIdOfRef.insert(RefIDMap::value_type(oldRefToNewRef[UIGET(ref)],
            oldIdOfRef[_justiceFnSetRefs[i][j]]));
      }
    }
  }

  //Fairness constraints
  for(unsigned i = 0; i < _fairnessFnRefs.size(); ++i) {
    //Get the AIG reference corresponding to this output function
    NodeRef ref = _fairnessFnRefs[i];
    bool isInverted = false;
    if(isNot(ref)) {
      ref = invert(ref);
      isInverted = true;
    }
    //Get the AIG reference of the node it has been merged with
    //Keep looping until we hit a node that is merged with itself (i.e. not
    //merged)
    while(ref != _merged[UIGET(indexOf(ref))]) {
      //Get the AIG reference of the node it has been merged with
      ref = _merged[UIGET(indexOf(ref))];
      if(isNot(ref)) {
        ref = invert(ref);
        //Flip the isInverted flag
        isInverted ^= true;
      }
    }
    //Recursively build the AIG for this node
    traverse(ref, newAig, oldRefToNewRef, oldRefOfId, oldIdOfRef, newRefOfId,
        newIdOfRef);
    
    //Update the id2ref and fairnessFnRefs
    assert(oldIdOfRef.find(_fairnessFnRefs[i]) != oldIdOfRef.end());
    assert(oldRefToNewRef[UIGET(ref)] != ULONG_MAX);
    if(isInverted) {
      newAig._fairnessFnRefs.push_back(invert(oldRefToNewRef[UIGET(ref)]));
      newRefOfId.insert(IDRefMap::value_type(oldIdOfRef[_fairnessFnRefs[i]],
          invert(oldRefToNewRef[UIGET(ref)])));
      newIdOfRef.insert(RefIDMap::value_type(
          invert(oldRefToNewRef[UIGET(ref)]),
          oldIdOfRef[_fairnessFnRefs[i]]));
    }
    else {
      newAig._fairnessFnRefs.push_back(oldRefToNewRef[UIGET(ref)]);
      newRefOfId.insert(IDRefMap::value_type(oldIdOfRef[_fairnessFnRefs[i]],
          oldRefToNewRef[UIGET(ref)]));
      newIdOfRef.insert(RefIDMap::value_type(oldRefToNewRef[UIGET(ref)],
          oldIdOfRef[_fairnessFnRefs[i]]));
    }
  }



  //Replace the existing AIG with the new one
  _nodes = newAig._nodes;
  _merged = newAig._merged;
  _depth = newAig._depth;
  _fanouts = newAig._fanouts;
  _nextStateFnRefs = newAig._nextStateFnRefs;
  _outputFnRefs = newAig._outputFnRefs;
  _badFnRefs = newAig._badFnRefs;
  _constraintFnRefs = newAig._constraintFnRefs;
  _justiceFnSetRefs = newAig._justiceFnSetRefs;
  _fairnessFnRefs = newAig._fairnessFnRefs;
  _numInputs = newAig._numInputs;
  _numStateVars = newAig._numStateVars;

  oldRefOfId = newRefOfId;
  oldIdOfRef = newIdOfRef;
}

string AIG::dot() const
{
  ostringstream dot;
  dot << "digraph AIG {" << endl
      << "edge [dir=none];" << endl;
  //Do a first pass to print the variables as dot sinks
  dot << "{ rank=sink;" << endl;
  //Add the false node to the sinks
  dot << 0 << ";" << endl;
  for(unsigned i = 1; i < size(); ++i) {
    if(_nodes[i].isVar())
      dot << i << ";" << endl;
  }
  //Print all non-variable nodes with their edges
  dot << "}" << endl;
  for(unsigned i = 1; i < size(); ++i) {
    if(!_nodes[i].isVar()) {
      dot << i << " -> " << indexOf(_nodes[i][0]) << ";" << endl;
      dot << i << " -> " << indexOf(_nodes[i][1]) << ";" << endl;
   }
  }
  dot << "}" << endl;
  return dot.str();
}

string AIG::dot(NodeRef ref)
{
  ostringstream dot;
  dot << "digraph AIG {" << endl
      << "edge [dir=none];" << endl;
  //Do a first pass to get the variables and print them as dot sinks
  set<NodeIndex> vars;
  ::traverse(this, indexOf(ref), vars);
  dot << "{ rank=sink;" << endl;
  for(set<NodeIndex>::iterator it = vars.begin(); it != vars.end(); ++it) {
    dot << *it << ";" << endl;
  }
  set<NodeIndex> cone;
  getCone(this, indexOf(ref), cone);
  //Print all non-variable nodes with their edges
  dot << "}" << endl;
  if(isNot(ref)) {
    dot << "inv" << indexOf(ref) << " [label=\"!\"];" << endl;
    dot << "inv" << indexOf(ref) << " -> " << indexOf(ref) << ";" << endl;
  }
  for(unsigned i = 1; i < size(); ++i) {
    if(!_nodes[i].isVar()) {
      if(cone.find(indexOf(_nodes[i][0])) != cone.end() && cone.find(indexOf(_nodes[i][1])) != cone.end() ) {
        if(isNot(_nodes[i][0])) {
          dot << "inv" << indexOf(_nodes[i][0]) << " [label=\"!\"];" << endl;
          dot << i << " -> inv" << indexOf(_nodes[i][0]) << ";" << endl;
          dot << "inv" << indexOf(_nodes[i][0]) << " -> " << indexOf(_nodes[i][0]) << ";" << endl;
        }
        else
          dot << i << " -> " << indexOf(_nodes[i][0]) << ";" << endl;
        if(isNot(_nodes[i][1])) {
          dot << "inv" << indexOf(_nodes[i][1]) << " [label=\"!\"]; " << endl;
          dot << i << " -> inv" << indexOf(_nodes[i][1]) << ";" << endl;
          dot << "inv" << indexOf(_nodes[i][1]) << " -> " << indexOf(_nodes[i][1]) << ";" << endl;
        }
        else
          dot << i << " -> " << indexOf(_nodes[i][1]) << ";" << endl;
      }
   }
  }
  dot << "}" << endl;

  return dot.str();
}


void AIG::print()
{
  std::cout << "Printing AIG..." << std::endl;
  for (size_t i = 1; i < _nodes.size(); ++i) {
    long n0, n1;
    if (isNot(_nodes[i][0])) n0 = -UIGET(indexOf(_nodes[i][0]));
    else n0 = UIGET(indexOf(_nodes[i][0]));
    if (isNot(_nodes[i][1])) n1 = -UIGET(indexOf(_nodes[i][1]));
    else n1 = UIGET(indexOf(_nodes[i][1]));

    if (_nodes[i].isVar())
      std::cout << "Node " << std::setw(6) << i << ": "
                << std::setw(7) << "Null" << ", "
                << std::setw(7) << "Null" << "\t||";
    else
      std::cout << "Node " << std::setw(6) << i << ": "
                << std::setw(7) << n0 << ", "
                << std::setw(7) << n1 << "\t||";

    std::cout << std::setw(6) << std::right << _fanouts[i].size() << " Fanouts:";
    for (unordered_set<NodeIndex>::iterator j = _fanouts[i].begin(); j != _fanouts[i].end(); ++j) {
      std::cout << " " << *j;
    }
    std::cout << std::endl;
  }
}

void AIG::updateFanout(NodeIndex index)
{
  if (_nodes[UIGET(index)].isVar() || index == 0) return;

  NodeIndex ch0 = indexOf(_nodes[UIGET(index)][0]);
  if (_merged[UIGET(ch0)] != refOf(ch0, false))
    ch0 = indexOf(_merged[UIGET(ch0)]);
  NodeIndex ch1 = indexOf(_nodes[UIGET(index)][1]);
  if (_merged[UIGET(ch1)] != refOf(ch1, false))
    ch1 = indexOf(_merged[UIGET(ch1)]);

  if (_fanouts[UIGET(ch0)].empty())
    updateFanout(ch0);
  else {
    _fanouts[UIGET(ch0)].erase(index);
  }

  if (_fanouts[UIGET(ch1)].empty())
    updateFanout(ch1);
  else {
    _fanouts[UIGET(ch1)].erase(index);
  }
}

void printAIG(const AIG& aig)
{
  for( NodeIndex i = 1; i < aig.size(); ++i) {
    if(aig[i].isVar()) {
      ::std::cout << 2*i << ": Variable" << ::std::endl;
    } else {
      ::std::cout << 2*i << " " << aig[i][0] << " " << aig[i][1] << ::std::endl;
    }
  }
}

} // namespace Opt
