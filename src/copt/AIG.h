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

#ifndef _AIG_
#define _AIG_
#include<cstdlib> // for size_t

/** @file AIG.h */

#include "Expr.h"
#include "Model.h"
#include "UniqueIntegralType.h"
#include <unordered_map>
#include <unordered_set>

namespace Opt
{

class AIG;

#ifndef UNIQUE

typedef unsigned long NodeIndex;
typedef unsigned long NodeRef;

#else

typedef UniqueIntegralType<unsigned long, 0> NodeIndex;
typedef UniqueIntegralType<unsigned long, 1> NodeRef;

#endif

typedef std::unordered_map<ID, NodeRef> IDRefMap;
typedef std::unordered_map<NodeRef, ID> RefIDMap;

inline NodeRef invert(NodeRef ref) {
  return (UIGET(ref) ^ 0x1);
}
inline NodeRef refOf(NodeIndex index, bool c) {
  NodeRef ref = UIGET(index) << 0x1;
  return (c ? invert(ref) : ref);
}
inline NodeIndex indexOf(NodeRef ref) {
  return (UIGET(ref) >> 1);
}
inline bool isNot(NodeRef ref) {
  return (UIGET(ref) & 0x1);
}

} // namespace Opt

#include <cassert>
#include <vector>

class AIGAttachment;

namespace Opt
{

class AIG;

class AIGNode {
public:
  AIGNode();
  AIGNode(NodeRef arg0, NodeRef arg1);
  inline bool isVar() const;
  inline NodeRef operator[](size_t child) const;
  inline NodeRef& operator[](size_t child);
private:
  friend class AIG;
  NodeRef args[2];
};

class AIG {
public:
  AIG();
  inline const AIGNode& operator[](NodeIndex index) const;
  inline AIGNode& operator[](NodeIndex index);
  inline const std::vector<AIGNode>& nodes() const;
  inline NodeRef merged(NodeIndex index) const;
  inline size_t depth(NodeIndex index) const;
  inline size_t nFanout(NodeIndex index) const;
  inline size_t size() const;
  void resize(size_t new_size)
  {
    _nodes.resize(new_size);
  }
  void clear();

  NodeIndex addNode();
  NodeIndex addNode(NodeRef arg0, NodeRef arg1);

  void merge(NodeIndex index, NodeRef with, bool updateFanouts = true);
  void resetMerged();

  void update(AIGAttachment * aat);

  unsigned& numInputs() { return _numInputs; }
  const unsigned& numInputs() const { return _numInputs; }
  unsigned& numStateVars() { return _numStateVars; }
  const unsigned& numStateVars() const { return _numStateVars; }

  std::vector<NodeRef>& nextStateFnRefs() { return _nextStateFnRefs; }
  const std::vector<NodeRef>& nextStateFnRefs() const { return _nextStateFnRefs; }
  std::vector<NodeRef>& outputFnRefs() { return _outputFnRefs; }
  const std::vector<NodeRef>& outputFnRefs() const { return _outputFnRefs; }
  //For AIGER 1.9
  std::vector<NodeRef>& badFnRefs() { return _badFnRefs; }
  const std::vector<NodeRef>& badFnRefs() const { return _badFnRefs; }
  std::vector<NodeRef>& constraintFnRefs() { return _constraintFnRefs; }
  const std::vector<NodeRef>& constraintFnRefs() const { return _constraintFnRefs; }
  std::vector<std::vector<NodeRef> >& justiceFnSetRefs() { return _justiceFnSetRefs; }
  const std::vector< std::vector<NodeRef> >& justiceFnSetRefs() const { return _justiceFnSetRefs; }
  std::vector<NodeRef>& fairnessFnRefs() { return _fairnessFnRefs; }
  const std::vector<NodeRef>& fairnessFnRefs() const { return _fairnessFnRefs; }

  std::string dot() const;
  std::string dot(NodeRef ref);
  void print();
private:
  void traverse(NodeRef, AIG &, std::vector<NodeRef> &,
                IDRefMap &, RefIDMap &, IDRefMap &, RefIDMap &);
  void updateFanout(NodeIndex index);

  std::vector<AIGNode> _nodes;
  std::vector<NodeRef> _merged;
  std::vector<size_t> _depth;
  std::vector< std::unordered_set<NodeIndex> > _fanouts;
  std::vector<NodeRef> _nextStateFnRefs;
  std::vector<NodeRef> _outputFnRefs;
  //For AIGER 1.9
  std::vector<NodeRef> _badFnRefs;
  std::vector<NodeRef> _constraintFnRefs;
  std::vector<std::vector<NodeRef> > _justiceFnSetRefs;
  std::vector<NodeRef> _fairnessFnRefs;

  unsigned _numInputs;
  unsigned _numStateVars;
};

} // namespace Opt

#include <limits.h>

namespace Opt
{

bool AIGNode::isVar() const
{
  return (args[0] == ULONG_MAX && args[1] == ULONG_MAX);
}

NodeRef AIGNode::operator[](size_t child) const
{
  return args[child];
}

NodeRef& AIGNode::operator[](size_t child)
{
  return args[child];
}

} // namespace Opt

namespace Opt
{

const std::vector<AIGNode>& AIG::nodes() const
{
  return _nodes;
}

NodeRef AIG::merged(NodeIndex index) const
{
  return _merged[UIGET(index)];
}

const AIGNode& AIG::operator[](NodeIndex index) const
{
  return _nodes[UIGET(index)];
}

AIGNode& AIG::operator[](NodeIndex index)
{
  return _nodes[UIGET(index)];
}

/**
 * Returns the depth of the AIG node with the given index.
 * Depth is defined as the maximum of the depth of the node's fanouts. The
 * depth of variables is by definition zero.
 */
size_t AIG::depth(NodeIndex index) const
{
  return _depth[UIGET(index)];
}

size_t AIG::nFanout(NodeIndex index) const
{
  return _fanouts[UIGET(index)].size();
}

size_t AIG::size() const
{
  return _nodes.size();
}

void printAIG(const AIG& aig);

} // namespace Opt

#endif /* _AIG_ */
