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

#include "AIGUtil.h"

using namespace std;

namespace {

  using namespace Opt;

  vector<ID> or2(ID l1, ID l2) {
    vector<ID> lits;
    lits.push_back(l1);
    lits.push_back(l2);
    return lits;
  }

  ID rep(NodeRef ref, Expr::Manager::View& v, RefIDMap* satIdOfRef) {
    ostringstream buf;
    buf << "r" << ref;
    ID newId = v.newVar(buf.str());
    if(satIdOfRef != NULL) {
      satIdOfRef->insert(RefIDMap::value_type(ref, newId));
    }
    return newId;
  }

}

namespace Opt {

  ID buildClauses(const AIG& aig, NodeRef ref, Expr::Manager::View& v,
      vector<vector<ID> >& clauses, const RefIDMap& idOfAigRef, RefIDMap* satIdOfRef,
      vector<pair<bool, ID> >& visited) {
    if(ref == 0)
      return v.bfalse();
    if(ref == 1)
      return v.btrue();
    if(isNot(ref))
      return v.apply(Expr::Not, buildClauses(aig, invert(ref), v, clauses, idOfAigRef, satIdOfRef, visited));

    if(visited[UIGET(indexOf(ref))].first)
      return visited[UIGET(indexOf(ref))].second;
    if(aig[indexOf(ref)].isVar()) {
      assert(idOfAigRef.find(ref) != idOfAigRef.end());
      if(satIdOfRef != NULL) {
        satIdOfRef->insert(RefIDMap::value_type(ref, idOfAigRef.find(ref)->second));
      }
      return idOfAigRef.find(ref)->second;
    }

    ID r = rep(ref, v, satIdOfRef);
    visited[UIGET(indexOf(ref))].first = true;
    visited[UIGET(indexOf(ref))].second = r;
    ID nr = v.apply(Expr::Not, r);

    vector<ID> lits;
    NodeRef fanin1 = aig[indexOf(ref)][0];
    ID fanin1ID = buildClauses(aig, fanin1, v, clauses, idOfAigRef, satIdOfRef, visited);
    clauses.push_back(or2(nr, fanin1ID));
    lits.push_back(v.apply(Expr::Not, fanin1ID));

    NodeRef fanin2 = aig[indexOf(ref)][1];
    ID fanin2ID = buildClauses(aig, fanin2, v, clauses, idOfAigRef, satIdOfRef, visited);
    clauses.push_back(or2(nr, fanin2ID));
    lits.push_back(v.apply(Expr::Not, fanin2ID));

    lits.push_back(r);
    clauses.push_back(lits);

    return r;

  }

  ID tseitin(const AIG& aig, NodeRef ref, Expr::Manager::View& v, vector<vector<ID> >& clauses,
      const RefIDMap& idOfAigRef, RefIDMap* satIdOfRef, bool assert_roots) {
    
    vector<pair<bool, ID> > visited(aig.size(), pair<bool, ID>(false, 0));

    if(satIdOfRef != NULL) {
      satIdOfRef->insert(RefIDMap::value_type(0, v.bfalse()));
    }

    ID root = buildClauses(aig, ref, v, clauses, idOfAigRef, satIdOfRef, visited);
    if(assert_roots) {
      clauses.push_back(vector<ID>(1, root));
    }
    return root;
  }

  vector<ID> tseitin(const AIG& aig, const vector<NodeRef>& refs, Expr::Manager::View& v,
      vector<vector<ID> >& clauses, const RefIDMap& idOfAigRef, RefIDMap* satIdOfRef,
      bool assert_roots) {

    vector<pair<bool, ID> > visited(aig.size(), pair<bool, ID>(false, 0));

    if(satIdOfRef != NULL) {
      satIdOfRef->insert(RefIDMap::value_type(0, v.bfalse()));
    }

    vector<ID> retIds;
    for(unsigned i = 0; i < refs.size(); ++i) {
      ID root = buildClauses(aig, refs[i], v, clauses, idOfAigRef, satIdOfRef, visited);
      if(assert_roots) {
        clauses.push_back(vector<ID>(1, root));
      }
      retIds.push_back(root);
    }
    return retIds;
  }

  void countNodes(const AIG& aig, NodeRef ref, unsigned& count, vector<char>& visited) {
 
    if(isNot(ref))
      countNodes(aig, invert(ref), count, visited);

    NodeIndex index = indexOf(ref);
    if(visited[UIGET(index)] == 1) 
      return;

    ++count;
    visited[UIGET(index)] = 1;

    if(index == 0 || aig[index].isVar()) {
      return;
    }

    NodeRef fanin1 = aig[index][0];
    countNodes(aig, fanin1, count, visited);

    NodeRef fanin2 = aig[index][1];
    countNodes(aig, fanin2, count, visited);

  }

  unsigned sizeOf(const AIG& aig, NodeRef ref) {

    vector<char> visited(aig.size(), 0);
    unsigned count = 0;

    countNodes(aig, ref, count, visited);

    return count;
  }
               
  unsigned sizeOf(const AIG& aig, vector<NodeRef>& refs) {

    vector<char> visited(aig.size(), 0);

    unsigned total = 0;
    for(unsigned i = 0; i < refs.size(); ++i) {
      countNodes(aig, refs[i], total, visited);
    }

    return total;
  }

  unsigned nodeCount(const AIG& aig) {
    unsigned numNodes = 0;
    vector<NodeRef> all = aig.nextStateFnRefs();
    all.insert(all.end(), aig.outputFnRefs().begin(), aig.outputFnRefs().end());
    numNodes += sizeOf(aig, all);
    return numNodes;
  }
               
  void nodeDepth(const AIG &aig, NodeIndex index, vector<unsigned> &depth, vector<char> &seen)
  {
    if (seen[UIGET(index)] == 1) return;

    if (aig[index].isVar() || index == 0) return;

    NodeIndex i0 = indexOf(aig[index][0]), i1 = indexOf(aig[index][1]);
    depth[UIGET(i0)] = max(depth[UIGET(i0)], depth[UIGET(index)]+1);
    depth[UIGET(i1)] = max(depth[UIGET(i1)], depth[UIGET(index)]+1);

    nodeDepth(aig, i0, depth, seen);
    nodeDepth(aig, i1, depth, seen);

    seen[UIGET(index)] = 1;
  }

  void countDepth(const AIG &aig, std::vector<unsigned> &depth)
  {
    vector<char> seen(aig.size(), 0);
    depth.assign(aig.size(), 0);
    for (vector<NodeRef>::const_iterator i = aig.outputFnRefs().begin(); i != aig.outputFnRefs().end(); ++i)
      nodeDepth(aig, indexOf(*i), depth, seen);
    for (vector<NodeRef>::const_iterator i = aig.nextStateFnRefs().begin(); i != aig.nextStateFnRefs().end(); ++i)
      nodeDepth(aig, indexOf(*i), depth, seen);
  }
}
