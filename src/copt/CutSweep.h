/* -*- C++ -*- */

/********************************************************************
Copyright (c) 2010-2013, Regents of the University of Colorado

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

#ifndef _CutSweep_
#define _CutSweep_

/** @file CutSweep.h */

#include "options.h"
#include "Model.h"
#include "AIGAttachment.h"
#include "CombAttachment.h"

namespace Opt
{

void cutSweep(Model &model);

} // namespace Opt

namespace Action
{

class CutSweepAction : public Model::Action {
public:
  CutSweepAction(Model &model) : Model::Action(model)
  {
    AIGAttachment::Factory aaf;
    requires(Key::AIG, &aaf);
    CombAttachment::Factory caf;
    requires(Key::COMB, &caf);
  }
  void exec()
  {
    Opt::cutSweep(model());
  }
private:
  static ActionRegistrar action;
};

} // namespace Action

#include "cuddObj.hh"
#include <cassert>
#include <vector>
#include <sstream>
#include <unordered_map>
#include <algorithm>

namespace Opt
{

namespace Private
{

class Hash {
public:
  size_t operator()(const BDD &bdd) const
  {
    return hp(bdd.getNode());
  }
private:
  std::hash<DdNode *> hp;
};

class Equal {
public:
  bool operator()(const BDD &a, const BDD &b) const
  {
    return a == b;
  }
};

inline bool compareDepth(const std::pair<unsigned, unsigned> &a, const std::pair<unsigned, unsigned> &b)
{
  return a.second < b.second;
}

} // namespace Opt::Private

typedef std::unordered_map<BDD, int, Private::Hash, Private::Equal> CutIndexMap;

class CutSweepManager {
public:
  ~CutSweepManager()
  {
#if 0
    _bddmgr.info();
#endif
  }
  CutSweepManager() {}
  CutSweepManager(unsigned nvars, const std::vector<unsigned> &depth)
    : _bddmgr(nvars, 0, CUDD_UNIQUE_SLOTS/32),
      _bddI_to_aigI(), _aigI_to_cuts(nvars+1), _cut_to_aigI()
  {
#if 1
    std::vector<std::pair<unsigned, unsigned> > varorder(nvars);
    for (unsigned i = 0; i < nvars; ++i)
      varorder[i] = std::make_pair(i+1, depth[i+1]);
    std::stable_sort(varorder.begin(), varorder.end(), Private::compareDepth);

    for (unsigned i = 0; i < nvars; ++i) {
      _bddI_to_aigI.insert(std::make_pair(i, varorder[i].first));
      _aigI_to_cuts[varorder[i].first].push_back(_bddmgr.bddVar(i));
    }
#endif
#if 0
    for (unsigned i = 0; i < nvars; ++i) {
      _bddI_to_aigI.insert(std::make_pair(i, i+1));
      _aigI_to_cuts[i+1].push_back(_bddmgr.bddVar(i));
    }
#endif
  }
  inline unsigned AIGIndexOf(unsigned bddI) const
  {
    std::unordered_map<unsigned, unsigned>::const_iterator iter = _bddI_to_aigI.find(bddI);
    assert(iter != _bddI_to_aigI.end());
    return iter->second;
  }
  inline const std::vector<BDD>& getCutsOf(unsigned aigI) const
  {
    return _aigI_to_cuts[aigI];
  }
  inline const CutIndexMap& getCutIndexMap() const
  {
    return _cut_to_aigI;
  }
  inline CutIndexMap& getCutIndexMap()
  {
    return _cut_to_aigI;
  }
  inline void setCutsOf(unsigned aigI, const std::vector<BDD> &cuts)
  {
    _aigI_to_cuts[aigI].insert(_aigI_to_cuts[aigI].end(), cuts.begin(), cuts.end());
  }
  inline void setIndexOf(const BDD &cut, unsigned aigI)
  {
    _cut_to_aigI[cut] = aigI;
//      _cut_to_aigI.insert(CutIndexMap::value_type(cut, aigI));
  }
  std::string stringOf(const BDD &cut) const
  {
    std::vector<unsigned> support = cut.SupportIndices();
    std::stringstream ss;
    for (unsigned i = 0; i < support.size(); ++i) ss << AIGIndexOf(support[i]) << " ";
    return ss.str();
  }
private:
  Cudd _bddmgr;
  std::unordered_map<unsigned, unsigned> _bddI_to_aigI;
  std::vector<std::vector<BDD> > _aigI_to_cuts;
  CutIndexMap _cut_to_aigI;
};

} // namespace Opt

#endif // _CutSweep_
