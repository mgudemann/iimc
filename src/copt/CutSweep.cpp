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

#include "CutSweep.h"
#include "AIGUtil.h"
#include "Util.h"
#include <algorithm>

namespace
{

using namespace Opt;

class State {
public:
  State(Model &m, AIG &a)
    : mgr(0), aig(&a), verbosity(m.verbosity()), s(250), n(1),
      nGenerated(0), nUsed(0), nMerged(0), timeout(0), timeleft(0),
      done(false)
  {
    if (m.options().count("cutsweep_verbosity"))
      verbosity = (Options::Verbosity)m.options()["cutsweep_verbosity"].as<int>();

    if (m.options().count("cutsweep_nodeMax"))
      s = m.options()["cutsweep_nodeMax"].as<int>();

    if (m.options().count("cutsweep_cutMax"))
      n = m.options()["cutsweep_cutMax"].as<int>();

    const CombAttachment *cat = (CombAttachment *)m.constAttachment(Key::COMB);

    if (m.options().count("cutsweep_timeout")) {
      int64_t to = m.options()["cutsweep_timeout"].as<int>() * 1000000,
              un = cat->unusedTime();
      timeleft = timeout = to + un;
      if (verbosity > Options::Terse) {
        std::cout << "Cut Sweeping: timeout = " << to / 1000000.0 << "s";
        std::cout << " + " << un / 1000000.0 << "s" << std::endl;
      }
    } else {
      if (verbosity > Options::Terse)
        std::cout << "Cut Sweeping: timeout disabled" << std::endl;
    }

    if (cat->simplificationEffort() == CombAttachment::Complete) {
      if (verbosity > Options::Silent)
        std::cout << "Cut Sweeping: model has already been fully swept" << std::endl;
      done = true;
    }

    m.constRelease(cat);

    if (!done) {
      std::vector<unsigned> depth;
      countDepth(*aig, depth);
      mgr = new CutSweepManager(aig->size()-1, depth);
    }
  }

  ~State()
  {
    if (mgr != 0) delete mgr;
  }

  CutSweepManager *mgr;
  AIG *aig;
  Options::Verbosity verbosity;
  int s, n, nGenerated, nUsed, nMerged;
  int64_t timeout, timeleft;
  bool done;
};

BDD mergeCut(State &st, const BDD &a, bool sign_a, const BDD &b, bool sign_b)
{
  BDD bdd = (sign_a ? ~a : a) & (sign_b ? ~b : b);

  if (st.verbosity > Options::Verbose) {
    std::cout << "Cut Sweeping: conjoining two cuts with supports" << std::endl;
    std::cout << "  1: " << st.mgr->stringOf(a) << std::endl;
    std::cout << "  2: " << st.mgr->stringOf(b) << std::endl;
    std::cout << "  result: " << st.mgr->stringOf(bdd) << std::endl;
  }

  return bdd;
}

void replace(State &st, NodeIndex index, NodeRef with)
{
  NodeIndex from = index;
  NodeRef to = with;

  if (st.aig->depth(index) < st.aig->depth(indexOf(with))) {
    const std::vector<BDD> &vec = st.mgr->getCutsOf(UIGET(indexOf(with)));
    if (isNot(with)) {
      for (unsigned i = 0; i < vec.size(); ++i) {
        st.mgr->getCutIndexMap().erase(vec[i]);
        st.mgr->setIndexOf(~vec[i], UIGET(index));
      }
    } else {
      for (unsigned i = 0; i < vec.size(); ++i)
        st.mgr->setIndexOf(vec[i], UIGET(index));
    }
    from = indexOf(with);
    to = isNot(with) ? refOf(index, true) : refOf(index, false);
  }

  if (st.verbosity > Options::Informative) {
    int a = UIGET(from);
    int b = isNot(to) ? -(UIGET(indexOf(to))) : UIGET(indexOf(to));
    std::cout << "Cut Sweeping: merge node " << a << " with node " << b << std::endl;
  }
  st.aig->merge(from, to);
}

bool mergeEqvNodes(State &st, int index, const BDD &cut)
{
  CutIndexMap::const_iterator it = st.mgr->getCutIndexMap().find(cut);
  if (it != st.mgr->getCutIndexMap().end()) {
    replace(st, index, refOf(it->second, false));
    if (st.verbosity > Options::Verbose)
      std::cout << "Cut Sweeping: cut used: " << st.mgr->stringOf(cut) << std::endl;
    return true;
  }
  it = st.mgr->getCutIndexMap().find(~cut);
  if (it != st.mgr->getCutIndexMap().end()) {
    replace(st, index, refOf(it->second, true));
    if (st.verbosity > Options::Verbose)
      std::cout << "Cut Sweeping: cut used: " << st.mgr->stringOf(cut) << std::endl;
    return true;
  }
  return false;
}

bool mergeEqvNodes(State &st, int index, const std::vector<BDD> &cuts)
{
  for (unsigned i = 0; i < cuts.size(); ++i)
    if (mergeEqvNodes(st, index, cuts[i])) return true;

  if (st.verbosity > Options::Verbose)
    std::cout << "Cut Sweeping: no equivalence found for node "
              << index << " so far" << std::endl;

  return false;
}

bool buildCuts(State &st, int index, std::vector<BDD> &cuts)
{
  const AIGNode &node = (*st.aig)[index];
  if (node.isVar()) return true;

  NodeRef ref0 = isNot(node[0]) ?
    invert(st.aig->merged(indexOf(node[0]))) : st.aig->merged(indexOf(node[0]));
  int index0 = UIGET(indexOf(ref0));

  NodeRef ref1 = isNot(node[1]) ?
    invert(st.aig->merged(indexOf(node[1]))) : st.aig->merged(indexOf(node[1]));
  int index1 = UIGET(indexOf(ref1));

  if (st.verbosity > Options::Verbose) {
    int n0, n1;
    if (isNot(ref0)) n0 = -UIGET(indexOf(ref0));
    else n0 = UIGET(indexOf(ref0));
    if (isNot(ref1)) n1 = -UIGET(indexOf(ref1));
    else n1 = UIGET(indexOf(ref1));
    std::cout << "Cut Sweeping: " << n0 << ", " << n1 << std::endl;
  }

  if (ref0 == 0 || ref1 == 0) {
    replace(st, index, 0);
    return false;
  }
  if (ref0 == 1) {
    replace(st, index, ref1);
    return false;
  }
  if (ref1 == 1) {
    replace(st, index, ref0);
    return false;
  }

  const std::vector<BDD> &lcuts = st.mgr->getCutsOf(index0);
  const std::vector<BDD> &rcuts = st.mgr->getCutsOf(index1);

  for (unsigned i = 0; i < lcuts.size(); ++i) {
    if (lcuts[i].SupportSize() == 1 && st.aig->nFanout(index0) < 2)
      continue;
    for (unsigned j = 0; j < rcuts.size(); ++j) {
      if (rcuts[j].SupportSize() == 1 && st.aig->nFanout(index1) < 2)
        continue;

      BDD mergedCut = mergeCut(st, lcuts[i], isNot(ref0), rcuts[j], isNot(ref1));

      if (mergedCut.IsZero()) {
        replace(st, index, 0);
        return false;
      }
      if (mergedCut.IsOne()) {
        replace(st, index, 1);
        return false;
      }

      bool duplicated = false;
      for (unsigned k = 0; k < cuts.size(); ++k)
        if (cuts[k] == mergedCut) { duplicated = true; break; }
      if (!duplicated) cuts.push_back(mergedCut);
    }
  }

  return true;
}

template<typename T>
inline bool compare(const std::pair<unsigned, T> &a, const std::pair<unsigned, T> &b)
{
  return (a.second < b.second);
}

class NodeEraser {
public:
  NodeEraser(unsigned s) : threshold(s) {}
  bool operator()(const BDD &cut)
  {
    return (unsigned)cut.nodeCount() > threshold;
  }
private:
  unsigned threshold;
};

void removeLowQualityCut(State &st, std::vector<BDD> &cuts)
{
  cuts.erase(std::remove_if(cuts.begin(), cuts.end(), NodeEraser(st.s)), cuts.end());

  if (cuts.size() <= (unsigned)st.n) return;

  std::vector<std::pair<unsigned, float> > quality, height;

  for (unsigned i = 0; i < cuts.size(); ++i) {
    float q = 0, h = 0;
    std::vector<unsigned> support = cuts[i].SupportIndices();
    for (unsigned j = 0; j < support.size(); ++j) {
      q += 1.0 / st.aig->nFanout(st.mgr->AIGIndexOf(support[j]));
      h += st.aig->depth(st.mgr->AIGIndexOf(support[j]));
    }
    h /= support.size();
    quality.push_back(std::make_pair(i, q));
    height.push_back(std::make_pair(i, h));
  }
  std::sort(quality.begin(), quality.end(), compare<float>);
  std::vector<std::pair<unsigned, float> >::iterator
    miniter = std::min_element(height.begin(), height.end(), compare<float>);

  std::vector<BDD> vec;
  vec.push_back(cuts[miniter->first]);
  for (unsigned i = 0; vec.size() < (unsigned)st.n; ++i)
    if (quality[i].first != miniter->first) vec.push_back(cuts[quality[i].first]);

  cuts.assign(vec.begin(), vec.end());
}

void enumerateIthCut(State &st, int index)
{
  std::vector<BDD> cuts;
  if (!buildCuts(st, index, cuts)) {
    st.nMerged++;
    return;
  }

  if (st.verbosity > Options::Verbose) {
    std::cout << "Cut Sweeping: printing cuts for node " << index
              << " before pruning (one each line)..." << std::endl;
    for (unsigned i = 0; i < cuts.size(); ++i)
      std::cout << "  nodes: " << st.mgr->stringOf(cuts[i]) << std::endl;
  }

  st.nGenerated += cuts.size();

  bool foundmerge = mergeEqvNodes(st, index, cuts);
  if (foundmerge) { st.nMerged++; return; }

  for (unsigned i = 0; i < cuts.size(); ++i) st.mgr->setIndexOf(cuts[i], index);

  removeLowQualityCut(st, cuts);
  st.mgr->setCutsOf(index, cuts);

  if (st.verbosity > Options::Verbose) {
    std::cout << "Cut Sweeping: printing cuts for node " << index
              << " after pruning (one each line)..." << std::endl;
    for (unsigned i = 0; i < cuts.size(); ++i)
      std::cout << "  nodes: " << st.mgr->stringOf(cuts[i]) << std::endl;
  }

  st.nUsed += cuts.size();
}

void enumerate(State &st)
{
  int64_t start = Util::get_user_cpu_time();

  int ncutsofar = 0, ncutlast = 0;
  for (unsigned i = 1; i < st.aig->size(); ++i) {
    if (st.verbosity > Options::Verbose)
      std::cout << std::endl << "Cut Sweeping: enumerating node " << i << "..." << std::endl;
    if (!(*st.aig)[i].isVar()) enumerateIthCut(st, i);

    ncutsofar += st.nUsed - ncutlast;
    if (st.timeout != 0 && ncutsofar > 2000) {
      int64_t gone = Util::get_user_cpu_time() - start;
      if (gone >= st.timeout) {
        if (st.verbosity > Options::Silent) std::cout << "Cut Sweeping: timed out" << std::endl;
        break;
      }
      ncutsofar = 0;
    }
    ncutlast = st.nUsed;
  }

  st.timeleft = st.timeout - (Util::get_user_cpu_time() - start);

  if (st.verbosity > Options::Verbose) std::cout << std::endl;

  if (st.verbosity > Options::Silent)
    std::cout << "Cut Sweeping: found " << st.nMerged << " merges" << std::endl;

  if (st.verbosity > Options::Terse) {
    std::cout << "Cut Sweeping: generated " << st.nGenerated << " cuts" << std::endl;
    std::cout << "Cut Sweeping: used " << st.nUsed << " cuts in enumeration" << std::endl;
    if (st.timeout != 0 && st.timeleft > 0)
      std::cout << "Cut Sweeping: " << st.timeleft / 1000000.0 << "s left" << std::endl;
  }

  if (st.verbosity > Options::Terse) {
    int64_t end = Util::get_user_cpu_time();
    std::cout << "Cut Sweeping: " << (end - start) / 1000000.0
      << "s spent in sweeping" << std::endl;
  }
}

} // namespace

namespace Opt
{

void cutSweep(Model &model)
{
  AIGAttachment *aat = (AIGAttachment *)model.attachment(Key::AIG);

  State st(model, aat->aig);

  if (st.done) return;

  if (st.verbosity > Options::Silent)
    std::cout << "Cut Sweeping: before cut sweeping, AIG has "
              << nodeCount(aat->aig) << " nodes (Use -v4 to dump AIG)" << std::endl;
  if (st.verbosity > Options::Verbose)
    aat->aig.print();

  if (st.verbosity > Options::Silent)
    std::cout << "Cut Sweeping: in process "
      << "(s=" << st.s << ", N=" << st.n << ")..." << std::endl;

  enumerate(st);

  if (st.nMerged > 0) aat->aig.update(model);

  if (st.verbosity > Options::Silent)
    std::cout << "Cut Sweeping: new AIG has " << nodeCount(aat->aig) << " nodes" << std::endl;

  model.release(aat);

  CombAttachment *cat = (CombAttachment *)model.attachment(Key::COMB);

  cat->numEquivalences() += st.nMerged;
  if (st.timeout != 0) {
    if (st.timeleft > 0) cat->unusedTime() = st.timeleft;
    else cat->unusedTime() = 0;
  }

  model.release(cat);
}

} // namespace Opt
