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

#include "ExprUtil.h"
#include "SequentialEquivalence.h"
#include "Sim.h"

#include <set>
#include <unordered_map>
#include <vector>

using namespace std;

namespace {

  typedef vector< set<ID> > Partition;
  typedef unordered_map<ID, ID> FMap;
  typedef unordered_map< ID, set<ID> > IDIDSetMap;
  typedef unordered_map< ID, pair<set<ID>, ID> > CacheMap;

  class SimRefine : public Sim::StateFunctor64 {
  public:
    SimRefine(Model & m, Expr::Manager::View * _ev, Partition & _parts,
              FMap & _fmap) : ev(_ev), parts(_parts), fmap(_fmap) {
      ExprAttachment const * eat = (ExprAttachment *) m.constAttachment(Key::EXPR);
      const vector<ID> & latches = eat->stateVars();
      for (unsigned int i = 0; i < latches.size(); ++i)
        latchOrder.insert(OMap::value_type(latches[i], i));
      m.constRelease(eat);
    }

    virtual bool operator()(vector<uint64_t>::const_iterator stateBegin,
                            vector<uint64_t>::const_iterator stateEnd) {
      Partition newParts;
      for (Partition::iterator it = parts.begin(); it != parts.end(); ++it) {
        ID rep;
        uint64_t repVal;
        if (it->find(ev->bfalse()) != it->end()) {
          rep = ev->bfalse();
          repVal = 0;
        }
        else if (it->find(ev->btrue()) != it->end()) {
          rep = ev->btrue();
          repVal = 0xFFFFFFFFFFFFFFFFLL;
        }
        else {
          rep = *(it->begin());
          repVal = *(stateBegin + latchOrder[rep]);
        }
        set<ID> eq;
        ValIDSetMap neq;
        eq.insert(rep);
        for (set<ID>::const_iterator pit = it->begin(); pit != it->end(); ++pit) {
          if (*pit == rep) continue;
          uint64_t pitVal = *(stateBegin + latchOrder[*pit]);
          if (repVal == pitVal)
            eq.insert(*pit);
          else {
            neq[pitVal].insert(*pit);
          }
        }
        if (eq.size() > 1)
          newParts.push_back(eq);
        else
          fmap.erase(*(eq.begin()));
        for (ValIDSetMap::const_iterator classIt = neq.begin(); classIt != neq.end(); ++classIt) {
          if (classIt->second.size() > 1)
            newParts.push_back(classIt->second);
          else
            fmap.erase(*(classIt->second.begin()));
        }
      }
      parts = newParts;
      return (parts.size() > 0);
    }

  private:
    Expr::Manager::View * ev;
    Partition & parts;
    FMap & fmap;
    typedef unordered_map<ID, unsigned> OMap;
    typedef unordered_map< uint64_t, set<ID> > ValIDSetMap;
    OMap latchOrder;
  };

  class EqualFn {
  public:
    virtual bool operator()(ID f, ID g) = 0;
    virtual void reset() {}
  };

  class TrivialEq : public EqualFn {
  public:
    virtual bool operator()(ID f, ID g) { return (f == g); }
  };

  class VarEq : public EqualFn {
  public:
    VarEq(Expr::Manager::View & ev) : ev(ev) {}
    virtual bool operator()(ID f, ID g) {
      return (vars(f) == vars(g));
    }
    virtual void reset() {
      mem.clear();
    }
  private:
    Expr::Manager::View & ev;
    typedef unordered_map< ID, set<ID> > SMap;
    SMap mem;
    const set<ID> & vars(ID f) {
      SMap::iterator fit = mem.find(f);
      if (fit == mem.end()) {
        pair<SMap::iterator, bool> rv = mem.insert(SMap::value_type(f, set<ID>()));
        fit = rv.first;
        Expr::variables(ev, f, fit->second);
      }
      return fit->second;
    }
  };

  class SATEq : public EqualFn {
  public:
    SATEq(Model & model, Expr::Manager::View & ev) : model(model), ev(ev) {
      sman = model.newSATManager();
    }
    ~SATEq() {
      delete sman;
    }
    virtual bool operator()(ID f, ID g) {
      if (f == g) return true;
      if (ev.apply(Expr::Not, f) == g) return false;
      SAT::Manager::View * sview = sman->newView(ev);
      vector< vector<ID> > clauses;
      Expr::tseitin(ev, ev.apply(Expr::Not, ev.apply(Expr::Equiv, f, g)), clauses);
      sview->add(clauses);
      int rv = sview->sat();
      delete sview;
      return !rv;
    }
  private:
    Model & model;
    Expr::Manager::View & ev;
    SAT::Manager * sman;
  };

  bool refine(Expr::Manager::View * ev, Partition & parts, const FMap & roots, FMap & fmap, EqualFn & equal) {
    bool changed = false;
    Partition newParts;
    equal.reset();
    for (Partition::iterator it = parts.begin(); it != parts.end(); ++it) {
      ID rep, rrep;
      if (it->find(ev->bfalse()) != it->end()) {
        rep = ev->bfalse();
        rrep = ev->bfalse();
      }
      else if (it->find(ev->btrue()) != it->end()) {
        rep = ev->btrue();
        rrep = ev->btrue();
      }
      else {
        rep = *(it->begin());
        rrep = roots.find(rep)->second;
      }
      set<ID> eq;
      IDIDSetMap neq;
      eq.insert(rep);
      for (set<ID>::const_iterator pit = it->begin(); pit != it->end(); ++pit) {
        if (*pit == rep) continue;
        FMap::const_iterator rpit = roots.find(*pit);
        if (equal(rrep, rpit->second))
          eq.insert(*pit);
        else {
          neq[rpit->second].insert(*pit);
          changed = true;
        }
      }
      if (eq.size() > 1)
        newParts.push_back(eq);
      else
        fmap.erase(*(eq.begin()));
      for (IDIDSetMap::const_iterator classIt = neq.begin(); classIt != neq.end(); ++classIt) {
        if (classIt->second.size() > 1)
          newParts.push_back(classIt->second);
        else
          fmap.erase(*(classIt->second.begin()));
      }
    }
    parts = newParts;
    return changed;
  }

  void substitute(const set<ID> & support, set<ID> & subSupport, const FMap & lmap) {
    for (set<ID>::const_iterator it = support.begin(); it != support.end(); ++it) {
      FMap::const_iterator subIt = lmap.find(*it);
      ID sub = subIt != lmap.end() ? subIt->second : *it;
      subSupport.insert(sub);
    }
  }

  void iterate(Expr::Manager::View * ev, ExprAttachment * const eat, Partition & parts, FMap & fmap, const IDIDSetMap & nsfSupport, CacheMap & cache) {
    // 1. map each latch to its EC's representative
    FMap lmap;
    for (Partition::const_iterator it = parts.begin(); it != parts.end(); ++it) {
      set<ID>::const_iterator rep = it->begin();
      set<ID>::const_iterator pit = rep;
      for (++pit; pit != it->end(); ++pit)
        lmap.insert(FMap::value_type(*pit, *rep));
    }

    // 2. varSub the latch map to form new roots
    if (lmap.size() > 0) {
      vector<ID> roots;
      vector<ID> allRoots;
      vector<unsigned> indices;
      // assumes iteration in same order
      unsigned j = 0;
      for (FMap::const_iterator it = fmap.begin(); it != fmap.end(); ++it, ++j) {
        const set<ID> & support = nsfSupport.find(it->first)->second;
        set<ID> subSupport;
        substitute(support, subSupport, lmap);
        CacheMap::const_iterator cacheIt = cache.find(it->first);
        if (cacheIt == cache.end() || subSupport != cacheIt->second.first) {
          roots.push_back(it->second);
          indices.push_back(j);
          allRoots.push_back(ev->btrue()); //Arbitrary, will be replaced by roots
        }
        else {
          allRoots.push_back(cacheIt->second.second);
        }
      }
      Expr::varSub(*ev, lmap, roots);
      //Replace the nsfs that were varSubbed
      for (unsigned j = 0; j < indices.size(); ++j) {
        allRoots[indices[j]] = roots[j];
      }
      cache.clear();
      unsigned int i = 0;
      for (FMap::iterator it = fmap.begin(); it != fmap.end(); ++it, ++i) {
        it->second = allRoots[i];
        //Cache results
        const set<ID> & support = nsfSupport.find(it->first)->second;
        set<ID> subSupport;
        substitute(support, subSupport, lmap);
        cache.insert(CacheMap::value_type(it->first, make_pair(subSupport, allRoots[i])));
      }
    }
  }

}

void SequentialEquivalenceAction::exec() {
  TrivialEq teq;
  vector<EqualFn *> eqs;
  eqs.push_back(&teq);

  int rseed = model().options()["rand"].as<int>();
  if(rseed != -1)
    srand(rseed);

  ExprAttachment * const eat = (ExprAttachment *) model().constAttachment(Key::EXPR);

  Expr::Manager::View * ev = model().newView();

  FMap fmap;
  vector<ID> vars = eat->stateVars();
  for (vector<ID>::const_iterator it = vars.begin(); it != vars.end(); ++it)
    fmap.insert(FMap::value_type(*it, eat->nextStateFnOf(*it)));
 
  //uninitialized latches or those that get dropped out of ECs
  FMap singletonLatches = fmap; 

  // currently only works for AIGER 1.9 initial conditions
  Partition parts;
  set<ID> fpart, tpart;
  fpart.insert(ev->bfalse());
  tpart.insert(ev->btrue());
  vector<ID> init = eat->initialConditions();
  for (vector<ID>::const_iterator it = init.begin(); it != init.end(); ++it) {
    if (ev->op(*it) == Expr::Var) {
      tpart.insert(*it);
      singletonLatches.erase(*it);
    }
    else {
      fpart.insert(ev->apply(Expr::Not, *it));
      singletonLatches.erase(ev->apply(Expr::Not,*it));
    }
  }

  if (fpart.size() == 1 && tpart.size() == 1) {
    delete ev;
    return;
  }
  parts.push_back(fpart);
  parts.push_back(tpart);

  // Construct map of latches to fan-in latches.
  IDIDSetMap nsfSupport;
  for (vector<ID>::const_iterator it = vars.begin(); it != vars.end(); ++it) {
    set<ID> support;
    eat->supportStateVars(*ev, eat->nextStateFnOf(*it), support);
    nsfSupport.insert(IDIDSetMap::value_type(*it, support));
  }

  if (model().verbosity() > Options::Terse)
    cout << "SequentialEquivalenceAction starting" << endl;
  if (model().verbosity() > Options::Silent)
    cout << "SequentialEquivalence: Initial # latches = " << vars.size() << endl;

  //Refine classes
  if (model().verbosity() > Options::Informative)
    cout << "SequentialEquivalence: Simulation refinement" << endl;
  SimRefine simRefine(model(), ev, parts, fmap);
  sequentialSimulateRandom64(model(), 100, simRefine);

  CacheMap cache;
  ev->begin_local();
  for (vector<EqualFn *>::iterator eq = eqs.begin(); eq != eqs.end(); ++eq) {
    for (;;) {
      if (model().verbosity() > Options::Informative) {
        cout << " " << parts.size();
#if 0
        for (Partition::iterator it = parts.begin(); it != parts.end(); ++it)
          cout << " " << it->size();
#endif
        cout << endl;
      }
      FMap curr(fmap);
      iterate(ev, eat, parts, curr, nsfSupport, cache);
      if (!refine(ev, parts, curr, fmap, **eq)) {
        if (eq+1 == eqs.end()) {
          // globalize roots
          vector<ID> roots;
          for (FMap::const_iterator it = curr.begin(); it != curr.end(); ++it)
            roots.push_back(it->second);
          ev->global(roots);
          // make curr point to global roots
          unsigned int i = 0;
          for (FMap::iterator it = curr.begin(); it != curr.end(); ++it, ++i)
            it->second = roots[i];
          // save as fmap
          fmap = curr;
        }
        break;
      }
    }
  }
  ev->end_local();
  model().constRelease(eat);

  //Add latches that were dropped from ECs
  for (vector<ID>::const_iterator it = vars.begin(); it != vars.end(); ++it) {
    if (fmap.find(*it) == fmap.end())
      singletonLatches.insert(FMap::value_type(*it, eat->nextStateFnOf(*it)));
  }


  bool changed = false;
  for (Partition::const_iterator it = parts.begin(); it != parts.end(); ++it)
    if (it->size() > 1) {
      changed = true;
      break;
    }
  if (changed) {
    SeqAttachment * seqat = (SeqAttachment *) model().attachment(Key::SEQ);
    ExprAttachment * eat = (ExprAttachment *) model().attachment(Key::EXPR);

    FMap lmap;
    if(seqat->stateVars.empty()) {
      seqat->stateVars = eat->stateVars();
      seqat->nextStateFns = eat->nextStateFns();
    }
    eat->clearNextStateFns();
    map<ID, ID> latchToNsf;
    for (Partition::const_iterator it = parts.begin(); it != parts.end(); ++it) {
      // set next state function
      set<ID>::const_iterator rep = it->begin();
      if (*rep != ev->bfalse() && *rep != ev->btrue()) {
        FMap::const_iterator rit = fmap.find(*rep);
        latchToNsf.insert(map<ID, ID>::value_type(*rep, rit->second));
      }
      // build map of latch to representative latch
      set<ID>::const_iterator pit = rep;
      for (++pit; pit != it->end(); ++pit) {
        lmap.insert(FMap::value_type(*pit, *rep));
        seqat->optimized.insert(unordered_map<ID, ID>::value_type(*pit, *rep));
      }
    }
    for(FMap::const_iterator it = singletonLatches.begin();
        it != singletonLatches.end(); ++it) {
      ID nsf = Expr::varSub(*ev, lmap, it->second);
      latchToNsf.insert(map<ID, ID>::value_type(it->first, nsf));
    }
    for (map<ID, ID>::const_iterator it = latchToNsf.begin();
        it != latchToNsf.end(); ++it) {
      eat->setNextStateFn(it->first, it->second);
    }
    ev->keep(eat->nextStateFnOf(eat->stateVars()));

    if (model().verbosity() > Options::Silent)
      cout << "SequentialEquivalence: Final # latches = " << eat->stateVars().size() << endl;

    vector<ID> init(eat->initialConditions());
    if(seqat->initialConditions.empty())
      seqat->initialConditions = init;
    eat->clearInitialConditions();
    for (vector<ID>::iterator it = init.begin(); it != init.end(); ++it)
      if (Expr::varSub(*ev, lmap, *it) == *it)
        eat->addInitialCondition(*it);

    vector<ID> constraints(eat->constraints());
    vector<ID> constraintFns(eat->constraintFns());
    eat->clearConstraints();
    for (vector<ID>::size_type i = 0; i != constraintFns.size(); ++i) {
      //Changed by Zyad 11/08/2011
      //if (Expr::varSub(*ev, lmap, *it) == *it)
        //eat->addConstraint(*it);
      ID f = Expr::varSub(*ev, lmap, constraintFns[i]);
      eat->addConstraint(constraints[i], f);
    }
    ev->keep(eat->constraintFns());

    vector<ID> outputs(eat->outputs());
    vector<ID> outputFns(eat->outputFnOf(outputs));
    eat->clearOutputFns();
    Expr::varSub(*ev, lmap, outputFns);
    eat->setOutputFns(outputs, outputFns);
    ev->keep(outputFns);

    vector<ID> bad(eat->bad());
    vector<ID> badFns(eat->badFnOf(bad));
    eat->clearBadFns();
    Expr::varSub(*ev, lmap, badFns);
    eat->setBadFns(bad, badFns);
    ev->keep(badFns);

    vector<ID> fairness(eat->fairness());
    vector<ID> fairnessFns(eat->fairnessFnOf(fairness));
    eat->clearFairnessFns();
    Expr::varSub(*ev, lmap, fairnessFns);
    eat->setFairnessFns(fairness, fairnessFns);
    ev->keep(fairnessFns);

    vector<ID> justice(eat->justice());
    vector< vector<ID> > justiceS(eat->justiceSets());
    eat->clearJusticeSets();
    for (size_t i = 0; i < justiceS.size(); ++i) {
      Expr::varSub(*ev, lmap, justiceS[i]);
      eat->setJusticeSet(justice[i], justiceS[i]);
      ev->keep(justiceS[i]);
    }

    vector<ID> ctlProps(eat->ctlProperties());
    eat->clearCtlProperties();
    Expr::varSub(*ev, lmap, ctlProps);
    eat->addCtlProperties(ctlProps);

    model().release(eat);
    model().release(seqat);
  }
  else {
    if (model().verbosity() > Options::Silent)
      cout << "SequentialEquivalence: Final # latches = " << vars.size() << endl;
  }

  delete ev;
}
