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

#include "BMC.h"
#include "COI.h"
#include "Error.h"
#include "Expr.h"
#include "ExprUtil.h"
#include "Model.h"
#include "SAT.h"
#include "Sim.h"
#include "SimUtil.h"
#include "ThreeValuedSimulation.h"
#include "Util.h"

#include <deque>
#include <set>
#include <unordered_map>
#include <vector>

using namespace std;

namespace {

  typedef Expr::IDVector Clause;
  typedef std::vector<Expr::IDVector> Clauses;

  typedef set<unsigned int> Indexes;
  typedef unordered_map<ID, Indexes> LitOccurMap;

  class State {
  public:
    State(Model & m, const Clauses & _cnf) : m(m), _cnf(_cnf) {
      v = m.newView();

      COIAttachment const * cat = (COIAttachment *) m.constAttachment(Key::COI);
      coi = cat->coi();
      m.constRelease(cat);

      ExprAttachment const * eat = (ExprAttachment *) m.constAttachment(Key::EXPR);
      latches = eat->stateVars();
      functions = eat->nextStateFnOf(latches);
      slatches = set<ID>(latches.begin(), latches.end());
      vector<ID> init = eat->initialConditions();
      m.constRelease(eat);

      // 1. build initial value map
      ThreeValued::Map sval;
      for (vector<ID>::const_iterator it = init.begin(); it != init.end(); ++it) {
        if (v->op(*it) == Expr::Not) {
          int n;
          const ID * args = v->arguments(*it, &n);
          assert (v->op(args[0]) == Expr::Var);
          sval.insert(ThreeValued::Map::value_type(args[0], ThreeValued::TVFalse));
        }
        else {
          assert (v->op(*it) == Expr::Var);
          sval.insert(ThreeValued::Map::value_type(*it, ThreeValued::TVTrue));
        }
      }
      svals.push_back(sval);
      svals_done = false;
      // 2. build lit-occurrence map
      litOccur(lito, _cnf);
    }
    ~State() {
      delete v;
    }

    void nextFrontier() {
      if (frontier_cnf.size() >= coi.size()) return;

      set<ID> kcoi = coi.kCOI(frontier_cnf.size());
      set<unsigned int> curri;
      deque<unsigned int> q;
      for (set<ID>::const_iterator it = kcoi.begin(); it != kcoi.end(); ++it)
        add_clauses(q, v->prime(*it));

      // 1. find clauses not included in (k-1) frontier that should be in k frontier
      while (!q.empty()) {
        unsigned int i = q.front();
        q.pop_front();
        curri.insert(i);
        const Clause & cl = _cnf[i];
        for (Clause::const_iterator it = cl.begin(); it != cl.end(); ++it) {
          if (slatches.find(*it) == slatches.end() && slatches.find(v->apply(Expr::Not, *it)) == slatches.end())
            add_clauses(q, *it);
        }
      }

      // 2. build clause vector
      frontier_cnf.push_back(Clauses());
      Clauses & cls = frontier_cnf.back();
      for (unsigned int i = 0; i < _cnf.size(); ++i)
        if (curri.find(i) != curri.end())
          cls.push_back(_cnf[i]);
    }

    const Clauses & cnf(unsigned int kf, bool _frontier = true) {
      if (_frontier && kf < frontier_cnf.size()) return frontier_cnf[kf];
      return _cnf;
    }

    unsigned int fsize() { return coi.size(); }

    bool simplify(unsigned int k, Clauses & cnf) {
      // 1. simulate up to k steps if necessary
      while (!svals_done && k >= svals.size()) {
        ThreeValued::Map curr(svals.back());
        ThreeValued::Folder f(*v, curr);
        v->fold(f, functions);
        ThreeValued::Map next;
        for (unsigned int i = 0; i < latches.size(); ++i) {
          ThreeValued::Map::const_iterator tvit = curr.find(functions[i]);
          if (tvit != curr.end() && tvit->second != ThreeValued::TVX)
            next.insert(ThreeValued::Map::value_type(latches[i], tvit->second));
        }
        if (next.size() > 0)
          svals.push_back(next);
        else
          svals_done = true;
      }
      if (k >= svals.size()) return false;

      // 2. simplify clauses according to k'th step values
      deque<ID> units;
      // unprimed: k-1
      const ThreeValued::Map & kval = svals[k-1];
      for (ThreeValued::Map::const_iterator it = kval.begin(); it != kval.end(); ++it)
        if (it->second == ThreeValued::TVTrue)
          units.push_back(it->first);
        else {
          assert (it->second == ThreeValued::TVFalse);
          units.push_back(v->apply(Expr::Not, it->first));
        }
      // primed: k
      const ThreeValued::Map & kvalp = svals[k];
      for (ThreeValued::Map::const_iterator it = kvalp.begin(); it != kvalp.end(); ++it)
        if (it->second == ThreeValued::TVTrue)
          units.push_back(v->prime(it->first));
        else {
          assert (it->second == ThreeValued::TVFalse);
          units.push_back(v->apply(Expr::Not, v->prime(it->first)));
        }
      // existing units
      for (Clauses::const_iterator it = cnf.begin(); it != cnf.end(); ++it)
        if (it->size() == 1)
          units.push_back((*it)[0]);
      return bcp(cnf, units);
    }

    void simulate(unsigned int nRuns, unsigned int depth, set<ID> & sim_cubes) {
      class ISim : public Sim::StateFunctor64 {
      public:
        ISim(State & s, unsigned int nRuns, set<ID> & sim_cubes) : 
          s(s), 
          nRuns(64 < nRuns ? 64 : nRuns), 
          sim_cubes(sim_cubes) 
        {}
        virtual bool operator()(vector<uint64_t>::const_iterator stateBegin, vector<uint64_t>::const_iterator stateEnd) {
          vector<ID> st[64];
          const vector<ID> & latches = s.latches;
          for (vector<ID>::const_iterator lit = latches.begin(); 
               stateBegin != stateEnd; stateBegin++, lit++) {
            assert (lit != latches.end());
            uint64_t v = *stateBegin;
            ID latch = *lit;
            ID nlatch = s.v->apply(Expr::Not, latch);
            for (unsigned int i = 0; i < nRuns; ++i) {
              v >>= 1;
              st[i].push_back(v & 1 ? latch : nlatch);
            }
          }
          bool changed = false;
          for (unsigned int i = 0; i < nRuns; ++i) {
            pair<set<ID>::iterator, bool> rv = sim_cubes.insert(s.v->apply(Expr::And, st[i]));
            changed |= rv.second;
          }
          return changed;
        }
      private:
        State & s;
        unsigned int nRuns;
        set<ID> & sim_cubes;
      };
      cout << "simulating\n";
      ISim isim(*this, nRuns, sim_cubes);
      for (unsigned int i = 0; i < nRuns; ++i)
        Sim::sequentialSimulateRandom64(m, depth, isim);
      cout << "end simulating\n";
    }

    Expr::Manager::View & view() { return *v; }

  private:
    Model & m;
    Expr::Manager::View * v;
    vector<ID> latches;
    vector<ID> functions;
    set<ID> slatches;
    COI coi;
    Clauses _cnf;

    LitOccurMap lito;

    vector<Clauses> frontier_cnf;
    set<unsigned int> fmarked;

    vector<ThreeValued::Map> svals;
    bool svals_done;

    void litOccur(LitOccurMap & lito, const Clauses & _cnf) {
      for (unsigned int i = 0; i < _cnf.size(); ++i)
        for (Clause::const_iterator it = _cnf[i].begin(); it != _cnf[i].end(); ++it) {
          LitOccurMap::iterator sit = lito.find(*it);
          if (sit == lito.end()) {
            pair<LitOccurMap::iterator, bool> rv = 
              lito.insert(LitOccurMap::value_type(*it, Indexes()));
            sit = rv.first;
          }
          sit->second.insert(i);
        }
    }

    void add_clauses(deque<unsigned int> & q, ID lit) {
      _add_clauses(q, lit);
      _add_clauses(q, v->apply(Expr::Not, lit));
    }
    void _add_clauses(deque<unsigned int> & q, ID lit) {
      LitOccurMap::const_iterator litit = lito.find(lit);
      if (litit != lito.end())
        for (Indexes::const_iterator iit = litit->second.begin(); 
             iit != litit->second.end(); ++iit)
          if (fmarked.find(*iit) == fmarked.end()) {
            q.push_back(*iit);
            fmarked.insert(*iit);
          }
    }

    bool bcp(Clauses & cnf, deque<ID> & units) {
      LitOccurMap lito;
      litOccur(lito, cnf);
      set<ID> done;
      while (!units.empty()) {
        ID lit = units.front();
        units.pop_front();
        if (done.find(lit) != done.end()) continue;
        done.insert(lit);
        ID nlit = v->apply(Expr::Not, lit);
        if (done.find(nlit) != done.end())
          return true;
        // 1. clear satisfied clauses
        LitOccurMap::const_iterator litit = lito.find(lit);
        if (litit != lito.end())
          for (Indexes::const_iterator iit = litit->second.begin(); 
               iit != litit->second.end(); ++iit)
            cnf[*iit].clear();
        // 2. falsify neg of lit and obtain any new units
        litit = lito.find(nlit);
        if (litit != lito.end())
          for (Indexes::const_iterator iit = litit->second.begin(); 
               iit != litit->second.end(); ++iit) {
            if (cnf[*iit].size() == 0) continue;
            for (Clause::iterator it = cnf[*iit].begin(); it != cnf[*iit].end(); ++it)
              if (*it == nlit) {
                *it = cnf[*iit].back();
                cnf[*iit].pop_back();
                break;
              }
            if (cnf[*iit].size() == 0)
              return true;
            if (cnf[*iit].size() == 1)
              units.push_back(cnf[*iit][0]);
          }
      }

      // remove trivial clauses
      for (Clauses::iterator it = cnf.begin(); it != cnf.end();)
        if (it->size() == 0) {
          *it = cnf.back();
          cnf.pop_back();
        }
        else
          ++it;

      // add units
      for (set<ID>::const_iterator it = done.begin(); it != done.end(); ++it) {
        vector<ID> ucls(1);
        ucls[0] = *it;
        cnf.push_back(ucls);
      }

      return false;
    }
  };

  void prime(Expr::Manager::View & v, int k, const Clauses & cnf, Clauses & rv) {
    for (Clauses::const_iterator it = cnf.begin(); it != cnf.end(); ++it)
      if (k == 0)
        rv.push_back(*it);
      else {
        Clause c;
        for (Clause::const_iterator lit = it->begin(); lit != it->end(); ++lit) {
          if(*lit == v.btrue() || *lit == v.bfalse())
            c.push_back(*lit);
          else
            c.push_back(v.prime(*lit, k));
        }
        rv.push_back(c);
      }
  }

}

namespace BMC {

  MC::ReturnValue check(Model & m, const BMCOptions & opts, vector<Transition> * cexTrace) {
    if (m.verbosity() > Options::Silent && !opts.silent)
      cout << "BMC: Checking up to " << *(opts.bound) << endl;
    int rseed = m.options()["rand"].as<int>();
    if(rseed != -1) {
      srand(rseed);
      Sim::RandomGenerator::generator.seed(static_cast<unsigned int>(rseed));
    }

    MC::ReturnValue rv;

    ExprAttachment const * eat = (ExprAttachment *) m.constAttachment(Key::EXPR);
    Expr::Manager::View * v = m.newView();

    // assumes AIGER 1.0
    // get initial condition and property
    vector<ID> init = eat->initialConditions();
    vector<ID> latches(eat->stateVars());
    vector<ID> inputs(eat->inputs());
    vector<ID> constraints(eat->constraints());
    ID npi = eat->outputFnOf(eat->outputs()[0]);
    ID pi = v->apply(Expr::Not, npi);

    m.constRelease(eat);

    if (pi == v->btrue()) {
      if (m.verbosity() > Options::Terse)
        cout << "BMC: The property holds trivially. (0)" << endl;
      rv.returnType = MC::Proof;
      delete v;
      return rv;
    }
    else if (pi == v->bfalse()) {
      if (m.verbosity() > Options::Terse)
        cout << "BMC: The property fails trivially. (0)" << endl;
      rv.returnType = MC::CEX;
      if(cexTrace) {
        cexTrace->resize(1);
        (*cexTrace)[0].state = init;
      }
      delete v;
      return rv;
    }

    // Get CNF encoding for next-state functions.
    CNFAttachment * cnfat = (CNFAttachment *) m.constAttachment(Key::CNF);
    vector< vector<ID> > cons_clauses = opts.useCOI ? cnfat->getCNF() : cnfat->getPlainCNF();
    m.constRelease(cnfat);

    if (m.verbosity() > Options::Informative)
      cout << "BMC: CNF size: " << cons_clauses.size() << endl;

    bool use_frontier = opts.useCOI;
    if (!opts.extra_pi.empty()) {
      use_frontier = false;
      vector<ID> ex;
      for (vector< vector<ID> >::const_iterator it = opts.extra_pi.begin(); it != opts.extra_pi.end(); ++it) {
        vector<ID> cls(*it);
        for (vector<ID>::iterator cit = cls.begin(); cit != cls.end(); ++cit)
          *cit = v->apply(Expr::Not, *cit);
        ex.push_back(v->apply(Expr::And, cls));
      }
      ex.push_back(npi);
      npi = v->apply(Expr::Or, ex);
    }

    State s(m, cons_clauses);
    SAT::Manager * sman = m.newSATManager();
    SAT::Manager::View * sv = sman->newView(s.view());

    Clauses npi_cnf;
    if(!opts.iictl) {
      Expr::tseitin(s.view(), npi, npi_cnf);
    }
    else {
      npi_cnf = *opts.iictl_clauses;
    }
    npi_cnf.insert(npi_cnf.end(), opts.bwd.begin(), opts.bwd.end());
    if(opts.constraints) {
      for (unsigned i = 0; i < opts.constraints->size(); ++i) {
        npi_cnf.insert(npi_cnf.end(), (*opts.constraints)[i].begin(),
                                      (*opts.constraints)[i].end());
      }
    }

    // assert initial condition
    if (!opts.sim)
      for (vector<ID>::const_iterator it = init.begin(); it != init.end(); ++it) {
        Clause c;
        c.push_back(*it);
        sv->add(c);
      }
    else {
      set<ID> sim_cubes;
      s.simulate(1, 1000, sim_cubes);
      Clauses ic_cnf;
      vector<ID> ic(sim_cubes.begin(), sim_cubes.end());
      cout << ic.size() << endl;
      Expr::tseitin(s.view(), v->apply(Expr::Or, ic), ic_cnf);
      cout << ic_cnf.size() << endl;
      sv->add(ic_cnf);
    }

    int64_t stime = Util::get_user_cpu_time();
    unsigned int k = 0;
    SAT::Assignment asgn;
    for (; k <= *(opts.bound); ++k) {
      int64_t sofar = Util::get_user_cpu_time() - stime;
      if (opts.timeout > 0 && sofar / 1000000 >= opts.timeout) {
        if (m.verbosity() > Options::Terse)
          cout << "BMC: timeout (1)" << endl;
        rv.returnType = MC::Unknown;
        break;
      }
      if (opts.timeout > 0) {
        double rem = (double) (opts.timeout - sofar / 1000000);
        sv->timeout(rem);
      }
      if (m.verbosity() > Options::Informative) {
        cout << "BMC: K = " << k;
        if (k < opts.lo) cout << "*";
        cout << endl;
      }

      // 1. add transition relation clauses
      if (k > 0) {
        if (use_frontier) s.nextFrontier();
        Clauses new_cnf;
        bool trivial = false;
        for (unsigned int i = k; i > 0 && k-i < s.fsize(); --i) {
          Clauses icnf = s.cnf(k-i, use_frontier);
          if (!opts.sim) {
            if (m.verbosity() > Options::Informative)
              cout << "BMC: (before simp) " << i << " " << icnf.size() << endl;
            if (s.simplify(i, icnf)) {
              if (m.verbosity() > Options::Terse)
                cout << "BMC: The property holds trivially. (1)" << endl;
              rv.returnType = MC::Proof;
              trivial = true;
              break;
            }
            if (m.verbosity() > Options::Informative)
              cout << "BMC: (after simp)  " << i << " " << icnf.size() << endl;
          }
          prime(s.view(), i-1, icnf, new_cnf);
        }
        if (trivial) break;
        try {
          sv->add(new_cnf);
        }
        catch (SAT::Trivial tv) {
          if (!tv.value()) {
            if (m.verbosity() > Options::Terse)
              cout << "BMC: The property holds trivially. (2)" << endl;
            rv.returnType = MC::Proof;
            break;
          }
        }
      }
      // 1.5. add forward clauses
      if (k == opts.lo) {
        try {
          SAT::Clauses fwd(opts.fwd);
          sv->add(fwd);
        }
        catch (...) {
          assert (false);
        }
      }

      if(opts.printCex) {
        //Clear current assignment
        for (SAT::Assignment::iterator it = asgn.begin(); it != asgn.end(); ++it)
          it->second = SAT::Unknown;
        //Add new variables to assignment
        //1) Add latches
        for (vector<ID>::const_iterator it = latches.begin(); it != latches.end(); ++it) {
          asgn.insert(SAT::Assignment::value_type(v->prime(*it, k), SAT::Unknown));
        }
        //2) Add inputs
        for (vector<ID>::const_iterator it = inputs.begin(); it != inputs.end(); ++it) {
          asgn.insert(SAT::Assignment::value_type(v->prime(*it, k), SAT::Unknown));
        }
      }

      // 2. add temporary error clauses and backward clauses
      if (k >= opts.lo) {
        Clauses curr_npi;
        prime(s.view(), k, npi_cnf, curr_npi);
        SAT::GID tgid = sv->newGID();
        bool trivial = false;
        try {
          sv->add(curr_npi, tgid);
        }
        catch (SAT::Trivial tv) {
          if (tv.value()) {
            if (m.verbosity() > Options::Terse)
              cout << "BMC: The property fails trivially. (1)" << endl;
            cexTrace->resize(1);
            (*cexTrace)[0].state = init;
            rv.returnType = MC::CEX;
            break;
          }
          else
            trivial = true;
        }
        if (k == 0) {
          //add invariant constraints
          vector< vector<ID> > constraint_clauses;
          Expr::tseitin(s.view(), constraints, constraint_clauses);
          try {
            sv->add(constraint_clauses, tgid);
          }
          catch (SAT::Trivial tv) {
            if (!tv.value()) {
              if (m.verbosity() > Options::Terse) {
                cout << "BMC: The property holds trivially. (A constraint "
                     << "is equivalent to false)" << endl;
              }
              rv.returnType = MC::Proof;
              break;
            }
          }
        }
        // 3. check sat
        bool sat;
        if(!opts.printCex) {
          for (vector<ID>::const_iterator it = latches.begin(); it != latches.end(); ++it)
            asgn.insert(SAT::Assignment::value_type(v->prime(*it, k), SAT::Unknown));
        }
        try {
          sat = trivial ? false : sv->sat(NULL, &asgn);
        }
        catch (Timeout e) {
          if (m.verbosity() > Options::Terse)
            cout << "BMC: timeout (2)" << endl;
          rv.returnType = MC::Unknown;
          break;
        }
        // 4. remove temporary clauses
        sv->remove(tgid);
        if (sat) {
          rv.returnType = MC::CEX;
          if(opts.printCex) {
            cexTrace->resize(k + 1);
            ExprAttachment const * eat = (ExprAttachment *) m.constAttachment(Key::EXPR);
            for (SAT::Assignment::const_iterator it = asgn.begin();
                it != asgn.end(); ++it) {
              if(it->second != SAT::Unknown) {
                unsigned numPrimes = v->nprimes(it->first);
                assert(numPrimes <= k);
                ID id = v->unprime(it->first, numPrimes);
                if(eat->isInput(id)) {
                  (*cexTrace)[numPrimes].inputs.push_back(
                      it->second == SAT::False ?
                      v->apply(Expr::Not, id) :
                      id);
                }
                else {
                  (*cexTrace)[numPrimes].state.push_back(
                      it->second == SAT::False ?
                      v->apply(Expr::Not, id) :
                      id);
                }
              }
            }
            m.constRelease(eat);
          }
          else {
            vector<ID> cube;
            for (SAT::Assignment::const_iterator it = asgn.begin(); it != asgn.end(); ++it)
              if (it->second != SAT::Unknown) {
                ID var = v->primeTo(it->first, 0);
                cube.push_back(it->second == SAT::False ? 
                               v->apply(Expr::Not, var) :
                               var);
              }
            rv.counterexample.push_back(cube);
          }
          break;
        }
      }
      if (k == *(opts.bound))
        rv.returnType = MC::Unknown;
    }
    *(opts.bound) = k;

    delete v;
    delete sv;
    delete sman;
    return rv;
  }

}

namespace BMC {

  void BMCAction::exec()  {
      BMC::BMCOptions opts;

      size_t k = 0;
      opts.bound = &k;
      if (options().count("bmc_bound"))
        k = options()["bmc_bound"].as<unsigned int>();
      if (options().count("bmc_timeout"))
        opts.timeout = options()["bmc_timeout"].as<int>();

      RchAttachment const * rat = (RchAttachment *) model().constAttachment(Key::RCH);
      opts.lo = rat->cexLowerBound();

      Expr::Manager::View * ev = model().newView();
      SAT::Clauses fwd;
      SAT::Clauses bwd;
      for (int i = opts.lo+2; i > 0; --i) {
        if (rat->kForwardUpperBound(i, fwd))
          prime(*ev, i, fwd, opts.fwd);
        if (rat->kBackwardUpperBound(i, bwd))
          prime(*ev, -i, bwd, opts.bwd);
      }
      if (model().verbosity() > Options::Informative) {
        cout << "BMC: using " << fwd.size() << " forward clauses\n";
        cout << "BMC: using " << bwd.size() << " backward clauses\n";
      }
      delete ev;
      model().constRelease(rat);

      opts.sim = options().count("bmc_isim");
      opts.printCex = options().count("print_cex");
      vector<Transition> cex;
      MC::ReturnValue rv = BMC::check(model(), opts, opts.printCex ? &cex : NULL);
      if (rv.returnType != MC::Unknown) {
        ProofAttachment * pat = (ProofAttachment *) model().attachment(Key::PROOF);
        if (rv.returnType == MC::Proof)
          pat->setConclusion(0);
        else if (rv.returnType == MC::CEX) {
          pat->setConclusion(1);
          if(opts.printCex)
            pat->setCex(cex);
        }
        model().release(pat);
      }
      else if (k > opts.lo) {
        RchAttachment * rat = (RchAttachment *) model().attachment(Key::RCH);
        rat->updateCexLowerBound(k);
        model().release(rat);
      }
  }

}
