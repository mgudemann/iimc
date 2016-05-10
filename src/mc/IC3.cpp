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

#include "FSIS.h"
#include "IC3.h"

#include "Error.h"
#include "Expr.h"
#include "ExprUtil.h"
#include "Model.h"
#include "SAT.h"
#include "Sim.h"
#include "SimUtil.h"
#include "Util.h"

#include <algorithm>
#include <deque>
#include <set>
#include <stdlib.h>
#include <unordered_map>
#include <vector>

#include <iostream>

#define HEIGHT 1
#define IBM_LIFTING

using namespace std;

namespace {
  
  using namespace IC3;

  class Stats {
  public:
    Stats() : level(0), cubeSizeBef(0), cubeSizeTACAS(0), cubeSizeIBM(0),
              cubeSizeBrute(0), numLiftCubes(0), ibmLiftTime(0), 
              bruteLiftTime(0), numBruteIter(0),
              numMicCalls(0), numUpCalls(0), numDownCalls(0),
              clauseSizeBef(0), clauseSizeAft(0), micTime(0) {
      numPropQueries.push_back(0);
      numClauses.push_back(0);
      percentProp.push_back(0);
      clauseDistBef.push_back(vector<uint64_t>());
      clauseDistAft.push_back(vector<uint64_t>());
      levInd.push_back(0);
      numGenCalls.push_back(0);
    }

    void print() {
      const string ic3 = "IC3: ";
      cout << endl;
      cout << "============================ IC3 Statistics ============================" << endl;
      cout << ic3 << "Final level reached = " << level << endl;
      for(unsigned i = 1; i < numPropQueries.size(); ++i) {
        cout << ic3 << "Number of property inductiveness queries at level "
             << i << " = " << numPropQueries[i] << endl;
      }
      for(unsigned i = 1; i < numClauses.size(); ++i) {
        cout << ic3 << "Number of clauses derived at level " << i << " = "
             << numClauses[i] << endl;
      }
      assert(numPropQueries.size() == numClauses.size());
      for(unsigned i = 1; i < numPropQueries.size(); ++i) {
        cout << ic3 << "Average number of clauses needed to eliminate a CTI at level "
              << i << " = " << numClauses[i] / (double) numPropQueries[i] << endl;
      }
      for(unsigned i = 1; i < clauseDistBef.size(); ++i) {
        cout << ic3 << "Clause distribution before propagation at level "
             << i << " = ";
        for(unsigned j = 0; j < clauseDistBef[i].size(); ++j) {
          cout << clauseDistBef[i][j] << " ";
        }
        cout << endl;
        if(i < clauseDistAft.size()) {
          cout << ic3 << "Clause distribution after propagation at level "
               << i << " = ";
          for(unsigned j = 0; j < clauseDistAft[i].size(); ++j) {
            cout << clauseDistAft[i][j] << " ";
          }
          cout << endl;
        }
      }

      for(unsigned i = 1; i < percentProp.size(); ++i) {
        cout << ic3 << "Average percentage of clauses propagated at level "
             << i << " = " << percentProp[i] * 100.0 << "%" << endl;
      }
      cout << ic3 << "Number of mic calls = " << numMicCalls << endl;
      cout << ic3 << "Total time spent in mic = " << micTime / 1000000.0 << "s"
           << endl;
      cout << ic3 << "Average size of a clause before mic = "
           << clauseSizeBef / (double) numMicCalls << endl;
      cout << ic3 << "Average size of a clause after mic = "
           << clauseSizeAft / (double) numMicCalls << endl;
      cout << ic3 << "Average number of up calls for each mic call = "
           << numUpCalls / (double) numMicCalls << endl;
      cout << ic3 << "Average number of down calls for each mic call = "
           << numDownCalls / (double) numMicCalls << endl;
      for(unsigned i = 1; i < levInd.size(); ++i) {
        cout << ic3 << "Average level at which the negation of a "
             "property CTI is found to be inductive for level " << i << " = "
             << levInd[i] / (double) numGenCalls[i] << endl;
      }

      cout << ic3 << "Average size of CTI cubes before lifting = "
           << cubeSizeBef / (double) numLiftCubes << endl;
      cout << ic3 << "Average size of CTI cubes after TACAS lifting = "
           << cubeSizeTACAS / (double) numLiftCubes << endl;
      cout << ic3 << "Average size of CTI cubes after IBM lifting = "
           << cubeSizeIBM / (double) numLiftCubes << endl;
      cout << ic3 << "Average size of CTI cubes after brute-force lifting = "
           << cubeSizeBrute / (double) numLiftCubes << endl;
      cout << ic3 << "Total time spent in IBM lifting = "
           << ibmLiftTime / 1000000.0 << "s" << endl;
      cout << ic3 << "Total time spent in brute-force lifting = "
           << bruteLiftTime / 1000000.0 << "s" << endl;
      cout << ic3 << "Total number of brute-force lifting iterations = "
           << numBruteIter << endl;
    }

    int level;                          //Final level reached
    vector<uint64_t> numPropQueries;    //Number of property inductiveness queries for each level
    vector<uint64_t> numClauses;        //Number of clauses derived at each level
    uint64_t cubeSizeBef;               //Sum of CTI cube sizes before lifting
    uint64_t cubeSizeTACAS;             //Sum of CTI cube sizes after TACAS lifting
    uint64_t cubeSizeIBM;               //Sum of CTI cube sizes after IBM lifting
    uint64_t cubeSizeBrute;             //Sum of CTI cube sizes after brute-force lifting
    uint64_t numLiftCubes;              //Number of cubes on which lifting was applied
    uint64_t ibmLiftTime;               //Total time spent in IBM lifting
    uint64_t bruteLiftTime;             //Total time spent in brute-force lifting
    uint64_t numBruteIter;              //Total number of brute-force iterations
    vector<uint64_t> numGenCalls;       //Number of calls to generalize() on a property CTI
    vector<uint64_t> levInd;            //Sum of levels at which a clause (the negation of a property CTI) is found to be inductive
    uint64_t numMicCalls;               //Total number of calls to MIC
    uint64_t numUpCalls;                //Total number of calls to UP
    uint64_t numDownCalls;              //Total number of calls to DOWN
    uint64_t clauseSizeBef;             //Sum of clause sizes before MIC'ing
    uint64_t clauseSizeAft;             //Sum of clause sizes after MIC'ing
    uint64_t micTime;                   //Total time spent in MIC
    vector<double> percentProp;         //Average percentage of clauses propagated for each level
    vector< vector<uint64_t> > clauseDistBef; //The distribution of clauses among the different levels before clause propagation
    vector< vector<uint64_t> > clauseDistAft; //The distribution of clauses among the different levels after clause propagation
  };

  typedef vector< set<ID> > Partition;
 
  class CEX {
  public:
    CEX() {};
    CEX(vector<Transition> & _cexTrace): cexTrace(_cexTrace) {};
    CEX(vector<Transition> & _cexTrace, int _level): cexTrace(_cexTrace), level(_level) {};
    CEX(vector<Transition> & _cexTrace, int _level, CubeSet & _indCubes): cexTrace(_cexTrace), level(_level), indCubes(_indCubes) {};
    vector<Transition > cexTrace;
    int level;
    CubeSet indCubes;
  };
  class Safe {
  public:
    Safe() {};
    Safe(CubeSet & _proof): proof(_proof) {};
    Safe(CubeSet & _proof, vector<ID> gprop): proof(_proof), gprop(gprop) {};
    CubeSet proof;
    vector<ID> gprop;
  };
  class Trivial {};

  class SharedState {
  public:
    SharedState(Model & _m, IC3::IC3Options & _opts, vector<CubeSet> * _cubes = NULL,
                vector<LevClauses> * _propClauses = NULL) :
      m(_m), opts(_opts), nThreads(1), reverse(false),
      simpleInit(true), bddInit(true), bddTarget(true), 
      TESteps(0), rat(NULL), up_threshold(25), 
      init(NULL), cons(NULL), icons(NULL), lift(NULL), fae(NULL)
    {
      cons = m.newSATManager();
      if(_cubes)
        cubes = *_cubes;
      if(cubes.empty())
        cubes.push_back(CubeSet());
      if(_propClauses)
        propClauses = *_propClauses;
      eqprop = opts.eqprop;
    }
    ~SharedState() {
      if (init) delete init;
      delete cons;
      if (lift) delete lift;
      if (fae) delete fae;
      if (rat) m.constRelease(rat);
      if (icons) delete icons;
    }

    Model & m;
    IC3::IC3Options & opts;

    int64_t stime;

    int nThreads;

    bool reverse;

    COI coi;

    vector<CubeSet> cubes;
    CubeSet infCubes;
    vector<LevClauses> propClauses;
    Partition partition;
    Partition last_partition;

    bool simpleInit;
    set<ID> initially;

    bool bddInit;
    bool bddTarget;
    int TESteps;
    const RchAttachment * rat;

    unsigned int up_threshold;

    bool eqprop;

    set<ID> rvars;
    set<ID> nrvars;

    SAT::Manager * init;
    SAT::Manager * cons;
    SAT::Manager * icons;

    SAT::Manager * lift;
    SAT::Manager * fae;
    vector<ID> faeLits;

    vector< vector<ID> > base_constraints;

    Stats stats;

  };

  class State {
  public:
    State(SharedState & sst) : 
      ss(sst), m(sst.m), opts(sst.opts), _ev(sst.m.newView()), ev(*_ev), cubes(sst.cubes), infCubes(sst.infCubes), propClauses(sst.propClauses), id(0), 
      init(NULL), cons(NULL), icons(NULL), lift(NULL), fae(NULL),  faeLits(sst.faeLits)
    {
      init = sst.init ? sst.init->newView(ev) : NULL;
      cons = sst.cons->newView(ev);
      if (opts.timeout > 0)
        cons->timeout(opts.timeout);
    }
    ~State() {
      delete _ev;
      if (init) delete init;
      delete cons;
      if (lift) delete lift;
      if (fae) delete fae;
      if (icons) delete icons;
    }

    SharedState & ss;

    Model & m;
    IC3::IC3Options & opts;

    Expr::Manager::View * _ev;
    Expr::Manager::View & ev;

    vector<CubeSet> & cubes;
    CubeSet & infCubes;
    vector<LevClauses> & propClauses;

    unordered_map<ID, pair<int, int> > sccPoset;
    vector< vector<unsigned int> > lexReorder;

    int id;

    unordered_map<ID, unsigned int> litCnt;

    vector<Transition> cex;

    SAT::Manager::View * init;
    SAT::Manager::View * cons;
    SAT::Manager::View * icons;

    SAT::Manager::View * lift;
    SAT::Manager::View * fae;
    vector<ID> & faeLits;
  };

  class ProofPostProcState {
  public:
    ProofPostProcState(Model & _m, IC3Options & _opts) : m(_m), opts(_opts) {
      ev = m.newView();
      constraints = NULL;
    }
    ProofPostProcState(Model & _m, vector<ID> & _gprop, 
        vector<SAT::Clauses> * _constraints, IC3Options & _opts) : m(_m), gprop(_gprop),
        constraints(_constraints), opts(_opts) {
      ev = m.newView();
    }
    ~ProofPostProcState() {
      delete ev;
    }

    Model & m;
    vector<ID> gprop;
    vector<SAT::Clauses> * constraints;
    Expr::Manager::View * ev;
    COI coi;
    vector< vector<ID> > property;
    vector< vector<ID> > transRel;
    //For FAIR mode
    vector<ID> negGPropertyPrimed;
    unordered_set<ID> propCube;
    //For IC3 mode
    vector< vector<ID> > negPropPrimedCNF;
    ID npi;
    IC3Options opts;
  };

  void printVector(State & st, const vector<ID> & c) {
    if (st.m.verbosity() > Options::Informative) {
      for (vector<ID>::const_iterator it = c.begin(); it != c.end(); it++)
        cout << " " << Expr::stringOf(st.ev, *it);
      cout << endl;
    }
  }

  class SubsumptionUniverse {
  public:
    SubsumptionUniverse() {
      nodes.push_back(Node());
    }

    void add(const vector<ID> cube, int k) {
      NodeIndex n = _add(cube.begin(), cube.end(), 0);
      nodes[n].level(k);
    }
    void add(const CubeSet & cubes, int k) {
      for (CubeSet::const_iterator it = cubes.begin(); it != cubes.end(); ++it)
        add(*it, k);
    }

    void reduce(CubeSet & cubes, int k) {
      for (CubeSet::iterator it = cubes.begin(); it != cubes.end();) {
        vector<NodeIndex> tokens;
        tokens.push_back(0);
        int scnt = 0;
        if (_subsumed(it->begin(), it->end(), tokens, scnt, k)) {
          CubeSet::iterator tmp = it;
          ++it;
          cubes.erase(tmp);
        }
        else ++it;
      }
    }

  private:
    typedef unsigned int NodeIndex;
    class Node {
    public:
      Node(int lvl = -1) : lvl(lvl) {}
      int level() const { return lvl; }
      void level(int _lvl) {
        if (_lvl > lvl) lvl = _lvl;
      }
      void add(ID id, NodeIndex n) {
        next.insert(NextMap::value_type(id, n)); 
      }
      NodeIndex get(ID id) const {
        NextMap::const_iterator it = next.find(id);
        if (it == next.end()) return 0;
        return it->second;
      }
    private:
      int lvl;
      typedef unordered_map<ID, NodeIndex> NextMap;
      NextMap next;
    };
    vector<Node> nodes;

    NodeIndex _add(vector<ID>::const_iterator it, vector<ID>::const_iterator end, NodeIndex curr) {
      if (it == end) return curr;
      NodeIndex next = nodes[curr].get(*it);
      if (next == 0) {
        next = nodes.size();
        nodes.push_back(Node());
        nodes[curr].add(*it, next);
      }
      return _add(it+1, end, next);
    }

    bool _subsumed(vector<ID>::const_iterator it, vector<ID>::const_iterator end, 
                   vector<NodeIndex> & tokens, int & scnt, int k) 
    {
      if (it == end) return false;
      vector<NodeIndex>::size_type curr_end = tokens.size();
      for (vector<NodeIndex>::size_type tok = 0; tok < curr_end; ++tok) {
        NodeIndex n = nodes[tokens[tok]].get(*it);
        if (n != 0) {
          if (nodes[n].level() >= k) {
            if (scnt++ > 0 || it+1 != end) return true;
          }
          else if (it+1 != end)
            tokens.push_back(n);
        }
      }
      return _subsumed(it+1, end, tokens, scnt, k);
    }
  };

  ID levelVar(State & st, int k) {
    ostringstream buf;
    buf << "lvl" << k;
    return st.ev.newVar(buf.str());
  }

  ID var(Expr::Manager::View & ev) {
    static int stamp = 0;
    ostringstream buf;
    buf << "var";
    buf << stamp++;
    return ev.newVar(buf.str());
  }

  class SimRefine : public Sim::StateFunctor64 {
  public:
    SimRefine(State & st) : st(st) {
      ExprAttachment const * eat = (ExprAttachment *) st.m.constAttachment(Key::EXPR);
      latches = eat->stateVars();
      for (unsigned int i = 0; i < latches.size(); ++i)
        latchOrder.insert(OMap::value_type(latches[i], i));
      st.m.constRelease(eat);
      // map latch partition to latch-position partition
      const Partition & _parts = st.ss.partition;
      for (Partition::const_iterator it = _parts.begin(); it != _parts.end(); ++it) {
        set<int> lpart;
        for (set<ID>::const_iterator pit = it->begin(); pit != it->end(); ++pit)
          if (*pit == st.ev.bfalse())
            lpart.insert(-1);
          else {
            OMap::const_iterator vit = latchOrder.find(*pit);
            lpart.insert(vit->second);
          }
        parts.push_back(lpart);
      }
    }
    virtual bool operator()(vector<uint64_t>::const_iterator stateBegin, vector<uint64_t>::const_iterator stateEnd) {
      LPartition newParts;
      for (LPartition::const_iterator it = parts.begin(); it != parts.end(); ++it) {
        PMap pmap;
        for (set<int>::const_iterator pit = it->begin(); pit != it->end(); ++pit)
          if (*pit == -1)
            insert(pmap, 0, *pit);
          else
            insert(pmap, *(stateBegin + *pit), *pit);
        for (PMap::const_iterator pit = pmap.begin(); pit != pmap.end(); ++pit)
          if (pit->second.size() > 1)
            newParts.push_back(pit->second);
      }
      parts = newParts;
      return (parts.size() > 0);
    }
    void finish() {
      st.ss.partition.clear();
      for (LPartition::const_iterator it = parts.begin(); it != parts.end(); ++it) {
        set<ID> part;
        for (set<int>::const_iterator pit = it->begin(); pit != it->end(); ++pit)
          if (*pit == -1)
            part.insert(st.ev.bfalse());
          else
            part.insert(latches[*pit]);
        st.ss.partition.push_back(part);
      }
    }
  private:
    State & st;
    typedef unordered_map< uint64_t, set<int> > PMap;
    typedef unordered_map<ID, unsigned int> OMap;
    typedef vector< set<int> > LPartition;
    OMap latchOrder;
    vector<ID> latches;
    LPartition parts;

    inline void insert(PMap & pmap, uint64_t state, int id) {
      PMap::iterator it = pmap.find(state);
      if (it == pmap.end()) {
        pair<PMap::iterator, bool> rv = pmap.insert(PMap::value_type(state, set<int>()));
        it = rv.first;
      }
      it->second.insert(id);
    }
  };

  void simRefine(State & st) {
    if (st.m.verbosity() > Options::Informative)
      cout << "simRefine" << endl;
    SimRefine refine(st);
    // make these constants parameters
    unsigned int nRuns = st.ss.opts.nRuns;
    for (unsigned int i = 0; i < nRuns && st.ss.partition.size() > 0; ++i)
      Sim::sequentialSimulateRandom64(st.m, 1000, refine);
    refine.finish();
    if (st.m.verbosity() > Options::Informative) {
      Partition & parts = st.ss.partition;
      cout << "Parts (" << parts.size() << "):";
      for (Partition::iterator it = parts.begin(); it != parts.end(); ++it)
        cout << " " << it->size();
      cout << endl;
    }
  }

  ID var(State & st, ID lit) {
    Expr::Op op = st.ev.op(lit);
    if (op == Expr::Var)
      return lit;
    else {
      assert (op == Expr::Not);
      return var(st, st.ev.apply(Expr::Not, lit));
    }
  }

  void complement(Expr::Manager::View & ev, const vector<ID> & in, vector<ID> & out) {
    for (vector<ID>::const_iterator it = in.begin(); it != in.end(); it++)
      out.push_back(ev.apply(Expr::Not, *it));
  }

  void primeVector(Expr::Manager::View & ev, const vector<ID> & in, vector<ID> & out) {
    for(vector<ID>::const_iterator it = in.begin(); it != in.end(); ++it) {
      out.push_back(ev.prime(*it));
    }
  }

  void resetAssignment(SAT::Assignment & asgn) {
    for(SAT::Assignment::iterator it = asgn.begin(); it != asgn.end(); ++it) {
      it->second = SAT::Unknown;
    }
  }


  typedef unordered_map<ID, unsigned int> VMap;
  void randomVars(SharedState & ss, Expr::Manager::View & ev, 
                  const vector<ID> & latches, const vector<ID> & fns)
  {
    class cnt_folder : public Expr::Manager::View::Folder {
    public:
      cnt_folder(Expr::Manager::View & v, VMap & vmap) : 
        Expr::Manager::View::Folder(v), vmap(vmap) {}
      virtual ID fold(ID id, int n, const ID * const args) {
        if (view().op(id) == Expr::Var) {
          VMap::iterator it = vmap.find(id);
          if (it == vmap.end()) {
            pair<VMap::iterator, bool> rv = vmap.insert(VMap::value_type(id, 0));
            it = rv.first;
          }
          it->second++;
        }
        return id;
      }
    private:
      VMap & vmap;
    };
    VMap all;
    cnt_folder cntr(ev, all);
    for (vector<ID>::const_iterator it = fns.begin(); it != fns.end(); ++it)
      ev.fold(cntr, *it);
    set<ID> nrvars(latches.begin(), latches.end());
    for (unsigned int i = 0; i < latches.size(); ++i) {
      set<ID>::iterator li = nrvars.find(latches[i]);
      if (li == nrvars.end()) continue;
      ID v = ev.btrue();
      Expr::Op op = ev.op(fns[i]);
      if (op == Expr::Var) v = fns[i];
      if (op == Expr::Not) {
        ID nf = ev.apply(Expr::Not, fns[i]);
        if (ev.op(nf) == Expr::Var)
          v = nf;
      }
      //if (v != ev.btrue()) cout << Expr::stringOf(ev, latches[i]) << " = " << Expr::stringOf(ev, fns[i]);
      if (v != ev.btrue() && nrvars.find(v) == nrvars.end()) {
        //cout << "*";
        VMap::const_iterator it = all.find(v);
        assert (it != all.end());
        //cout << "(" << it->second << ")";
        if (it->second == 1) {
          //cout << "*";
          ss.rvars.insert(latches[i]);
          nrvars.erase(li);
        }
      }
      //if (v != ev.btrue()) cout << endl;
    }
    ss.nrvars = nrvars;
    if (ss.m.verbosity() > Options::Informative)
      cout << "IC3: randomVars: " << ss.rvars.size() << endl;
  }

  void fsisInitSAT(State & st) {
    COIAttachment const * cat = (COIAttachment *) st.m.constAttachment(Key::COI);
    st.ss.coi = cat->coi();
    st.m.constRelease(cat);

    // get CNF encoding for transition relation
    CNFAttachment * cnfat = (CNFAttachment *) st.m.constAttachment(Key::CNF);
    vector< vector<ID> > cons_clauses = cnfat->getCNF();

    // include user-provided constraints
    vector< vector<ID> > constraints;
    if (st.ss.opts.constraints)
      for (unsigned i = 0; i < st.ss.opts.constraints->size(); ++i)
        cons_clauses.insert(cons_clauses.end(), 
                            (*st.ss.opts.constraints)[i].begin(), 
                            (*st.ss.opts.constraints)[i].end());

    ExprAttachment const * eat = (ExprAttachment *) st.m.constAttachment(Key::EXPR);
    vector<ID> latches(eat->stateVars());
    vector<ID> fns(eat->nextStateFnOf(latches));

    if (st.opts.sccH) {
#if HEIGHT
      vector< vector< vector<ID> > > sccp = Expr::sortStateVarsBySccHeight(st.ev, eat->outputFns(), latches, fns);
#else
      vector< vector< vector<ID> > > sccp = Expr::sortStateVarsBySccDepth(st.ev, eat->outputFns(), latches, fns);
#endif
      for (unsigned int i = 0; i < sccp.size(); ++i) {
        st.lexReorder.push_back(vector<unsigned int>());
        for (unsigned int j = 0; j < sccp[i].size(); ++j) {
          st.lexReorder.back().push_back(j);
          for (vector<ID>::const_iterator it = sccp[i][j].begin(); it != sccp[i][j].end(); ++it)
            st.sccPoset.insert(unordered_map<ID, pair<int, int>>::value_type(*it, pair<int, int>(i, j)));
        }
      }
    }

    randomVars(st.ss, st.ev, latches, fns);

    // assumes initial condition is a cube
    RchAttachment const * rat = (RchAttachment *) st.m.constAttachment(Key::RCH);
    vector<ID> init = eat->initialConditions();
    if (st.ss.simpleInit) {
      ID iexp = rat->forwardLowerBound();
      if (iexp != st.ev.bfalse()) {
        cout << init.size();
        init.clear();
        Expr::conjuncts(st.ev, iexp, init);
        cout << " -> " << init.size() << endl;
      }
      for (vector<ID>::const_iterator it = init.begin(); it != init.end(); ++it)
        st.ss.initially.insert(*it);
    }

    // look for lower bound from bdd_reach
    bool use_flb = !st.ss.opts.bmcsz && st.ss.bddInit && rat->backwardStepsBdd() > 1;
    ID initf;
    if (use_flb) {
      const BddAttachment * bat = (const BddAttachment *) st.m.constAttachment(Key::BDD);
      initf = bat->exprOf(rat->forwardBddLowerBound(), st.ev);
      st.m.constRelease(bat);
#if 1
      vector<ID> disj;
      Expr::disjuncts(st.ev, st.ev.apply(Expr::Not, initf), disj);
      use_flb = false;
      for (vector<ID>::const_iterator it = disj.begin(); it != disj.end(); ++it)
        if (st.ev.op(*it) != Expr::Var && st.ev.op(st.ev.apply(Expr::Not, *it)) != Expr::Var) {
          use_flb = true;
          break;
        }
#endif
    }
    if (use_flb || (!eat->constraints().empty() && !st.ss.opts.bmcsz)) {
      st.ss.simpleInit = false;
      if (use_flb) {
        st.ss.rat = rat;
        st.ss.bddInit = true;
      }
      else {
        st.m.constRelease(rat);
        st.ss.bddInit = false;
      }

      SAT::Clauses init_clauses;
      if (use_flb) 
        Expr::tseitin(st.ev, initf, init_clauses);
      else {
        for (vector<ID>::const_iterator it = init.begin(); it != init.end(); ++it) {
          vector<ID> cls;
          cls.push_back(*it);
          init_clauses.push_back(cls);
        }
      }
      SAT::Clauses icons_clauses(cons_clauses);
      icons_clauses.insert(icons_clauses.end(), init_clauses.begin(), init_clauses.end());
      for (vector<ID>::const_iterator it = eat->constraints().begin(); it != eat->constraints().end(); ++it)
        Expr::tseitin(st.ev, *it, init_clauses);

      st.ss.icons = st.m.newSATManager();
      st.icons = st.ss.icons->newView(st.ev);
      st.ss.icons->add(icons_clauses);

      st.ss.init = st.m.newSATManager();
      st.init = st.ss.init->newView(st.ev);
      st.ss.init->add(init_clauses);
    }
    else if (!st.ss.opts.bmcsz) {
      st.ss.bddInit = false;
      st.m.constRelease(rat);
      ID nlv0 = st.ev.apply(Expr::Not, levelVar(st, 0));
      for (vector<ID>::const_iterator it = init.begin(); it != init.end(); it++) {
        vector<ID> cls;
        cls.push_back(nlv0);
        cls.push_back(*it);
        cons_clauses.push_back(cls);
      }
    }
    else {
      assert (st.ss.opts.bmcsz);
      st.ss.bddInit = false;
      st.ss.simpleInit = false;

      // copy constrained transition relation
      SAT::Clauses tr0 = cnfat->getPlainCNF();
      tr0.insert(tr0.end(), constraints.begin(), constraints.end());
      // add initial condition (cube)
      for (vector<ID>::const_iterator it = init.begin(); it != init.end(); ++it) {
        vector<ID> cls;
        cls.push_back(*it);
        tr0.push_back(cls);
      }
      // step back one timestep
      for (vector< vector<ID> >::iterator it = tr0.begin(); it != tr0.end(); ++it)
        Expr::primeFormulas(st.ev, *it, -1);
      // initial condition is post-image of init
      st.ss.init = st.m.newSATManager();
      st.init = st.ss.init->newView(st.ev);
      st.ss.init->add(tr0);
      // special case for k=0
      tr0.insert(tr0.end(), cons_clauses.begin(), cons_clauses.end());
      st.ss.icons = st.m.newSATManager();
      st.icons = st.ss.icons->newView(st.ev);
      st.ss.icons->add(tr0);
    }

    vector< vector<ID> > error_clauses;
    ID npi;
    if (st.ss.bddTarget && rat->backwardStepsBdd() > 1) {
      st.ss.TESteps = rat->backwardStepsBdd() - 1;
      const BddAttachment * bat = (const BddAttachment *) st.m.constAttachment(Key::BDD);
      npi = bat->exprOf(rat->backwardBddLowerBound(), st.ev);
      st.m.constRelease(bat);
      Expr::tseitin(st.ev, st.ev.apply(Expr::Not, npi), cons_clauses);
    }
    else {
      st.ss.bddTarget = false;
      npi = eat->outputFnOf(eat->outputs()[0]);
    }
    if (npi == st.ev.bfalse()) throw Safe();
    if (npi == st.ev.btrue()) throw CEX();
    Expr::tseitin(st.ev, Expr::primeFormula(st.ev, npi), error_clauses);
    ID er = st.ev.apply(Expr::Not, levelVar(st, -1));
    for (vector< vector<ID> >::iterator it = error_clauses.begin(); it != error_clauses.end(); it++)
      it->push_back(er);

    vector< vector<ID> > property_clauses;
    Expr::tseitin(st.ev, st.ev.apply(Expr::Not, npi), property_clauses);

    //Add property
    st.cons->manager().add(property_clauses);

    st.cons->manager().add(cons_clauses);
    st.cons->manager().add(error_clauses);

    st.ss.base_constraints.insert(st.ss.base_constraints.end(), property_clauses.begin(), property_clauses.end());
    st.ss.base_constraints.insert(st.ss.base_constraints.end(), cons_clauses.begin(), cons_clauses.end());
    st.ss.base_constraints.insert(st.ss.base_constraints.end(), error_clauses.begin(), error_clauses.end());

    st.m.constRelease(eat);
    st.m.constRelease(cnfat);
  }


  void initSAT(State & st) {
    COIAttachment const * cat = (COIAttachment *) st.m.constAttachment(Key::COI);
    st.ss.coi = cat->coi();
    st.m.constRelease(cat);

    // get CNF encoding for transition relation
    CNFAttachment * cnfat = (CNFAttachment *) st.m.constAttachment(Key::CNF);
    vector< vector<ID> > cons_clauses = cnfat->getCNF();
 
    // include user-provided constraints
    vector< vector<ID> > constraints;
    if (st.ss.opts.constraints)
      for (unsigned i = 0; i < st.ss.opts.constraints->size(); ++i) {
        cons_clauses.insert(cons_clauses.end(), 
                            (*st.ss.opts.constraints)[i].begin(), 
                            (*st.ss.opts.constraints)[i].end());
        constraints.insert(constraints.end(), (*st.ss.opts.constraints)[i].begin(),
                           (*st.ss.opts.constraints)[i].end());
      }

    ExprAttachment const * eat = (ExprAttachment *) st.m.constAttachment(Key::EXPR);
    vector<ID> latches(eat->stateVars());
    vector<ID> fns(eat->nextStateFnOf(latches));

    if (st.opts.sccH) {
#if HEIGHT
      vector< vector< vector<ID> > > sccp = Expr::sortStateVarsBySccHeight(st.ev, eat->outputFns(), latches, fns);
#else
      vector< vector< vector<ID> > > sccp = Expr::sortStateVarsBySccDepth(st.ev, eat->outputFns(), latches, fns);
#endif
      for (unsigned int i = 0; i < sccp.size(); ++i) {
        st.lexReorder.push_back(vector<unsigned int>());
        for (unsigned int j = 0; j < sccp[i].size(); ++j) {
          st.lexReorder.back().push_back(j);
          for (vector<ID>::const_iterator it = sccp[i][j].begin(); it != sccp[i][j].end(); ++it)
            st.sccPoset.insert(unordered_map<ID, pair<int, int>>::value_type(*it, pair<int, int>(i, j)));
        }
      }
    }

    randomVars(st.ss, st.ev, latches, fns);

    // assumes initial condition is a cube
    RchAttachment const * rat = (RchAttachment *) st.m.constAttachment(Key::RCH);
    vector<ID> init = eat->initialConditions();
    if (st.ss.simpleInit) {
      ID iexp = rat->forwardLowerBound();
      if (iexp != st.ev.bfalse()) {
        cout << init.size();
        init.clear();
        Expr::conjuncts(st.ev, iexp, init);
        cout << " -> " << init.size() << endl;
      }
      for (vector<ID>::const_iterator it = init.begin(); it != init.end(); ++it)
        st.ss.initially.insert(*it);
    }

    // look for lower bound from bdd_reach
    bool use_flb = !st.ss.opts.bmcsz && st.ss.bddInit && rat->backwardStepsBdd() > 1;
    ID initf;
    if (use_flb) {
      const BddAttachment * bat = (const BddAttachment *) st.m.constAttachment(Key::BDD);
      initf = bat->exprOf(rat->forwardBddLowerBound(), st.ev);
      st.m.constRelease(bat);
#if 1
      vector<ID> disj;
      Expr::disjuncts(st.ev, st.ev.apply(Expr::Not, initf), disj);
      use_flb = false;
      for (vector<ID>::const_iterator it = disj.begin(); it != disj.end(); ++it)
        if (st.ev.op(*it) != Expr::Var && st.ev.op(st.ev.apply(Expr::Not, *it)) != Expr::Var) {
          use_flb = true;
          break;
        }
#endif
    }
    if (use_flb || (!eat->constraints().empty() && !st.ss.opts.bmcsz)) {
      st.ss.simpleInit = false;
      if (use_flb) {
        st.ss.rat = rat;
        st.ss.bddInit = true;
      }
      else {
        st.m.constRelease(rat);
        st.ss.bddInit = false;
      }

      SAT::Clauses init_clauses;
      if (use_flb) 
        Expr::tseitin(st.ev, initf, init_clauses);
      else {
        for (vector<ID>::const_iterator it = init.begin(); it != init.end(); ++it) {
          vector<ID> cls;
          cls.push_back(*it);
          init_clauses.push_back(cls);
        }
      }
      SAT::Clauses icons_clauses(cons_clauses);
      icons_clauses.insert(icons_clauses.end(), init_clauses.begin(), init_clauses.end());
      for (vector<ID>::const_iterator it = eat->constraints().begin(); it != eat->constraints().end(); ++it)
        Expr::tseitin(st.ev, *it, init_clauses);

      st.ss.icons = st.m.newSATManager();
      st.icons = st.ss.icons->newView(st.ev);
      st.ss.icons->add(icons_clauses);


      st.ss.init = st.m.newSATManager();
      st.init = st.ss.init->newView(st.ev);
      st.ss.init->add(init_clauses);

      for (unsigned i = 0; i < st.ss.opts.constraints->size(); ++i) {
        st.ss.init->add((*st.ss.opts.constraints)[i]);
      }
    }
    else if (!st.ss.opts.bmcsz) {
      st.ss.bddInit = false;
      st.m.constRelease(rat);
      ID nlv0 = st.ev.apply(Expr::Not, levelVar(st, 0));
      for (vector<ID>::const_iterator it = init.begin(); it != init.end(); it++) {
        vector<ID> cls;
        cls.push_back(nlv0);
        cls.push_back(*it);
        cons_clauses.push_back(cls);
      }
    }
    else {
      assert (st.ss.opts.bmcsz);
      st.ss.bddInit = false;
      st.ss.simpleInit = false;

      // copy constrained transition relation
      SAT::Clauses tr0 = cnfat->getPlainCNF();
      tr0.insert(tr0.end(), constraints.begin(), constraints.end());
      // add initial condition (cube)
      for (vector<ID>::const_iterator it = init.begin(); it != init.end(); ++it) {
        vector<ID> cls;
        cls.push_back(*it);
        tr0.push_back(cls);
      }
      // step back one timestep
      for (vector< vector<ID> >::iterator it = tr0.begin(); it != tr0.end(); ++it)
        Expr::primeFormulas(st.ev, *it, -1);
      // initial condition is post-image of init
      st.ss.init = st.m.newSATManager();
      st.init = st.ss.init->newView(st.ev);
      st.ss.init->add(tr0);
      // special case for k=0
      tr0.insert(tr0.end(), cons_clauses.begin(), cons_clauses.end());
      st.ss.icons = st.m.newSATManager();
      st.icons = st.ss.icons->newView(st.ev);
      st.ss.icons->add(tr0);
    }

    vector< vector<ID> > error_clauses;
    ID npi;
    if (st.ss.bddTarget && rat->backwardStepsBdd() > 1) {
      st.ss.TESteps = rat->backwardStepsBdd() - 1;
      const BddAttachment * bat = (const BddAttachment *) st.m.constAttachment(Key::BDD);
      npi = bat->exprOf(rat->backwardBddLowerBound(), st.ev);
      st.m.constRelease(bat);
      Expr::tseitin(st.ev, st.ev.apply(Expr::Not, npi), cons_clauses);
    }
    else {
      st.ss.bddTarget = false;
      npi = eat->outputFnOf(eat->outputs()[0]);
      vector<ID> cube;
      Expr::conjuncts(st.ev, npi, cube);
      npi = st.ev.apply(Expr::And, cube);
    }
    if (npi == st.ev.bfalse()) throw Safe();
    if (npi == st.ev.btrue()) throw CEX();
    if(!st.ss.opts.iictl) {
      Expr::tseitin(st.ev, Expr::primeFormula(st.ev, npi), error_clauses);
    }
    else {
      for(SAT::Clauses::const_iterator it = st.ss.opts.iictl_clauses->begin();
          it != st.ss.opts.iictl_clauses->end(); ++it) {
        vector<ID> cls;
        for(vector<ID>::const_iterator it2 = it->begin(); it2 != it->end(); ++it2) {
          if(*it2 != st.ev.btrue() && *it2 != st.ev.bfalse()) {
            cls.push_back(st.ev.prime(*it2));
          }
          else {
            cls.push_back(*it2);
          }
        }
        error_clauses.push_back(cls);
      }
    }
    vector< vector<ID> > error_clauses_cpy = error_clauses;

    ID er = st.ev.apply(Expr::Not, levelVar(st, -1));
    for (vector< vector<ID> >::iterator it = error_clauses.begin(); it != error_clauses.end(); it++)
      it->push_back(er);

    st.cons->manager().add(cons_clauses);
    st.cons->manager().add(error_clauses);

    st.ss.base_constraints.insert(st.ss.base_constraints.end(), cons_clauses.begin(), cons_clauses.end());
    st.ss.base_constraints.insert(st.ss.base_constraints.end(), error_clauses.begin(), error_clauses.end());

    if(st.opts.lift) {
      vector< vector<ID> > property_clauses;
      Expr::tseitin(st.ev, Expr::primeFormula(st.ev, st.ev.apply(Expr::Not, npi)), property_clauses);

      st.ss.lift = st.m.newSATManager();
      st.lift = st.ss.lift->newView(st.ev);
      SAT::Clauses trNpi = cnfat->getCNF();
      st.lift->add(trNpi);
      st.lift->add(property_clauses);

      st.ss.fae = st.m.newSATManager();
      st.fae = st.ss.fae->newView(st.ev);
      SAT::Clauses tr = cnfat->getPlainCNF();
      st.fae->add(tr);
      st.fae->add(error_clauses_cpy);
      st.faeLits.push_back(levelVar(st, -1));
    }

    st.m.constRelease(eat);
    st.m.constRelease(cnfat);
  }

  void initReverseSAT(State & st) {
    st.ss.bddInit = false;
    st.ss.eqprop = false;
    st.ss.reverse = true;
    st.ss.simpleInit = false;

    COIAttachment const * cat = (COIAttachment *) st.m.constAttachment(Key::COI);
    st.ss.coi = cat->coi();
    st.m.constRelease(cat);

    ExprAttachment const * eat = (ExprAttachment *) st.m.constAttachment(Key::EXPR);
    vector<ID> latches(eat->stateVars());
    vector<ID> fns(eat->nextStateFnOf(latches));

    if (st.opts.sccH) {
      vector< vector< vector<ID> > > sccp = Expr::sortStateVarsBySccDepth(st.ev, eat->outputFns(), latches, fns);
      for (unsigned int i = 0; i < sccp.size(); ++i) {
        st.lexReorder.push_back(vector<unsigned int>());
        for (unsigned int j = 0; j < sccp[i].size(); ++j) {
          st.lexReorder.back().push_back(j);
          for (vector<ID>::const_iterator it = sccp[i][j].begin(); it != sccp[i][j].end(); ++it)
            st.sccPoset.insert(unordered_map<ID, pair<int, int>>::value_type(*it, pair<int, int>(i, j)));
        }
      }
    }

    randomVars(st.ss, st.ev, latches, fns);

    // get CNF encoding for transition relation
    CNFAttachment * cnfat = (CNFAttachment *) st.m.constAttachment(Key::CNF);
    vector< vector<ID> > cons_clauses = cnfat->getCNF();
    st.m.constRelease(cnfat);

    // switch primed and unprimed vars
    set<ID> tpv(latches.begin(), latches.end());
    set_union(tpv.begin(), tpv.end(), eat->inputs().begin(), eat->inputs().end(), inserter(tpv, tpv.end()));
    for (vector< vector<ID> >::iterator cl = cons_clauses.begin(); cl != cons_clauses.end(); cl++)
      for (vector<ID>::iterator lit = cl->begin(); lit != cl->end(); lit++) {
        ID v = var(st, *lit);
        if (tpv.find(v) != tpv.end())
          *lit = *lit == v ? st.ev.prime(v) : st.ev.apply(Expr::Not, st.ev.prime(v));
        else if (st.ev.nprimes(v))
          *lit = *lit == v ? st.ev.unprime(v) : st.ev.apply(Expr::Not, st.ev.unprime(v));
      }

    // initial condition
    ID initf = eat->outputFnOf(eat->outputs()[0]);
    if (initf == st.ev.btrue()) throw CEX();
    if (initf == st.ev.bfalse()) throw Safe();
    SAT::Clauses initf_cnf;
    Expr::tseitin(st.ev, initf, initf_cnf);

    st.ss.init = st.m.newSATManager();
    st.init = st.ss.init->newView(st.ev);
    st.ss.init->add(initf_cnf);
    vector<ID> constraints = eat->constraints();
    vector< vector<ID> > constraint_clauses;
    Expr::tseitin(st.ev, constraints, constraint_clauses);
    st.ss.init->add(constraint_clauses);
    if (!st.init->sat()) throw Trivial();

    ID nlv0 = st.ev.apply(Expr::Not, levelVar(st, 0));
    for (SAT::Clauses::iterator it = initf_cnf.begin(); it != initf_cnf.end(); it++) {
      it->push_back(nlv0);
      cons_clauses.push_back(*it);
    }

    // error
    vector< vector<ID> > error_clauses;
    ID er = st.ev.apply(Expr::Not, levelVar(st, -1));
    const vector<ID> & init = eat->initialConditions();
    for (vector<ID>::const_iterator it = init.begin(); it != init.end(); it++) {
      vector<ID> cls;
      cls.push_back(er);
      cls.push_back(Expr::primeFormula(st.ev, *it));
      error_clauses.push_back(cls);
    }
    vector<ID> npi;
    complement(st.ev, init, npi);
    cons_clauses.push_back(npi);

    // include user-provided constraints
    if (st.ss.opts.constraints)
      for (unsigned i = 0; i < st.ss.opts.constraints->size(); ++i)
        cons_clauses.insert(cons_clauses.end(), 
                            (*st.ss.opts.constraints)[i].begin(), 
                            (*st.ss.opts.constraints)[i].end());

    st.cons->manager().add(cons_clauses);
    st.cons->manager().add(error_clauses);

    st.ss.base_constraints.insert(st.ss.base_constraints.end(), cons_clauses.begin(), cons_clauses.end());
    st.ss.base_constraints.insert(st.ss.base_constraints.end(), error_clauses.begin(), error_clauses.end());

    st.m.constRelease(eat);
  }

  void extend(State & st, int k) {
    assert (st.cons);
    vector<ID> cls;
    cls.push_back(st.ev.apply(Expr::Not, levelVar(st, k)));
    cls.push_back(levelVar(st, k+1));
    st.cons->manager().add(cls);

    if(k + 1 == static_cast<int>(st.cubes.size()))
      st.cubes.push_back(st.infCubes);
  }

  void prepareCons(State & st, int k, vector<ID> & assumps) {
    bool inf = false;
    if(k == INT_MAX) {
      k = st.cubes.size();
      inf = true;
    }
    else
      assumps.push_back(levelVar(st, k));                            // enable >= k
    assumps.push_back(st.ev.apply(Expr::Not, levelVar(st, k-1)));  // disable < k
    assumps.push_back(st.ev.apply(Expr::Not, levelVar(st, -1)));   // disable error
    if(st.opts.inf_weak) {
      if(inf)
        assumps.push_back(levelVar(st, INT_MAX)); //enable inf
      else //inf cubes are subsumed by cubes at other levels, so disable them
           //so as not to overwhelm the SAT solver
        assumps.push_back(st.ev.apply(Expr::Not, levelVar(st, INT_MAX)));
    }
  }

  void prepareError(State & st, int k, vector<ID> & assumps) {
    assert (k > 0);
    assumps.push_back(levelVar(st, k));                            // enable >= k
    assumps.push_back(st.ev.apply(Expr::Not, levelVar(st, k-1)));  // disable < k
    assumps.push_back(levelVar(st, -1));                           // enable error
    if(st.opts.inf_weak)
      assumps.push_back(st.ev.apply(Expr::Not, levelVar(st, INT_MAX))); //disable inf
  }

  void prepareAssignSpecial(State & st, SAT::Assignment & asgn) {
    //Add inputs to asgn
    ExprAttachment const * eat = (ExprAttachment *) st.m.constAttachment(Key::EXPR);
    const vector<ID> & inputs = eat->inputs();
    for(vector<ID>::const_iterator it = inputs.begin(); it != inputs.end(); ++it) {
      asgn.insert(SAT::Assignment::value_type(*it, SAT::Unknown));
      asgn.insert(SAT::Assignment::value_type(st.ev.unprime(*it), SAT::Unknown));
    }
    st.m.constRelease(eat);
    const set<ID> & latches = st.ss.coi.cCOI();
    for (set<ID>::const_iterator it = latches.begin(); it != latches.end(); ++it) {
      asgn.insert(SAT::Assignment::value_type(*it, SAT::Unknown));
      asgn.insert(SAT::Assignment::value_type(st.ev.unprime(*it), SAT::Unknown));
    }
  }

  void prepareAssign(State & st, SAT::Assignment & asgn, int dlvl = -1,
                     bool inputs = false, bool primedLatches = false,
                     bool primedInputs = false) {
    if(inputs || primedInputs) {
      //Add inputs to asgn
      ExprAttachment const * eat = (ExprAttachment *) st.m.constAttachment(Key::EXPR);
      for(vector<ID>::const_iterator it = eat->inputs().begin(); it != eat->inputs().end(); ++it) {
        if(inputs)
          asgn.insert(SAT::Assignment::value_type(*it, SAT::Unknown));
        if(primedInputs)
          asgn.insert(SAT::Assignment::value_type(st.ev.prime(*it), SAT::Unknown));
      }
      st.m.constRelease(eat);
    }
    const set<ID> & latches = 
      st.ss.reverse 
      ? st.ss.nrvars
      : dlvl >= 0 && !st.ss.opts.cycle
      ? st.ss.coi.kCOI(dlvl + st.ss.TESteps) 
      : st.ss.coi.cCOI();
    for (set<ID>::const_iterator it = latches.begin(); it != latches.end(); ++it) {
      asgn.insert(SAT::Assignment::value_type(*it, SAT::Unknown));
      if(primedLatches) {
        asgn.insert(SAT::Assignment::value_type(st.ev.prime(*it), SAT::Unknown));
      }
    }
  }

  void preparePrimedAssign(State & st, SAT::Assignment & asgn, int dlvl = -1) {
    const set<ID> & latches = 
      dlvl >= 0 && !st.ss.opts.cycle 
      ? st.ss.coi.kCOI(dlvl + st.ss.TESteps) 
      : st.ss.coi.cCOI();
    for (set<ID>::const_iterator it = latches.begin(); it != latches.end(); ++it)
      asgn.insert(SAT::Assignment::value_type(st.ev.prime(*it), SAT::Unknown));
  }

  void randomizeVector(vector<ID> & c) {
    for (unsigned int i = 0; i < 7 * c.size(); ++i) {
      int j = rand() % c.size();
      int k = rand() % c.size();
      ID t = c[j];
      c[j] = c[k];
      c[k] = t;
    }
  }

  void fullAssignOf(State & st, SAT::Assignment & asgn, vector<ID> & cube, vector<ID> & inputCube) {
    ExprAttachment const * eat = (ExprAttachment *) st.m.constAttachment(Key::EXPR);
    for (SAT::Assignment::const_iterator it = asgn.begin(); it != asgn.end(); ++it) {
      if (it->second != SAT::Unknown) {
        if(eat->isInput(it->first)) {
          inputCube.push_back(it->second == SAT::False ?
                              st.ev.apply(Expr::Not, it->first) :
                              it->first);
        }
        else {
          cube.push_back(it->second == SAT::False ? 
                         st.ev.apply(Expr::Not, it->first) : 
                         it->first);
        }
      }
    }
    st.m.constRelease(eat);
  }

  void fullAssignWithPrimedInputsOf(State & st, SAT::Assignment & asgn, vector<ID> & state, vector<ID> & inputs, vector<ID> & nsInputs) {
    ExprAttachment const * eat = (ExprAttachment *) st.m.constAttachment(Key::EXPR);
    for (SAT::Assignment::const_iterator it = asgn.begin(); it != asgn.end(); ++it) {
      assert(st.ev.nprimes(it->first) <= 1);
      if (it->second != SAT::Unknown) {
        if (st.ev.nprimes(it->first) == 0) {
          if(eat->isInput(it->first)) {
            inputs.push_back(it->second == SAT::False ?
                             st.ev.apply(Expr::Not, it->first) :
                             it->first);
          }
          else {
            state.push_back(it->second == SAT::False ? 
                            st.ev.apply(Expr::Not, it->first) : 
                            it->first);
          }
        }
        else {
          ID id = st.ev.unprime(it->first);
          assert(eat->isInput(id));
          nsInputs.push_back(it->second == SAT::False ? 
                             st.ev.apply(Expr::Not, id) : 
                             id);
        }
      }
    }
    st.m.constRelease(eat);
  }

  void fullAssignWithPrimedOf(State & st, SAT::Assignment & asgn, vector<ID> & cube, vector<ID> & inputCube, vector<ID> & nsCube) {
    ExprAttachment const * eat = (ExprAttachment *) st.m.constAttachment(Key::EXPR);
    for (SAT::Assignment::const_iterator it = asgn.begin(); it != asgn.end(); ++it) {
      assert(st.ev.nprimes(it->first) <= 1);
      if (it->second != SAT::Unknown) {
        if (st.ev.nprimes(it->first) == 0) {
          if(eat->isInput(it->first)) {
            inputCube.push_back(it->second == SAT::False ?
                                st.ev.apply(Expr::Not, it->first) :
                                it->first);
          }
          else {
            cube.push_back(it->second == SAT::False ? 
                           st.ev.apply(Expr::Not, it->first) : 
                           it->first);
          }
        }
        else {
          nsCube.push_back(it->second == SAT::False ? 
                         st.ev.apply(Expr::Not, st.ev.unprime(it->first)) : 
                         st.ev.unprime(it->first));
        }
      }
    }
    st.m.constRelease(eat);
  }

  void specAssignOf(State & st, SAT::Assignment & asgn, vector<ID> & cube1, vector<ID> & inputCube1, vector<ID> & cube2, vector<ID> & inputCube2) {
    ExprAttachment const * eat = (ExprAttachment *) st.m.constAttachment(Key::EXPR);
    for (SAT::Assignment::const_iterator it = asgn.begin(); it != asgn.end(); ++it) {
      assert(st.ev.nprimes(it->first) <= 1);
      if (it->second != SAT::Unknown) {
        if (st.ev.nprimes(it->first) == 0) {
          if(eat->isInput(it->first)) {
            inputCube2.push_back(it->second == SAT::False ?
                                 st.ev.apply(Expr::Not, it->first) :
                                 it->first);
          }
          else {
            cube2.push_back(it->second == SAT::False ? 
                            st.ev.apply(Expr::Not, it->first) : 
                            it->first);
          }
        }
        else {
          assert(st.ev.nprimes(it->first) == -1);
          ID id = st.ev.primeTo(it->first, 0);
          if(eat->isInput(id)) {
            inputCube1.push_back(it->second == SAT::False ?
                                 st.ev.apply(Expr::Not, id) :
                                 id);
          }
          else {
            cube1.push_back(it->second == SAT::False ? 
                            st.ev.apply(Expr::Not, id) : 
                            id);
          }
        }
      }
    }
    st.m.constRelease(eat);
  }


  void assignOf(State & st, SAT::Assignment & asgn, vector<ID> & cube) {
    for (SAT::Assignment::const_iterator it = asgn.begin(); it != asgn.end(); ++it)
      if (it->second != SAT::Unknown)
        cube.push_back(it->second == SAT::False ? 
                       st.ev.apply(Expr::Not, it->first) : 
                       it->first);
#if 0
      else
        cout << "Unknown: " << Expr::stringOf(st.ev, it->first) << endl;
#endif
  }

  void assignOf(Expr::Manager::View & ev, SAT::Assignment & asgn, vector<ID> & cube) {
    for (SAT::Assignment::const_iterator it = asgn.begin(); it != asgn.end(); ++it) {
      //cout << it->second;
      if (it->second != SAT::Unknown)
        cube.push_back(it->second == SAT::False ? 
                       ev.apply(Expr::Not, it->first) : 
                       it->first);
     }
     //cout << endl;
  }


  void addTransitionToCexTrace(State & st, const vector<ID> & state, const vector<ID> & inputs) {
    st.cex.push_back(Transition(state, inputs));
  }

  void popBackTransition(State & st) {
    st.cex.pop_back();
  }

  bool initialLatch(State & st, ID lit) {
    return (st.ss.initially.find(st.ev.apply(Expr::Not, lit)) != st.ss.initially.end());
  }

  void addCubeToManager(State & st, int k, const vector<ID> & cube, bool quiet = false) {
    // 1. convert to clause
    vector<ID> cls;
    complement(st.ev, cube, cls);

    if (!quiet && st.m.verbosity() > Options::Verbose) {
      if(k == INT_MAX)
        cout << "At " << "inf" << ":";
      else
        cout << "At " << k << ":";
      printVector(st, cls);
    }

    if(st.opts.inf_weak && k == INT_MAX && !quiet /*bad hack!*/) {
      //Add it to the lifting database
      if(st.lift)
        st.lift->manager().add(cls);
    }

    if(k != INT_MAX || !st.opts.inf) {
      // 2. make it a level k clause
      cls.push_back(st.ev.apply(Expr::Not, levelVar(st, k)));
    }

    // 3. add to manager
    st.cons->manager().add(cls);
  }

  bool addCubeToCubes(State & st, int k, vector<ID> & cube) {
    // add to cube set for propagation
    sort(cube.begin(), cube.end());
    CubeSet & tmp = k == INT_MAX ? st.infCubes : st.cubes[k];
    pair<CubeSet::iterator, bool> rv = tmp.insert(cube);
    return rv.second;
  }

  void addCube(State & st, int k, vector<ID> & cube) {
    if (addCubeToCubes(st, k, cube))
      addCubeToManager(st, k, cube);
  }

  void renewSAT(State & st) {
    // ZChaff gets overwhelmed by the many clauses that are repeated
    // at various levels.  Our SAT solver should recognize and
    // eliminate level-based repetition.

    if (st.m.verbosity() > Options::Informative)
      cout << "renewSAT" << endl;

    SharedState & sst = st.ss;
    delete st.cons;
    delete sst.cons;
    sst.cons = st.m.newSATManager();

    sst.cons->add(sst.base_constraints);
    st.cons = sst.cons->newView(st.ev);
    if (sst.opts.timeout > 0)
      st.cons->timeout(sst.opts.timeout);

    for(CubeSet::const_iterator it = st.infCubes.begin();
        it != st.infCubes.end(); ++it) {
      addCubeToManager(st, INT_MAX, *it, true);
    }

    for (unsigned int k = 0; k < st.cubes.size(); ++k) {
      vector<ID> cls;
      cls.push_back(st.ev.apply(Expr::Not, levelVar(st, k)));
      cls.push_back(levelVar(st, k+1));
      sst.cons->add(cls);

      const CubeSet & cubes = st.cubes[k];
      for(CubeSet::const_iterator it = cubes.begin(); it != cubes.end(); ++it)
        addCubeToManager(st, k, *it, true);
    }
    if(!st.propClauses.empty()) {
      for(vector<LevClauses>::const_iterator it = st.propClauses.begin(); it != st.propClauses.end(); ++it) {
        int level = it->level;
        const vector< vector<ID> > & clauses = it->clauses;
        for(vector< vector<ID> >::const_iterator it2 = clauses.begin(); it2 != clauses.end(); ++it2) {
          vector<ID> cls = *it2;
          //Make it a level "level" clause
          cls.push_back(st.ev.apply(Expr::Not, levelVar(st, level)));
          sst.cons->add(cls);
        }
      }
    }
  }

  void reverseVector(vector<ID> & vec) {
    for (unsigned int i = 0; i < vec.size()/2; ++i) {
      ID tmp = vec[i];
      vec[i] = vec[vec.size()-1-i];
      vec[vec.size()-1-i] = tmp;
    }
  }

  void prime_implicate_init(State & st, const vector<ID> & keep, vector<ID> & rest) 
  {
    assert (st.init);
    vector<ID> assumps(keep);
    vector<ID> lkeep;
    // reverse to give priority to rightmost rest elements
    reverseVector(rest);
    // dummy to pop immediately
    rest.push_back(st.ev.btrue());
    while (rest.size() > 0) {
      ID lit = rest.back();
      rest.pop_back();
      vector<ID> cassumps(assumps);
      cassumps.insert(cassumps.end(), rest.begin(), rest.end());
      bool rv = st.init->sat(&cassumps, NULL, &cassumps);
      if (rv) {
        assert (lit != st.ev.btrue());
        lkeep.push_back(lit);
        assumps.push_back(lit);
      }
      else {
        // reduce rest by the unsat core
        sort(cassumps.begin(), cassumps.end());
        vector<ID> nrest;
        for (vector<ID>::iterator it = rest.begin(); it != rest.end(); it++)
          if (binary_search(cassumps.begin(), cassumps.end(), *it))
            nrest.push_back(*it);
        rest = nrest;
      }
    }
    rest = lkeep;
  }

  bool initiation(State & st, vector<ID> & cube, SAT::Assignment * asgn = NULL, bool rcore = false) {
    assert (!asgn);
    if (rcore) {
      if (st.ss.bddInit) {
        vector<ID> rcube;
        if (st.ss.rat->disjointFromFwBdd(cube, &rcube)) {
          cube = rcube;
          return true;
        }
        else
          return false;
      }
      else if (st.ss.simpleInit) {
        for (vector<ID>::reverse_iterator it = cube.rbegin(); it != cube.rend(); ++it)
          if (initialLatch(st, *it)) {
            ID lit = *it;
            cube.clear();
            cube.push_back(lit);
            return true;
          }
        return false;
      }
      else {
        if (st.init->sat(&cube)) {
          prime_implicate_init(st, vector<ID>(), cube);
          return true;
        }
        return false;
      }
    }
    else {
      if (st.ss.bddInit)
        return st.ss.rat->disjointFromFwBdd(cube);
      else if (st.ss.simpleInit) {
        for (vector<ID>::iterator it = cube.begin(); it != cube.end(); ++it)
          if (initialLatch(st, *it))
            return true;
        return false;
      }
      else {
        assert (st.init);
        return !st.init->sat(&cube);
      }
    }
  }

  bool consecution(State & st, int k, vector<ID> & cube, 
                   SAT::Assignment * asgn = NULL, bool rcore = true,
                   bool full_init = false, SAT::Assignment * lifted = NULL) 
  {
    if (st.ss.opts.timeout > 0) {
      int64_t sofar = Util::get_user_cpu_time() - st.ss.stime;
      if (sofar / 1000000 >= st.ss.opts.timeout) {
        if (st.m.verbosity() > Options::Terse)
          cout << "IC3" << (st.ss.reverse ? "r" : "") << ": timeout" << endl;
        throw Timeout("IC3 timeout");
      }
    }

    vector<ID> cls, assumps;
    complement(st.ev, cube, cls);

    SAT::GID tgid = SAT::NULL_GID;
    SAT::Manager::View * cons;
    if (k == 0 && st.icons) 
      cons = st.icons;
    else {
      prepareCons(st, k, assumps);
      cons = st.cons;
      tgid = cons->newGID();
      try {
        cons->add(cls, tgid);
      }
      catch (SAT::Trivial tr) {
        assert (!tr.value());
          return true;
      }
    }
    for (vector<ID>::iterator it = cube.begin(); it != cube.end(); it++)
      assumps.push_back(st.ev.prime(*it));
    bool rv = cons->sat(&assumps, asgn, rcore ? &assumps : NULL, tgid, full_init, lifted);
    if (tgid != SAT::NULL_GID) cons->remove(tgid);

    if (rv)
      return false;
    else {
      if (rcore) {
        vector<ID> copy(cube);
        // reduce the cube by the unsat core  
        cube.clear();
        sort(assumps.begin(), assumps.end());
        for (vector<ID>::iterator it = copy.begin(); it != copy.end(); it++)
          if (binary_search(assumps.begin(), assumps.end(), 
                            Expr::primeFormula(st.ev, *it)))
            cube.push_back(*it);
        if (!initiation(st, cube)) {
          if (st.ss.simpleInit) {
            // return a positive lit to the cube
            for (vector<ID>::reverse_iterator it = copy.rbegin(); it != copy.rend(); it++)
              if (initialLatch(st, *it)) {
                cube.push_back(*it);
                break;
              }
          }
          else if (st.ss.bddInit) {
            vector<ID> exp;
            bool rv = st.ss.rat->disjointFromFwBddExpand(copy, cube, &exp);
            assert (rv);
            if (st.m.verbosity() > Options::Verbose)
              cout << "^" << copy.size() << " " << exp.size() << " " << cube.size() << endl;
            cube = exp;
          }
          else {
            vector<ID> scopy(cube), rest;
            sort(scopy.begin(), scopy.end());
            for (vector<ID>::const_iterator it = copy.begin(); it != copy.end(); ++it)
              if (!binary_search(scopy.begin(), scopy.end(), *it))
                rest.push_back(*it);
            prime_implicate_init(st, cube, rest);
            cube.insert(cube.end(), rest.begin(), rest.end());
            if (st.m.verbosity() > Options::Verbose)
              cout << "*" << copy.size() << " " << cube.size() << " " << scopy.size() << endl;
          }
        }
      }
      return true;
    }
  }

  void reduceCube(State & st, vector<ID> & cube) {
    if (!st.ss.rvars.empty()) {
      vector<ID> copy(cube);
      for (unsigned int i = 0; i < cube.size();)
        if (st.ss.rvars.find(var(st, cube[i])) != st.ss.rvars.end()) {
          cube[i] = cube.back();
          cube.pop_back();
        }
        else
          ++i;
      if (!initiation(st, cube)) cube = copy;
      // WTF?
      if (st.icons && !consecution(st, 0, cube, NULL, false)) cube = copy;
    }
  }

  bool down(State & st, int k, const set<ID> & keep, vector<ID> & cube) {
    SAT::Assignment asgn;
    for (vector<ID>::iterator it = cube.begin(); it != cube.end(); it++)
      asgn.insert(SAT::Assignment::value_type(var(st, *it), SAT::Unknown));
    vector<ID> rcube;
    while (true) {
      if (!initiation(st, cube))
        return false;
      if (!consecution(st, k, cube, &asgn)) {
        // reduce cube by asgn
        rcube.clear();
        for (vector<ID>::iterator it = cube.begin(); it != cube.end(); it++) {
          SAT::Assignment::const_iterator ait = asgn.find(var(st, *it));
          Expr::Op op = st.ev.op(*it);
          if ((op == Expr::Not && ait->second == SAT::True) ||
              (op == Expr::Var && ait->second == SAT::False)) {
            if (keep.find(*it) != keep.end())
              // about to drop a literal that should be kept
              return false;
          }
          else
            rcube.push_back(*it);
        }
        cube = rcube;
      }
      else
        return true;
    }
  }

  void prime_implicate(State & st, int k, const vector<ID> & nlits, 
                       const vector<ID> & keep, vector<ID> & rest) 
  {
    vector<ID> cls, assumps;
    complement(st.ev, nlits, cls);
    SAT::Manager::View * cons;

    if (k == 0 && st.icons)
      cons = st.icons;
    else {
      cons = st.cons;
      prepareCons(st, k, assumps);
    }
    SAT::GID tgid = SAT::NULL_GID;
    if (nlits.size()) {
      tgid = cons->newGID();
      cons->add(cls, tgid);
    }
    for (vector<ID>::const_iterator it = keep.begin(); it != keep.end(); it++)
      assumps.push_back(st.ev.prime(*it));

    vector<ID> lkeep;
    // reverse to give priority to rightmost rest elements
    reverseVector(rest);
    // dummy to pop immediately
    rest.push_back(st.ev.btrue());
    while (rest.size() > 0) {
      ID lit = rest.back();
      rest.pop_back();
      vector<ID> cassumps(assumps);
      for (vector<ID>::const_iterator it = rest.begin(); it != rest.end(); it++)
        cassumps.push_back(st.ev.prime(*it));
      bool rv = cons->sat(&cassumps, NULL, &cassumps);
      if (rv) {
        if (lit == st.ev.btrue()) {
          cout << k << " " << rest.size() << ": ";
          printVector(st, nlits);
        }
        assert (lit != st.ev.btrue());
        lkeep.push_back(lit);
        assumps.push_back(st.ev.prime(lit));
      }
      else {
        // reduce rest by the unsat core
        sort(cassumps.begin(), cassumps.end());
        vector<ID> nrest;
        for (vector<ID>::iterator it = rest.begin(); it != rest.end(); it++)
          if (binary_search(cassumps.begin(), cassumps.end(), 
                            Expr::primeFormula(st.ev, *it)))
            nrest.push_back(*it);
        rest = nrest;
      }
    }
    if (tgid != SAT::NULL_GID) cons->remove(tgid);
    rest = lkeep;
  }

  void up(State & st, int k, const set<ID> & keep, vector<ID> & ocube) {
    ++st.ss.stats.numUpCalls;
    vector<ID> sofar(keep.begin(), keep.end());

    // 0. remove keep from ocube
    vector<ID> cube;
    for (vector<ID>::iterator it = ocube.begin(); it != ocube.end(); it++)
      if (keep.find(*it) == keep.end())
        cube.push_back(*it);

    // 1. form initial cube
    if (st.ss.simpleInit) {
      bool is_init = false;
      for (set<ID>::const_iterator it = keep.begin(); it != keep.end(); ++it)
        is_init = is_init || initialLatch(st, *it);
      if (!is_init) {
        for (int i = cube.size()-1; i >= 0; --i)
          if (initialLatch(st, cube[i])) {
            sofar.push_back(cube[i]);
            cube.erase(cube.begin()+i);
            break;
          }
      }
    }
    else if (st.ss.bddInit) {
      vector<ID> picube(sofar), pi;
      picube.insert(picube.end(), cube.begin(), cube.end());
      bool rv = st.ss.rat->disjointFromFwBddExpand(picube, sofar, &pi);
      assert (rv);
      sofar = pi;
    }
    else {
      vector<ID> init(cube);
      prime_implicate_init(st, sofar, init);
      sofar.insert(sofar.end(), init.begin(), init.end());
    }

    // 2. propagate via prime_implicate
    vector<ID> nlits(sofar);
    vector<ID> rem(cube);
    while (nlits.size() > 0) {
      sort(nlits.begin(), nlits.end());
      vector<ID> nrem;
      for (vector<ID>::const_iterator it = rem.begin(); it != rem.end(); it++)
        if (!binary_search(nlits.begin(), nlits.end(), *it))
          nrem.push_back(*it);
      rem = nrem;

      vector<ID> ccube(rem);
      prime_implicate(st, k, nlits, sofar, ccube);
      sofar.insert(sofar.end(), ccube.begin(), ccube.end());
      nlits = ccube;
    }

    // 3. final sofar is inductive subclause of original cube
    ocube = sofar;
  }

  void recordLits(State & st, const vector<ID> & cube) {
    for (vector<ID>::const_iterator it = cube.begin(); it != cube.end(); ++it) {
      unordered_map<ID, unsigned int>::iterator lit = st.litCnt.find(*it);
      if (lit == st.litCnt.end()) {
        pair<unordered_map<ID, unsigned int>::iterator, bool> rv = 
          st.litCnt.insert(unordered_map<ID, unsigned int>::value_type(*it, 0));
        lit = rv.first;
      }
      lit->second++;
    }
  }

  void unrecordLits(State & st, const vector<ID> & cube) {
    for (vector<ID>::const_iterator it = cube.begin(); it != cube.end(); ++it) {
      unordered_map<ID, unsigned int>::iterator lit = st.litCnt.find(*it);
      assert (lit != st.litCnt.end() && lit->second > 0);
      lit->second--;
    }
  }

  void resetLits(State & st) {
    st.litCnt.clear();
  }

  class LitCntOrd {
  public:
    LitCntOrd(State & st) : st(st) {}
    bool operator()(ID id1, ID id2) {
      unordered_map<ID, unsigned int>::const_iterator lit1 = st.litCnt.find(id1);
      unordered_map<ID, unsigned int>::const_iterator lit2 = st.litCnt.find(id2);
      unsigned int c1 = lit1 == st.litCnt.end() ? 0 : lit1->second;
      unsigned int c2 = lit2 == st.litCnt.end() ? 0 : lit2->second;
      return c1 < c2;
    }
  private:
    State & st;
  };

  class SCCOrd1 {
  public:
    SCCOrd1(State & st) : st(st) {}
    bool operator()(ID id1, ID id2) {
      id1 = var(st, id1);
      id2 = var(st, id2);
      unordered_map<ID, pair<int, int> >::const_iterator lit1 = st.sccPoset.find(id1);
      unordered_map<ID, pair<int, int> >::const_iterator lit2 = st.sccPoset.find(id2);
      bool ln1 = lit1 == st.sccPoset.end(), ln2 = lit2 == st.sccPoset.end();
      if (ln1 || ln2) {
        if (ln1 && !ln2) return false;
        else if (!ln1 && ln2) return true;
        else return id1 < id2;
      }
      assert (lit1 != st.sccPoset.end());
      assert (lit2 != st.sccPoset.end());
#if HEIGHT
      return lit1->second.first > lit2->second.first;
#else
      return lit1->second.first < lit2->second.first;
#endif
    }
  private:
    State & st;
  };

  class SCCOrd2 {
  public:
    SCCOrd2(State & st) : st(st) {}
    bool operator()(ID id1, ID id2) {
      id1 = var(st, id1);
      id2 = var(st, id2);
      unordered_map<ID, pair<int, int> >::const_iterator lit1 = st.sccPoset.find(id1);
      unordered_map<ID, pair<int, int> >::const_iterator lit2 = st.sccPoset.find(id2);
      bool ln1 = lit1 == st.sccPoset.end(), ln2 = lit2 == st.sccPoset.end();
      if (ln1 || ln2) {
        if (ln1 && !ln2) return false;
        else if (!ln1 && ln2) return true;
        else return id1 < id2;
      }
      assert (lit1 != st.sccPoset.end());
      assert (lit2 != st.sccPoset.end());
      int l11 = lit1->second.first, l21 = lit2->second.first;
#if HEIGHT
      return l11 > l21 ||
#else
      return l11 < l21 ||
#endif
        (l11 == l21 && st.lexReorder[l11][lit1->second.second] > st.lexReorder[l21][lit2->second.second]);
    }
  private:
    State & st;
  };

  void randomizeLex(vector<unsigned int> & c) {
    if (c.size() > 1)
      for (unsigned int i = 0; i < 7 * c.size(); ++i) {
        int j = rand() % c.size();
        int k = rand() % c.size();
        ID t = c[j];
        c[j] = c[k];
        c[k] = t;
      }
  }

  void orderCube(State & st, vector<ID> & cube) {
    if (st.opts.sccH) {
      for (unsigned int i = 0; i < st.lexReorder.size(); ++i)
        randomizeLex(st.lexReorder[i]);
      SCCOrd2 ord1(st);
      LitCntOrd ord2(st);
      stable_sort(cube.begin(), cube.end(), ord2);
      stable_sort(cube.begin(), cube.end(), ord1);
    }
    else {
      LitCntOrd ord(st);
      stable_sort(cube.begin(), cube.end(), ord);
    }
  }

  void mic(State & st, int k, vector<ID> & cube, bool complete = false) {
    set<ID> keep;
    if (!st.ss.reverse) reduceCube(st, cube);
    randomizeVector(cube);
    orderCube(st, cube);
    for (;;) {
      // 1. apply up if large cube or k == 0
      if (k == 0 || cube.size() > st.ss.up_threshold) {
        // TODO: not efficient for k == 0
        up(st, k, keep, cube);
        if (k == 0) break;
        // up does not preserve order
        orderCube(st, cube);
      }

      // 2. try brute force reduction four times
      unsigned int i = 0;
      int cnt = complete? cube.size() : 3;
      for (; i < cube.size() && cnt >= 0; ++i, --cnt) {
        vector<ID> dcube(cube.size()-1);
        for (unsigned int j = 0, l = 0; j < cube.size(); ++j)
          if (j != i)
            dcube[l++] = cube[j];
        ++st.ss.stats.numDownCalls;
        if (down(st, k, keep, dcube)) {
          cube = dcube;
          break;
        }
        keep.insert(cube[i]);
      }
      if (i == cube.size() || cnt < 0) return;
    }
  }

  typedef vector< pair<bool, vector<ID> > > ConsMem;

  bool mem_consecution(ConsMem & mem, State & st, int k, int lo, vector<ID> & cube, SAT::Assignment * asgn = NULL) {
    pair<bool, vector<ID> > & entry = mem[k-lo];
    if (entry.first) {
      if (entry.second.empty())
        return false;
      else {
        cube = entry.second;
        return true;
      }
    }
    entry.first = true;
    bool rv = consecution(st, k, cube, asgn);
    if (rv) entry.second = cube;
    return rv;
  }

  int generalize(State & st, int lo, int hi, vector<ID> & cube, bool pursue, vector<ID> * unlifted = NULL) {
    if (!pursue) {
      // if it's inductive at lo+1, this cube has probably already been
      // taken care of
      vector<ID> assumps(cube);
      prepareCons(st, lo+1, assumps);
      if (!st.cons->sat(&assumps))
        return INT_MAX;
      // inductive relative only to lo
      hi = lo;
    }

    lo = max(0, lo);
    if (lo == 0 && !initiation(st, cube))
      return 0;

    bool indInf = false;
    if((st.opts.inf || st.opts.inf_weak) && pursue) {
      //Check if inductive relative to truly inductive clauses
      if(consecution(st, INT_MAX, cube)) {
        indInf = true;
        mic(st, INT_MAX, cube);
        addCube(st, INT_MAX, cube);
        if(st.opts.inf)
          return INT_MAX;
      }
    }

    int k = hi;
    ConsMem mem(hi-lo+1);
    if (!mem_consecution(mem, st, k, lo, cube)) {
      int _lo = lo, _hi = hi-1;
      SAT::Assignment asgn;
      if(st.ss.opts.printCex) {
        if(st.icons)
          prepareAssignSpecial(st, asgn);
        else
          prepareAssign(st, asgn, -1, true);
      }
      while (_lo <= _hi) {
        k = (_lo+_hi)/2;
        vector<ID> copy1(cube);
        if (mem_consecution(mem, st, k, lo, copy1, st.ss.opts.printCex ? &asgn : NULL)) {
          vector<ID> copy2(cube);
          if (!mem_consecution(mem, st, k+1, lo, copy2)) {
            cube = copy1;
            break;
          }
          else
            _lo = k+1;
        }
        else
          _hi = k-1;
      }
      if (_lo > _hi) {
        if(st.ss.opts.printCex) {
          if(st.icons) {
            vector<ID> state1, inputs1, state2, inputs2;
            specAssignOf(st, asgn, state1, inputs1, state2, inputs2);
            addTransitionToCexTrace(st, state2, inputs2);
            addTransitionToCexTrace(st, state1, inputs1);
          }
          else {
            vector<ID> state, inputs;
            fullAssignOf(st, asgn, state, inputs);
            addTransitionToCexTrace(st, state, inputs);
          }
        }
        return 0;
      }
    }

    // use down to push forward as far as possible
    set<ID> dummy;
    for (; k < hi; ++k) {
      vector<ID> ccube(cube);
      if (down(st, k+1, dummy, ccube))
        cube = ccube;
      else
        break;
    }

    if(st.opts.try_unlifted && unlifted && k < hi) {
      vector<ID> unliftedCpy = *unlifted;
      int k2 = hi;
      ConsMem mem2(hi-lo+1);
      if (!mem_consecution(mem2, st, k2, lo, *unlifted)) {
        int _lo = lo, _hi = hi-1;
        SAT::Assignment asgn;
        if(st.ss.opts.printCex) {
          if(st.icons)
            prepareAssignSpecial(st, asgn);
          else
            prepareAssign(st, asgn, -1, true);
        }
        while (_lo <= _hi) {
          k2 = (_lo+_hi)/2;
          vector<ID> copy1(*unlifted);
          if (mem_consecution(mem2, st, k2, lo, copy1, st.ss.opts.printCex ? &asgn : NULL)) {
            vector<ID> copy2(*unlifted);
            if (!mem_consecution(mem2, st, k2+1, lo, copy2)) {
              *unlifted = copy1;
              break;
            }
            else
              _lo = k2+1;
          }
          else
            _hi = k2-1;
        }
        if (_lo > _hi) {
          if(st.ss.opts.printCex) {
            if(st.icons) {
              vector<ID> state1, inputs1, state2, inputs2;
              specAssignOf(st, asgn, state1, inputs1, state2, inputs2);
              addTransitionToCexTrace(st, state2, inputs2);
              addTransitionToCexTrace(st, state1, inputs1);
            }
            else {
              vector<ID> state, inputs;
              fullAssignOf(st, asgn, state, inputs);
              addTransitionToCexTrace(st, state, inputs);
            }
          }
          return 0;
        }
      }

      // use down to push forward as far as possible
      set<ID> dummy;
      for (; k2 < hi; ++k2) {
        vector<ID> ccube(*unlifted);
        if (down(st, k2+1, dummy, ccube))
          *unlifted = ccube;
        else
          break;
      }

      if(k2 > k) {
        k = k2;
        cube = *unlifted;
        *unlifted = unliftedCpy;
      }
      else {
        //signal the caller that the unlifted cube wasn't used
        unlifted->clear();
      }
    }

    if (k == hi && st.opts.inf && pursue) {
      //Check if inductive relative to truly inductive clauses
      vector<ID> ccube(cube);
      if(down(st, INT_MAX, dummy, ccube)) {
        cube = ccube;
        mic(st, INT_MAX, cube);
        addCube(st, INT_MAX, cube);
        if(st.opts.inf)
          return INT_MAX;
      }
    }

    //Even if it wasn't inductive relative to truly inductive clauses, the
    //generalized clause might be
    if(st.opts.inf_weak && !indInf && pursue) {
      if(consecution(st, INT_MAX, cube)) {
        mic(st, INT_MAX, cube);
        addCube(st, INT_MAX, cube);
      }
    }

    ++st.ss.stats.numClauses.back();
    ++st.ss.stats.numMicCalls;

    // definitely inductive
    ++st.ss.stats.clauseSizeBef += cube.size();
    int64_t start = Util::get_user_cpu_time();
    mic(st, k, cube);
    st.ss.stats.micTime += (Util::get_user_cpu_time() - start);
    ++st.ss.stats.clauseSizeAft += cube.size();
    addCube(st, k+1, cube);
    return k+1;
  }

  class SzOrd {
  public:
    bool operator()(set<ID> s1, set<ID> s2) {
      return s1.size() < s2.size();
    }
  };

  ID tempVar(State & st, int n) {
    ostringstream buf;
    buf << "_tmp_";
    buf << n;
    return st.ev.newVar(buf.str());
  }


  void partitionCubes(State & st, set<ID> & part, CubeSet & cubes) {
    if (part.find(st.ev.bfalse()) != part.end()) {
      for (set<ID>::iterator it = part.begin(); it != part.end(); ++it)
        if (*it != st.ev.bfalse()) {
          vector<ID> c;
          c.push_back(*it);
          cubes.insert(c);
        }
    }
    else {
      set<ID>::iterator _rep = part.begin();
      assert (_rep != part.end());
      ID rep = *_rep;
      ID nrep = st.ev.apply(Expr::Not, rep);
      set<ID>::iterator _rem = _rep;
      ++_rem;
      for (; _rem != part.end(); ++_rem) {
        ID rem = *_rem;
        ID nrem = st.ev.apply(Expr::Not, rem);
        vector<ID> c1, c2;
        c1.push_back(rep); c1.push_back(nrem);
        c2.push_back(nrep); c2.push_back(rem);
        sort(c1.begin(), c1.end());
        sort(c2.begin(), c2.end());
        cubes.insert(c1);
        cubes.insert(c2);
      }
    }
  }

  void refine(State & st, deque< set<ID> > & parts, const SAT::Assignment & asgn, bool primed = true) {
    deque< set<ID> > newParts;
    for (deque< set<ID> >::iterator it = parts.begin(); it != parts.end(); ++it) {
      set<ID> tpart, fpart;
      for (set<ID>::iterator pit = it->begin(); pit != it->end(); ++pit) {
        if (*pit == st.ev.bfalse())
          fpart.insert(*pit);
        else {
          SAT::Assignment::const_iterator vit = asgn.find(primed ? st.ev.prime(*pit) : *pit);
          assert (vit != asgn.end());
          if (vit->second == SAT::True)
            tpart.insert(*pit);
          else
            fpart.insert(*pit);
        }
      }
      if (tpart.size() > 1)
        newParts.push_back(tpart);
      if (fpart.size() > 1)
        newParts.push_back(fpart);
    }
    parts = newParts;
  }


  void propagateEquivalences(State & st, int k, Partition & parts, 
                             CubeSet & next, SubsumptionUniverse & su) 
  {
    SzOrd szord;
    sort(parts.begin(), parts.end(), szord);
    deque< set<ID> > q(parts.begin(), parts.end());
    parts.clear();

    while (!q.empty()) {
      set<ID> part = q.front();

      st.ev.begin_local();

      SAT::Assignment asgn;
      SAT::Manager::View * cons;
      vector<ID> assumps;
      if (k == -1) {
        prepareAssign(st, asgn);
        assert (st.init);
        cons = st.init;
      }
      else {
        preparePrimedAssign(st, asgn);
        if (k == 0 && st.icons)
          cons = st.icons;
        else {
          prepareCons(st, k, assumps);
          cons = st.cons;
        }
      }
      SAT::GID tgid = cons->newGID();

      vector<ID> ivs;
      CubeSet cubes;
      partitionCubes(st, part, cubes);
      su.reduce(cubes, k+1);
      for (CubeSet::const_iterator cit = cubes.begin(); cit != cubes.end(); ++cit) {
        if (cit->size() == 1)
          ivs.push_back(k >= 0 ? st.ev.prime((*cit)[0]) : (*cit)[0]);
        else {
          assert (cit->size() == 2);
          ID l1 = k >= 0 ? st.ev.prime((*cit)[0]) : (*cit)[0];
          ID nl1 = st.ev.apply(Expr::Not, l1);
          ID l2 = k >= 0 ? st.ev.prime((*cit)[1]) : (*cit)[1];
          ID nl2 = st.ev.apply(Expr::Not, l2);
          ID iv = tempVar(st, ivs.size());
          ID niv = st.ev.apply(Expr::Not, iv);
          vector<ID> c1, c2, c3;
          c1.push_back(niv); c1.push_back(l1);
          c2.push_back(niv); c2.push_back(l2);
          c3.push_back(nl1); c3.push_back(nl2); c3.push_back(iv);
          ivs.push_back(iv);
          cons->add(c1, tgid);
          cons->add(c2, tgid);
          cons->add(c3, tgid);
        }
      }
      if (ivs.size() == 0) {
        parts.push_back(q.front());
        q.pop_front();
      }
      else {
        cons->add(ivs, tgid);
        bool rv = cons->sat(&assumps, &asgn, 0, tgid);
        if (rv) 
          refine(st, q, asgn, k >= 0);
        else {
          parts.push_back(q.front());
          q.pop_front();
        }
      }
      cons->remove(tgid);

      st.ev.end_local();
    }

    if (st.m.verbosity() > Options::Informative && parts.size() > 0) {
      cout << "Parts at " << k << " (" << parts.size() << "):";
      for (Partition::iterator it = parts.begin(); it != parts.end(); ++it)
        cout << " " << it->size();
      cout << endl;
    }

    for (Partition::iterator it = parts.begin(); it != parts.end(); ++it)
      partitionCubes(st, *it, next);
  }


  bool initializeEquivalences(State & st, SubsumptionUniverse & su) {
    st.ss.partition.clear();

    // initialize partition
    set<ID> allpart = st.ss.coi.cCOI();
    allpart.insert(st.ev.bfalse());
    st.ss.partition.push_back(allpart);
    simRefine(st);

    vector< set<ID> > & parts = st.ss.partition;
    unsigned int maxps = st.ss.opts.ecSz;
    for (vector< set<ID> >::iterator it = parts.begin(); it != parts.end();)
      if (it->size() > maxps) {
        vector< set<ID> >::iterator tmp = it;
        tmp++;
        parts.erase(it);
      }
      else ++it;

    // propagate to level 1
    CubeSet next;
    if (st.init) {
      propagateEquivalences(st, -1, st.ss.partition, next, su);
      next.clear();
    }
    propagateEquivalences(st, 0, st.ss.partition, next, su);
    for (CubeSet::const_iterator it = next.begin(); it != next.end(); ++it) {
      st.cubes[1].insert(*it);
      addCubeToManager(st, 1, *it, true);
    }

    return true;
  }

  void unsatCoreLift(State & st, int k, vector<ID> & cube, vector<ID> & inputs,
                     vector<ID> & nsInputs, bool silent = false) {
    vector<ID> assumps;
    assumps.insert(assumps.end(), inputs.begin(), inputs.end());
    assumps.insert(assumps.end(), cube.begin(), cube.end());
    for(vector<ID>::const_iterator it = nsInputs.begin();
        it != nsInputs.end(); ++it) {
      assumps.push_back(st.ev.prime(*it));
    }
    bool sat = st.lift->sat(&assumps, NULL, &assumps);
    assert(!sat);
    cube.clear();
    ExprAttachment const * eat = (ExprAttachment const *) st.m.constAttachment(Key::EXPR);
    for(vector<ID>::const_iterator it = assumps.begin(); it != assumps.end(); ++it) {
      if(eat->isStateVar(*it) || eat->isStateVar(st.ev.apply(Expr::Not, *it))) {
        cube.push_back(*it);
      }
    }
    if(st.m.verbosity() > Options::Verbose && !silent)
      cout << "UNSAT Core Lifting: " << cube.size() << endl;
    st.m.constRelease(eat);
  }

  void minUnsatCoreLift(State & st, int k, vector<ID> & cube, vector<ID> & inputs,
                     vector<ID> & nsInputs, bool silent = false) {
    ExprAttachment const * eat = (ExprAttachment const *) st.m.constAttachment(Key::EXPR);
    vector<ID> assumps;
    sort(cube.begin(), cube.end());
    for(unsigned i = 0; i < cube.size(); ++i) {
      ++st.ss.stats.numBruteIter;
      vector<ID> rcube;
      for(unsigned j = 0; j < cube.size(); ++j) {
        if(j != i)
          rcube.push_back(cube[j]);
      }
      assumps.clear();
      assumps.insert(assumps.end(), inputs.begin(), inputs.end());
      assumps.insert(assumps.end(), rcube.begin(), rcube.end());
      for(vector<ID>::const_iterator it = nsInputs.begin();
          it != nsInputs.end(); ++it) {
        assumps.push_back(st.ev.prime(*it));
      }
      bool sat = st.lift->sat(&assumps, NULL, &assumps);
      if(!sat) {
        cube.clear();
        for(vector<ID>::const_iterator it = assumps.begin();
            it != assumps.end(); ++it) {
          if(eat->isStateVar(*it) ||
             eat->isStateVar(st.ev.apply(Expr::Not, *it))) {
            cube.push_back(*it);
          }
        }
        --i;
      }
    }
    if(st.m.verbosity() > Options::Verbose && !silent)
      cout << "Minimum UNSAT Core Lifting: " << cube.size() << endl;
    st.m.constRelease(eat);
  }

  void liftAdd(State & st, vector<ID> & cube, bool addUnprimed = true) {
    vector<ID> cls, prCls;
    complement(st.ev, cube, cls);
    primeVector(st.ev, cls, prCls);
    if(addUnprimed)
      st.lift->add(cls);
    st.lift->add(prCls);
  }

  void faeAdd(State & st, vector<ID> & cube) {
    //Create a new activation literal
    vector<ID> prCube;
    primeVector(st.ev, cube, prCube);
    ID act = var(st.ev);
    for(vector<ID>::const_iterator it = prCube.begin();
        it != prCube.end(); ++it) {
      vector<ID> cls;
      cls.push_back(*it);
      cls.push_back(st.ev.apply(Expr::Not, act));
      st.fae->add(cls);
    }
    st.faeLits.push_back(act);
  }

  void forAllExists(State & st, int k, vector<ID> & cube, vector<ID> & inputs, vector<ID> & nsInputs) {

    SAT::Assignment asgn;
    prepareAssign(st, asgn, -1);

    SAT::Assignment fullAsgn;
    prepareAssign(st, fullAsgn, -1, true, false, true);

    vector<ID> c_bar = cube;
    for(unsigned i = 0; i < c_bar.size(); ++i) {
      if(st.m.verbosity() > Options::Verbose)
        cout << "Attempting to drop literal from cube" << endl;
      c_bar[i] = st.ev.apply(Expr::Not, c_bar[i]);

      vector<ID> assumps = c_bar;
      bool dropLit = false;
      while(true) {
        resetAssignment(asgn);
        bool sat = st.lift->sat(&assumps, &asgn);
        if(!sat) {
          if(st.m.verbosity() > Options::Verbose)
            cout << "Dropping literal was successful" << endl;
          dropLit = true;
          break;
        }
        else {
          //Find the trouble-maker state
          vector<ID> asgnc;
          assignOf(st, asgn, asgnc);
          SAT::GID gid = st.fae->newGID();
          st.fae->add(st.faeLits, gid);
          resetAssignment(fullAsgn);
          bool sat = st.fae->sat(&asgnc, &fullAsgn);
          st.fae->remove(gid);
          if(!sat) {
            dropLit = false;
            break;
          }
          else {
            vector<ID> cube, inputs, nsInputs;
            fullAssignWithPrimedInputsOf(st, fullAsgn, cube, inputs, nsInputs);
            //lift
            unsatCoreLift(st, k, cube, inputs, nsInputs, true);
            minUnsatCoreLift(st, k, cube, inputs, nsInputs, true);
            liftAdd(st, cube);
            faeAdd(st, cube);
          }
        }
      }
      if(!dropLit) {
        c_bar[i] = st.ev.apply(Expr::Not, c_bar[i]);
      }
      else {
        vector<ID> newCube;
        for(unsigned j = 0; j < c_bar.size(); ++j) {
          if(j != i)
            newCube.push_back(c_bar[j]);
        }
        c_bar = newCube;
      }
    }
    cube = c_bar;
    if(st.m.verbosity() > Options::Verbose)
      cout << "Forall-exists Lifting: " << cube.size() << endl;
  }

  void lift(State & st, int k, vector<ID> & cube, vector<ID> & inputs, vector<ID> & nsInputs) {
    liftAdd(st, cube, false);

    int64_t start = Util::get_user_cpu_time();
    unsatCoreLift(st, k, cube, inputs, nsInputs);
    st.ss.stats.ibmLiftTime += (Util::get_user_cpu_time() - start);
    st.ss.stats.cubeSizeIBM += cube.size();
    liftAdd(st, cube, false);

    if(st.opts.lift_aggr > 0) {
      //Do brute-force
      int64_t start = Util::get_user_cpu_time();
      minUnsatCoreLift(st, k, cube, inputs, nsInputs);
      st.ss.stats.bruteLiftTime += (Util::get_user_cpu_time() - start);
      st.ss.stats.cubeSizeBrute += cube.size();

      liftAdd(st, cube);
    }
    if(st.opts.lift_aggr > 1) {
      faeAdd(st, cube);
      //Apply forall-exists generalization
      forAllExists(st, k, cube, inputs, nsInputs);
      liftAdd(st, cube);
      faeAdd(st, cube);
    }
  }

  void propagateClauses(State & st, int k, bool trivial, bool shortCircuit, bool possible = true) {
    if (st.m.verbosity() > Options::Informative) cout << "propagateClauses " << endl;

    st.ss.stats.percentProp.push_back(0.0);

    st.ss.stats.clauseDistBef.push_back(vector<uint64_t>());

    for(int i = 1; i <= k+1; ++i) {
      st.ss.stats.clauseDistBef.back().push_back(st.cubes[i].size());
    }

    SubsumptionUniverse su;
    if (!trivial) {
      for (int i = 1; i <= k+1; ++i)
        su.add(st.cubes[i], i);
      if(st.opts.inf)
        su.add(st.infCubes, k+1); //Add to level k+1?
      su.reduce(st.cubes[1], 1);
    }

    // don't interrupt at a bad time if incremental
    int timeout = st.opts.timeout;
    if (st.opts.incremental) {
      st.opts.timeout = -1;
      st.cons->timeout();
    }

    bool inited = false;
    Partition parts = trivial ? st.ss.last_partition : st.ss.partition;
    for (int i = trivial ? k : 1; i <= k; ++i) {
      CubeSet next;

    restart:
      CubeSet & icubes = st.cubes[i];
      int numProp = 0;
      int total = icubes.size();

      for (CubeSet::iterator it = icubes.begin(); it != icubes.end();) {
        vector<ID> cube = *it;
        if (consecution(st, i, cube)) {
          ++numProp;
          CubeSet::iterator tmp = it;
          it++;
          icubes.erase(tmp);
          sort(cube.begin(), cube.end());
          next.insert(cube);
          if (!trivial) su.add(cube, i+1);
        }
        else
          it++;
      }
      st.ss.stats.percentProp.back() += (numProp / (double) total);
      if (icubes.empty() && possible) {
        if (shortCircuit && !st.ss.opts.incremental) throw Safe();
        if (i == k) {
          CubeSet & ncubes = st.cubes[i+1];
          if (!trivial) {
            su.reduce(ncubes, i+1);
            su.reduce(next, i+1);
          }
          for (CubeSet::const_iterator it = next.begin(); it != next.end(); ++it) {
            st.cubes[i+1].insert(*it);
            addCubeToManager(st, i+1, *it, true);
          }
          ExprAttachment const * eat = (ExprAttachment *) st.m.constAttachment(Key::EXPR);
          ID npi = eat->outputFnOf(eat->outputs()[0]);
          st.m.constRelease(eat);
          vector<ID> cube, cls;
          Expr::conjuncts(st.ev, npi, cube);
          bool iscube = true;
          for (unsigned int j = 0; j < cube.size(); ++j)
            if (st.ev.op(cube[j]) != Expr::Var &&
                st.ev.op(st.ev.apply(Expr::Not, cube[j])) != Expr::Var) {
              iscube = false;
              break;
            }
          if (iscube) {
            mic(st, i+1, cube, true);
            complement(st.ev, cube, cls);
            if (st.opts.incremental)
              st.opts.timeout = timeout;
            throw Safe(st.cubes[i+1], cls);
          }
          else {
            if (st.opts.incremental)
              st.opts.timeout = timeout;
            throw Safe(st.cubes[i+1]);
          }
        }
      }

      if (st.ss.eqprop && k == 1 && !inited) {
        // tried first level without equivalences, but didn't work
        st.ss.eqprop = initializeEquivalences(st, su);
        parts = st.ss.partition;
        if (st.ss.eqprop) {
          inited = true;
          goto restart;
        }
      }
      if (st.ss.eqprop)
        propagateEquivalences(st, i, parts, next, su);

      CubeSet & ncubes = st.cubes[i+1];
      if (!trivial) {
        su.reduce(ncubes, i+1);
        su.reduce(next, i+1);
      }
      for (CubeSet::const_iterator it = next.begin(); it != next.end(); ++it) {
        st.cubes[i+1].insert(*it);
        addCubeToManager(st, i+1, *it, true);
      }

      if (st.opts.incremental) {
        // ok to timeout here
        if (st.ss.opts.timeout > 0) {
          int64_t sofar = Util::get_user_cpu_time() - st.ss.stime;
          if (sofar / 1000000 >= st.ss.opts.timeout) {
            if (st.m.verbosity() > Options::Terse)
              cout << "IC3" << (st.ss.reverse ? "r" : "") 
                   << ": timeout (during propagation)" << endl;
            throw Timeout("IC3 timeout");
          }
        }
      }
    }
    st.ss.stats.percentProp.back() /= (double) k;

    st.ss.stats.clauseDistAft.push_back(vector<uint64_t>());

    for(int i = 1; i <= k+1; ++i) {
      st.ss.stats.clauseDistAft.back().push_back(st.cubes[i].size());
    }



    if(st.opts.inf || st.opts.inf_weak) {
      //Apply subsumption on infCubes
      SubsumptionUniverse su2;
      su2.add(st.infCubes, 1);
      su2.reduce(st.infCubes, 1);
    }

    // enable timeouts again
    if (st.opts.incremental) {
      st.opts.timeout = timeout;
      st.cons->timeout(st.opts.timeout);
    }
    st.ss.last_partition = parts;
  }

  void propagateClausesSpecial(State & st, int k, CubeSet & indCubes) {
    if (st.m.verbosity() > Options::Informative) cout << "propagateClauses " << endl;

    try {
      propagateClauses(st, k, false, false, false);
    }
    catch(Safe safe) {
      assert(false);
    }

    SharedState & sst = st.ss;
    delete st.cons;
    delete sst.cons;
    sst.cons = st.m.newSATManager();

    CNFAttachment * cnfat = (CNFAttachment *) st.m.constAttachment(Key::CNF);
    vector< vector<ID> > tr = cnfat->getPlainCNF();
    st.m.constRelease(cnfat);

    sst.cons->add(tr);
    if(st.ss.opts.constraints) {
      for (unsigned i = 0; i < st.ss.opts.constraints->size(); ++i)
        sst.cons->add((*st.ss.opts.constraints)[i]);
    }
    st.cons = sst.cons->newView(st.ev);

    CubeSet cubes = st.cubes[k+1];

    for(CubeSet::const_iterator it = cubes.begin(); it != cubes.end(); ++it)
      addCubeToManager(st, 1, *it, true);

    while(true) {
      CubeSet next;

      for (CubeSet::iterator it = cubes.begin(); it != cubes.end();) {
        vector<ID> cube = *it;
        if (consecution(st, 1, cube)) {
          CubeSet::iterator tmp = it;
          it++;
          cubes.erase(tmp);
          sort(cube.begin(), cube.end());
          next.insert(cube);
        }
        else
          it++;
      }
      if(cubes.empty()) { //converged
        SubsumptionUniverse su;
        su.add(next, 1);
        su.reduce(next, 1);
        indCubes = next;
        break;
      }

      SharedState & sst = st.ss;
      delete st.cons;
      delete sst.cons;
      sst.cons = st.m.newSATManager();

      sst.cons->add(tr);
      if(st.ss.opts.constraints) {
        for (unsigned i = 0; i < st.ss.opts.constraints->size(); ++i)
          sst.cons->add((*st.ss.opts.constraints)[i]);
      }
      st.cons = sst.cons->newView(st.ev);

      cubes = next;

      for(CubeSet::const_iterator it = cubes.begin(); it != cubes.end(); ++it)
        addCubeToManager(st, 1, *it, true);
    }
  }


  struct ToPush {
    ToPush(int k, int dlvl, vector<ID> cube) : k(k), dlvl(dlvl), cube(cube) {}
    ToPush(int k, int dlvl, vector<ID> cube, int idx) : k(k), dlvl(dlvl),
        cube(cube), nodeIdx(idx) {}
    int k;
    int dlvl;
    vector<ID> cube;
    int nodeIdx; //Index of node in graph maintaining state-skeleton
  };
  struct Node {
    Node(vector<ID> & _cube, vector<ID> & _inputs, int _successor) :
        cube(_cube), inputs(_inputs), successor(_successor) {}
    vector<ID> cube;
    vector<ID> inputs;
    int successor;
  };
  class ToPushComp {
  public:
    bool operator()(const ToPush & tp1, const ToPush & tp2) {
      if (tp1.k < tp2.k) return true;
      if (tp1.k > tp2.k) return false;
      if (tp1.dlvl < tp2.dlvl) return true;
      if (tp1.dlvl > tp2.dlvl) return false;
      return _IDVectorComp(tp1.cube, tp2.cube);
    }
  };

  typedef set<ToPush, ToPushComp> PushSet;

  void pushGeneralization(State & st, int toK, PushSet & toPush, vector<Node> & skeleton) {
    while (!toPush.empty()) {
      PushSet::iterator tp = toPush.begin();
      vector<ID> cube(tp->cube);
      SAT::Assignment asgn;
      prepareAssign(st, asgn, st.ss.opts.printCex ? -1 : tp->dlvl+1, st.ss.opts.printCex);
      if (consecution(st, tp->k, cube, &asgn, true, true)) {
        int n = generalize(st, tp->k, toK, cube, false);
        if (n <= toK) {
          if(st.ss.opts.printCex) {
            toPush.insert(ToPush(n, tp->dlvl, tp->cube, tp->nodeIdx));
          }
          else
            toPush.insert(ToPush(n, tp->dlvl, tp->cube));
        }
        else {
          unrecordLits(st, tp->cube);
        }
        toPush.erase(tp);
      }
      else {
        vector<ID> pred, inputs;
        if(st.ss.opts.printCex) {
          fullAssignOf(st, asgn, pred, inputs);
        }
        else {
          assignOf(st, asgn, pred);
        }
        vector<ID> cube(pred);
        int n = generalize(st, tp->k-2, toK, cube, true);
        if (n == 0) {
          if (st.m.verbosity() > Options::Silent && !st.ss.opts.silent)
            cout << "Counterexample of length " << tp->dlvl+3 << endl;
          //Retrieve trace
          if(st.ss.opts.printCex) {
            vector<Transition> trace;
            trace.push_back(Transition(pred, inputs));
            int curNodeIdx = tp->nodeIdx;
            int successor = skeleton[curNodeIdx].successor;
            while(successor != -1) {
              assert(static_cast<unsigned>(successor) < skeleton.size());
              trace.push_back(Transition(skeleton[curNodeIdx].cube,
                  skeleton[curNodeIdx].inputs));
              curNodeIdx = successor;
              successor = skeleton[successor].successor;
            }

            //Remove last added transition(s) (initial transition(s))
            Transition init = st.cex.back();
            popBackTransition(st);
            Transition init2;
            if(st.icons) {
              init2 = st.cex.back();
              popBackTransition(st);
            }
            for(vector<Transition>::const_reverse_iterator rit = trace.rbegin();
                rit != trace.rend(); ++rit) {
              addTransitionToCexTrace(st, rit->state, rit->inputs);
            }
            //Add back initial transition(s)
            if(st.icons)
              st.cex.push_back(init2);
            st.cex.push_back(init);
          }
          if(st.ss.opts.propagate) {
            //Propagate clauses until convergence to extract the truly-inductive
            //one
            CubeSet indCubes;
            propagateClausesSpecial(st, toK, indCubes);
            throw CEX(st.cex, toK, indCubes);
          }
          else {
            throw CEX(st.cex, toK);
          }
        }
        if (n <= toK) {
          sort(pred.begin(), pred.end());
          if(st.ss.opts.printCex) {
            //Add state to skeleton
            skeleton.push_back(Node(pred, inputs, tp->nodeIdx));
            toPush.insert(ToPush(n, tp->dlvl + 1, pred, skeleton.size() - 1));
          }
          else
            toPush.insert(ToPush(n, tp->dlvl + 1, pred));
          recordLits(st, pred);
        }
      }
    }
  }

  bool strengthen(State & st, int k) {
    if (st.m.verbosity() > Options::Informative)
      cout << "strengthen" << endl;
    resetLits(st);
    bool first = true;

    //Statistics
    st.ss.stats.level = k;
    st.ss.stats.numPropQueries.push_back(0);
    st.ss.stats.numClauses.push_back(0);
    st.ss.stats.levInd.push_back(0);
    st.ss.stats.numGenCalls.push_back(0);

    while (true) {
      if (st.m.verbosity() > Options::Verbose) cout << "strengthen" << endl;
      vector<ID> assumps;
      prepareError(st, k, assumps);
      SAT::Assignment asgn;
      prepareAssign(st, asgn, st.ss.opts.printCex ? -1 : 1,
                    st.ss.opts.printCex || st.ss.opts.lift, st.ss.opts.printCex,
                    st.ss.opts.lift);
      SAT::Assignment lifted;
      if(st.ss.opts.printCex || st.ss.opts.lift)
        prepareAssign(st, lifted, 1);
      else
        lifted = asgn;
      bool rv = st.cons->sat(&assumps, &asgn, NULL, SAT::NULL_GID, true, &lifted);
      ++st.ss.stats.numPropQueries.back();
      if (rv) {
        vector<ID> asgnc, liftedc, inputs, unliftedc;
        if(st.ss.opts.printCex) {
          //Separate asgn into current state, input, and next state
          vector<ID> curState, nextState;
          fullAssignWithPrimedOf(st, asgn, curState, inputs, nextState);
          vector<ID> empty;
          addTransitionToCexTrace(st, nextState, empty);
          addTransitionToCexTrace(st, curState, inputs);
          asgnc = curState;
        }
        else if(st.ss.opts.lift) {
          ++st.ss.stats.numLiftCubes;
          vector<ID> nsInputs;
          fullAssignWithPrimedInputsOf(st, asgn, asgnc, inputs, nsInputs);
          st.ss.stats.cubeSizeBef += asgnc.size();
          if(st.m.verbosity() > Options::Verbose)
            cout << "Before lifting: " << asgnc.size() << endl;
          assignOf(st, lifted, liftedc);
          st.ss.stats.cubeSizeTACAS += liftedc.size();
          if(st.m.verbosity() > Options::Verbose) {
            cout << "TACAS Lifting: " << liftedc.size() << endl;
          }
          //Lift asgnc
          unliftedc = asgnc;
          lift(st, k, asgnc, inputs, nsInputs);
        }
        else {
          assignOf(st, asgn, asgnc);
        }
        first = false;
        vector<ID> cube(asgnc);
        ++st.ss.stats.numGenCalls.back();
        int n = generalize(st, k-2, k, cube, true, st.ss.opts.lift ? &unliftedc : NULL);
        st.ss.stats.levInd.back() += (n - 1);
        if(st.ss.opts.lift) {
          //Find out which cube was used (lifted or unlifted)
          if(!unliftedc.empty())
            asgnc = unliftedc;
        }
        if (n == 0) {
          if (st.m.verbosity() > Options::Silent && !st.ss.opts.silent)
            cout << "Counterexample of length 3 (!)" << endl;
          if(st.ss.opts.propagate) {
            CubeSet indCubes;
            propagateClausesSpecial(st, k, indCubes);
            throw CEX(st.cex, k, indCubes);
          }
          else
            throw CEX(st.cex, k);
        }
        if (n <= k) {
          PushSet toPush;
          vector<Node> skeleton;
          sort(asgnc.begin(), asgnc.end());
          if(st.ss.opts.printCex) {
            skeleton.push_back(Node(asgnc, inputs, -1));
            toPush.insert(ToPush(n, 1, asgnc, 0));
          }
          else
            toPush.insert(ToPush(n, 1, asgnc));
          recordLits(st, asgnc);
          pushGeneralization(st, k, toPush, skeleton);
        }
        if(st.ss.opts.printCex) {
          popBackTransition(st);
          popBackTransition(st);
        }
      }
      else {
        if (st.m.verbosity() > Options::Informative)
          cout << "IC3: SAT Count: " << st.cons->manager().satCount() << " " 
               << ((float) st.cons->manager().satTime() / 
                   (float) Util::get_user_cpu_time())  
               << endl;
        return first;
      }
    }
  }

  void check(SharedState & sst, bool shortCircuit = true) {
    State st(sst);
    if (sst.opts.reverse)
      initReverseSAT(st);
    else
      initSAT(st);
    if(sst.opts.incremental) {
      renewSAT(st);
    }
    sst.stime = Util::get_user_cpu_time();
    extend(st, 0);
    for (int k = 1;; ++k) {
      if (st.m.verbosity() > Options::Informative) cout << "Level " << k << endl;
      extend(st, k);
      bool trivial = strengthen(st, k);
      propagateClauses(st, k, trivial, shortCircuit);
      renewSAT(st);
    }
  }

  void initProofPostProcState(ProofPostProcState & st) {

    //Get CNF for transition relation
    CNFAttachment * cnfat = (CNFAttachment *) st.m.constAttachment(Key::CNF);
    if(st.gprop.empty()) {
      if(!st.opts.iictl) {
        st.transRel = cnfat->getCNF();
        ExprAttachment const * eat = (ExprAttachment *) st.m.constAttachment(Key::EXPR);
        st.npi = Expr::primeFormula(*st.ev, eat->outputFns()[0]);
        Expr::tseitin(*st.ev, st.npi, st.negPropPrimedCNF);
      }
      else {
        st.transRel = cnfat->getPlainCNF();
        for(SAT::Clauses::const_iterator it = st.opts.iictl_clauses->begin();
            it != st.opts.iictl_clauses->end(); ++it) {
          SAT::Clause cls;
          for(vector<ID>::const_iterator it2 = it->begin(); it2 != it->end(); ++it2) {
            if(*it2 != st.ev->btrue() && *it2 != st.ev->bfalse()) {
              cls.push_back(st.ev->prime(*it2));
            }
            else {
              cls.push_back(*it2);
            }
          }
          st.negPropPrimedCNF.push_back(cls);
        }
      }
    }
    else {
      //Property is generalized and is a clause 
      st.transRel = cnfat->getPlainCNF();
      vector<ID> cube;
      complement(*st.ev, st.gprop, cube);
      ID npi = st.ev->btrue();
      for(vector<ID>::const_iterator it = cube.begin(); it != cube.end(); ++it) {
        npi = st.ev->apply(Expr::And, npi, st.ev->prime(*it));
        st.negGPropertyPrimed.push_back(st.ev->prime(*it));
      }
      st.npi = npi;
      st.propCube.insert(st.negGPropertyPrimed.begin(), st.negGPropertyPrimed.end());
    }
 
    //Get COI latches
    COIAttachment const * coiat = (COIAttachment *) st.m.constAttachment(Key::COI);
    st.coi = coiat->coi();
    st.m.constRelease(coiat);

    st.m.constRelease(cnfat);
  }

  bool assignSatisfiesCube(Expr::Manager::View & ev, vector<ID> & asgn, unordered_set<ID> & cube) {
    for(vector<ID>::const_iterator it = asgn.begin(); it != asgn.end(); ++it) {
      if(cube.find(ev.apply(Expr::Not, *it)) != cube.end()) {
        return false;
      }
    }
    return true;
  }

  bool assignSatisfiesNegPropPrimed(ProofPostProcState & st, vector<ID> & asgn) {
    if(st.gprop.empty()) {
      SAT::Manager * satMgr = st.m.newSATManager();
      satMgr->add(st.negPropPrimedCNF);
      SAT::Manager::View* satView = satMgr->newView(*st.ev);
      bool sat = satView->sat(&asgn);
      delete satView;
      delete satMgr;
      return sat;
    }
    else {
      return assignSatisfiesCube(*st.ev, asgn, st.propCube);
    }
  }

  ID clauseVar(Expr::Manager::View & ev, int k) {
    ostringstream buf;
    buf << "cla" << k;
    return ev.newVar(buf.str());
  }

  void printProofSize(vector< vector<ID> > & proof) {
    cout << "Number of clauses = " << proof.size() << ", ";
    unsigned numLits = 0;
    for(vector< vector<ID> >::const_iterator it = proof.begin();
        it != proof.end(); ++it) {
      numLits += it->size();
    }
    cout << "number of literals = " << numLits << endl;
  }

  void addProperty(Model & m, vector< vector<ID> > & proof) {
    Expr::Manager::View * ev = m.newView();
    //Get CNF for property
    ExprAttachment const * eat = (ExprAttachment *) m.constAttachment(Key::EXPR);
    ID npi = eat->outputFnOf(eat->outputs()[0]);
    m.constRelease(eat);

    vector<ID> cube, cls;
    Expr::conjuncts(*ev, npi, cube);
    complement(*ev, cube, cls);
    proof.push_back(cls);

    delete ev;
  }

  bool deriveStrongerProof(ProofPostProcState & st, vector< vector<ID> > & proof,
      IC3::IC3Options & opts, bool forceMicProperty = false) {
  
    if(st.m.verbosity() > Options::Informative) {
      cout << "IC3: Deriving a stronger proof: ";
      printProofSize(proof);
      if(!st.gprop.empty()) {
        cout << "Property has " << st.gprop.size() << " literals" << endl;
      }
    }
    int numLitsPre = 0; 
    for(vector< vector<ID> >::const_iterator it = proof.begin();
        it != proof.end(); ++it) {
      numLitsPre += it->size();
    }
    int propLitsPre = st.gprop.size();

    int64_t startTime = Util::get_user_cpu_time();

    bool old_cycle = opts.cycle;
    opts.eqprop = false;
    opts.cycle = true;

    //State of SAT manager after next block of statements: P ^ T ^ !P'
    SharedState sst(st.m, opts);
    State _st(sst);
    initSAT(_st);
    extend(_st, 0);

    vector<ID> cube;
    if(!st.gprop.empty()) {
      complement(_st.ev, st.gprop, cube);
      addCube(_st, 1, cube);
    }
    //State of SAT manager after next block of statements: F ^ P ^ T ^ !P'
    for (SAT::Clauses::const_iterator it = proof.begin(); it != proof.end(); ++it) {
      vector<ID> cube;
      complement(_st.ev, *it, cube);
      addCube(_st, 1, cube);
    }

    bool reduced = true;
    while(reduced) {
      reduced = false;
      SAT::Clauses nproof;
      for (SAT::Clauses::const_iterator it = proof.begin(); it != proof.end(); ++it) {
        vector<ID> cube;
        complement(_st.ev, *it, cube);
        mic(_st, 1, cube, true);
        if (cube.size() < it->size()) {
          reduced = true;
          vector<ID> cls;
          complement(_st.ev, cube, cls);
          nproof.push_back(cls);
          addCube(_st, 1, cube);
        }
        else
          nproof.push_back(*it);
      }
      proof = nproof;

      //Apply subsumption
      if(st.m.verbosity() > Options::Verbose) {
        cout << "Size of proof before subsumption = " << proof.size() << endl;
      }
      CubeSet cubes;
      for(SAT::Clauses::const_iterator it = proof.begin(); it != proof.end(); ++it) {
        vector<ID> cube;
        complement(_st.ev, *it, cube);
        cubes.insert(cube);
      }
      SubsumptionUniverse su;
      su.add(cubes, 1);
      su.reduce(cubes, 1);
      proof.clear();
      for(CubeSet::const_iterator it = cubes.begin(); it != cubes.end(); ++it) {
        vector<ID> cls;
        complement(_st.ev, *it, cls);
        proof.push_back(cls);
      }
      if(st.m.verbosity() > Options::Verbose) {
        cout << "Size of proof after subsumption = " << proof.size() << endl;
      }

      if((reduced || forceMicProperty) && !st.gprop.empty()) {
        //MIC the property
        mic(_st, 1, cube, true);
        if(cube.size() < st.gprop.size()) {
          reduced = true;
          st.gprop.clear();
          complement(_st.ev, cube, st.gprop);
          addCube(_st, 1, cube);
          st.npi = st.ev->btrue();
          st.negGPropertyPrimed.clear();
          for(vector<ID>::const_iterator it = cube.begin(); it != cube.end(); ++it) {
            st.npi = st.ev->apply(Expr::And, st.npi, st.ev->prime(*it));
            st.negGPropertyPrimed.push_back(st.ev->prime(*it));
          }
          st.propCube.clear();
          st.propCube.insert(st.negGPropertyPrimed.begin(), st.negGPropertyPrimed.end());
        }
      }
    }

    opts.cycle = old_cycle;

    int64_t endTime = Util::get_user_cpu_time();
    if(st.m.verbosity() > Options::Informative) {
      cout << "IC3: Stronger proof derived: ";
      printProofSize(proof);
      if(!st.gprop.empty()) {
        cout << "Property has " << st.gprop.size() << " literals" << endl;
      }
      cout << "Time elapsed = " << (endTime - startTime) / 1000000.0 << "s" << endl;
    }

    int numLitsPost = 0; 
    for(vector< vector<ID> >::const_iterator it = proof.begin();
        it != proof.end(); ++it) {
      numLitsPost += it->size();
    }
    int propLitsPost = st.gprop.size();

    return (numLitsPost != numLitsPre || propLitsPost != propLitsPre); 


  }

  bool deriveWeakerProof(ProofPostProcState & st, vector< vector<ID> > & proof) {
  
    if(st.m.verbosity() > Options::Informative) {
      cout << "IC3: Deriving a weaker proof: ";
      printProofSize(proof);
    }
    int numClausesPre = proof.size();

    int64_t startTime = Util::get_user_cpu_time();

    SAT::Manager * satMgr = st.m.newSATManager();
   
    //Add generalized property to SAT database
    if(!st.gprop.empty())
      satMgr->add(st.gprop);

    //Add transition relation to SAT database
    //State of SAT manager after next statement: T
    satMgr->add(st.transRel);

    Expr::Manager::View* & ev = st.ev;

    //State of SAT manager after next block: T ^ P
    if(!st.opts.iictl) {
      if(st.gprop.empty()) {
        //Need to add property
        SAT::Clauses prop;
        Expr::tseitin(*ev, ev->apply(Expr::Not, st.npi), prop);
        satMgr->add(prop);
      }
    }
    else {
      //Add property
      SAT::Clauses prop = *st.opts.iictl_clauses;
      vector<ID> & repClause = prop.back();
      assert(repClause.size() == 1);
      repClause[0] = ev->apply(Expr::Not, repClause[0]);
      satMgr->add(prop);
    }

    // include user-provided constraints
    if (st.constraints)
      for (unsigned i = 0; i < st.constraints->size(); ++i)
        satMgr->add((*st.constraints)[i]);

    if (st.opts.constraints)
      for (unsigned i = 0; i < st.opts.constraints->size(); ++i)
        satMgr->add((*st.opts.constraints)[i]);


    //State of SAT manager after next block of statements : F ^ P ^ T
    ID dnf = ev->bfalse();
    //Create as many variables there are clauses in the proof
    vector<ID> clauseVars;
    vector< unordered_set<ID> > cubes;
    for(unsigned i = 0; i < proof.size(); ++i) {
      //Create a variable that would be used to enable/disable this clause
      ID var = clauseVar(*ev, i);
      clauseVars.push_back(var);
      ID nvar = ev->apply(Expr::Not, var);
      vector<ID> clause = proof[i];
      vector<ID> cube;
      complement(*ev, clause, cube);
      primeFormulas(*ev, cube);
      cubes.push_back(unordered_set<ID>(cube.begin(), cube.end()));
      clause.push_back(nvar);
      satMgr->add(clause);
      cube.push_back(var);
      ID conj = ev->apply(Expr::And, cube);
      dnf = ev->apply(Expr::Or, dnf, conj);
    }

    vector< vector<ID> > negPropOrProofClauses;
    if(!st.opts.iictl) {
      Expr::tseitin(*ev, ev->apply(Expr::Or, dnf, st.npi), negPropOrProofClauses);
    }
    else {
      //Need to form the disjunction of !F' (dnf) and !P' (st.negPropPrimedCNF)
      Expr::tseitin(*ev, dnf, negPropOrProofClauses);
      vector<ID> repClause1 = negPropOrProofClauses.back();
      assert(repClause1.size() == 1);
      negPropOrProofClauses.pop_back();
      vector<ID> repClause2 = st.negPropPrimedCNF.back();
      assert(repClause2.size() == 1);
      negPropOrProofClauses.insert(negPropOrProofClauses.end(), st.negPropPrimedCNF.begin(), st.negPropPrimedCNF.end());
      negPropOrProofClauses.pop_back();
      //Form the OR of the two representatives
      ID r = ev->apply(Expr::Or, repClause1[0], repClause2[0]);
      Expr::tseitin(*ev, r, negPropOrProofClauses);
    }

    //State of SAT manager after next statement: F ^ P ^ T ^ (!F' v !P')
    satMgr->add(negPropOrProofClauses);

    //unordered_set<ID> propCube(st.negGPropertyPrimed.begin(), st.negGPropertyPrimed.end());

    SAT::Manager::View* satView = satMgr->newView(*ev);

    assert(!(satView->sat(&clauseVars)));

    set<ID> latches = st.coi.cCOI();
    //Prepare primed assignment
    SAT::Assignment asgn;
    for(set<ID>::const_iterator it = latches.begin(); it != latches.end(); ++it) {
      asgn.insert(SAT::Assignment::value_type(ev->prime(*it), SAT::Unknown));
    }
 
    set<unsigned> clauseVarsIndices;
    for(unsigned i = 0; i < clauseVars.size(); ++i) {
      clauseVarsIndices.insert(i);
    }

    set<unsigned> keep;

    while(!clauseVarsIndices.empty()) {
      //Disable a clause
      unsigned index = *(clauseVarsIndices.begin());
      clauseVars[index] = ev->apply(Expr::Not, clauseVars[index]);
      clauseVarsIndices.erase(clauseVarsIndices.begin());
      vector<ID> rcube = clauseVars;
      resetAssignment(asgn);
      SAT::Assignment lifted(asgn);
      bool inductive = !(satView->sat(&rcube, &asgn, &rcube, SAT::NULL_GID, false, &lifted));
      if(st.m.verbosity() > Options::Verbose) {
        cout << "Inductive? " << (inductive? "Yes" : "No") << endl;
      }
      if(inductive) {
        //All clauses whose clause variables are not in rcube (the UNSAT core)
        //can be disabled
        unordered_set<unsigned> rcubeSet(rcube.begin(), rcube.end());
        for(unsigned i = 0; i < clauseVars.size(); ++i) {
          if(st.ev->op(clauseVars[i]) == Expr::Var) {
            if(rcubeSet.find(clauseVars[i]) == rcubeSet.end()) {
              clauseVars[i] = ev->apply(Expr::Not, clauseVars[i]);
              clauseVarsIndices.erase(i);
            }
          }
        }
      }
      else {
        //Apply down. Since down can fail, take a snapshot of the current
        //state to be able to revert
        vector<ID> clauseVarsTmp = clauseVars;
        set<unsigned> clauseVarsIndicesTmp = clauseVarsIndices;
        bool failed = false;
        while(!inductive) {
          vector<ID> pred, predl;
          assignOf(*ev, asgn, pred);
          assignOf(*ev, lifted, predl);
          //First find out if the property cube is violated
          //if(assignSatisfiesCube(*ev, predl, propCube)) {
          if(assignSatisfiesNegPropPrimed(st, predl)) {
            if(st.m.verbosity() > Options::Verbose) {
              cout << "Dropping leads to property violation" << endl;
            }
            failed = true;
            break;
          }
          //Find out which of the enabled cubes are satisfied, and disable them
          for(unsigned i = 0; i < cubes.size(); ++i) {
            if(ev->op(clauseVars[i]) == Expr::Var) {
              if(assignSatisfiesCube(*ev, predl, cubes[i])) {
                //Disable this clause if it is not in keep
                if(keep.find(i) != keep.end()) {
                  failed = true;
                  break;
                }
                clauseVars[i] = ev->apply(Expr::Not, clauseVars[i]);
                clauseVarsIndices.erase(i);
              }
            }
          }
          if(clauseVarsIndices.empty() || failed)
            break;
          //Recheck inductiveness
          rcube = clauseVars;
          resetAssignment(asgn);
          lifted = asgn;
          inductive = !(satView->sat(&rcube, &asgn, &rcube, SAT::NULL_GID, false, &lifted));
        }
        if(clauseVarsIndices.empty() || failed) {
          //Down failed, revert
          clauseVars = clauseVarsTmp;
          clauseVarsIndices = clauseVarsIndicesTmp;
          clauseVars[index] = ev->apply(Expr::Not, clauseVars[index]);
          keep.insert(index);
        }
        else {
          //All clauses whose clause variables are not in rcube (the UNSAT core)
          //can be disabled
          unordered_set<unsigned> rcubeSet(rcube.begin(), rcube.end());
          for(unsigned i = 0; i < clauseVars.size(); ++i) {
            if(st.ev->op(clauseVars[i]) == Expr::Var) {
              if(rcubeSet.find(clauseVars[i]) == rcubeSet.end()) {
                clauseVars[i] = ev->apply(Expr::Not, clauseVars[i]);
                clauseVarsIndices.erase(i);
              }
            }
          }
        }
      }
    }

    delete satView;
    delete satMgr;

    vector< vector<ID> > weakerProof;
    for(unsigned i = 0; i < proof.size(); ++i) {
      if(ev->op(clauseVars[i]) == Expr::Var) {
        weakerProof.push_back(proof[i]);
      }
    }

    proof = weakerProof;

    int64_t endTime = Util::get_user_cpu_time();

    if(st.m.verbosity() > Options::Informative) {
      cout << "IC3: Weaker proof derived: ";
      printProofSize(proof);
      cout << "Time elapsed = " << (endTime - startTime) / 1000000.0 << "s" << endl;
    }
    int numClausesPost = proof.size();

    return numClausesPost != numClausesPre;
  }

  void deriveSmallerProof(ProofPostProcState & st, vector< vector<ID> > & proof,
      IC3::IC3Options & opts) {

    if(st.m.verbosity() > Options::Informative) {
      cout << "IC3: Deriving a smaller proof: ";
      printProofSize(proof);
    }

    int64_t startTime = Util::get_user_cpu_time();

    //Apply each of deriveStrongerProof and deriveWeakerProof once
    bool strengthened = deriveStrongerProof(st, proof, opts);
    bool weakened = deriveWeakerProof(st, proof);

    while(weakened && !proof.empty()) {
      strengthened = deriveStrongerProof(st, proof, opts, true);
      weakened = false;
      if(strengthened && !proof.empty()) {
        weakened = deriveWeakerProof(st, proof);
      }
    }

    int64_t endTime = Util::get_user_cpu_time();

    if(st.m.verbosity() > Options::Informative) {
      cout << "IC3: Smaller proof derived: ";
      printProofSize(proof);
      cout << "Time elapsed = " << (endTime - startTime) / 1000000.0 << "s" << endl;
    }

  }

  void fsisSubsumption(State & st) {
    int subsum_freq = st.m.options()["fsis_subsum_freq"].as<int>();
    if(subsum_freq > 0) {
      static int numCalls = 0;
      ++numCalls;
      if(numCalls % subsum_freq == 0) {
        SubsumptionUniverse su;
        if(st.m.verbosity() > Options::Verbose) {
          cout << "Number of cubes before subsumption: " << st.cubes[1].size() << endl;
        }
        su.add(st.cubes[1], 1);
        su.reduce(st.cubes[1], 1);
        if(st.m.verbosity() > Options::Verbose) {
          cout << "Number of cubes after subsumption: " << st.cubes[1].size() << endl;
        }
        renewSAT(st);
        numCalls = 0;
      }
    }
  }

  bool fsisConsecution(State & st, vector<ID> & cube, 
                   SAT::Assignment * asgn = NULL, bool rcore = true,
                   bool full_init = false, SAT::Assignment * lifted = NULL) 
  {
    if (st.ss.opts.timeout > 0) {
      int64_t sofar = Util::get_user_cpu_time() - st.ss.stime;
      if (sofar / 1000000 >= st.ss.opts.timeout) {
        if (st.m.verbosity() > Options::Terse)
          cout << "IC3" << (st.ss.reverse ? "r" : "") << ": timeout" << endl;
        throw Timeout("IC3 timeout");
      }
    }

    vector<ID> assumps;
    prepareCons(st, 1, assumps);

    for (vector<ID>::iterator it = cube.begin(); it != cube.end(); it++)
      assumps.push_back(st.ev.prime(*it));
    bool rv = st.cons->sat(&assumps, asgn, rcore ? &assumps : NULL, SAT::NULL_GID, full_init, lifted);

    if (rv)
      return false;
    else {
      if (rcore) {
        vector<ID> copy(cube);
        // reduce the cube by the unsat core  
        cube.clear();
        sort(assumps.begin(), assumps.end());
        for (vector<ID>::iterator it = copy.begin(); it != copy.end(); it++)
          if (binary_search(assumps.begin(), assumps.end(), 
                            Expr::primeFormula(st.ev, *it)))
            cube.push_back(*it);
        if (!initiation(st, cube)) {
          if (st.ss.simpleInit) {
            // return a positive lit to the cube
            for (vector<ID>::reverse_iterator it = copy.rbegin(); it != copy.rend(); it++)
              if (initialLatch(st, *it)) {
                cube.push_back(*it);
                break;
              }
          }
          else if (st.ss.bddInit) {
            vector<ID> exp;
            bool rv = st.ss.rat->disjointFromFwBddExpand(copy, cube, &exp);
            assert (rv);
            if (st.m.verbosity() > Options::Verbose)
              cout << "^" << copy.size() << " " << exp.size() << " " << cube.size() << endl;
            cube = exp;
          }
          else {
            vector<ID> scopy(cube), rest;
            sort(scopy.begin(), scopy.end());
            for (vector<ID>::const_iterator it = copy.begin(); it != copy.end(); ++it)
              if (!binary_search(scopy.begin(), scopy.end(), *it))
                rest.push_back(*it);
            prime_implicate_init(st, cube, rest);
            cube.insert(cube.end(), rest.begin(), rest.end());
            if (st.m.verbosity() > Options::Verbose)
              cout << "*" << copy.size() << " " << cube.size() << " " << scopy.size() << endl;
          }
        }
      }
      return true;
    }
  }


  struct ToEliminate {
    ToEliminate(int dlvl, vector<ID> cube) : dlvl(dlvl), cube(cube) {}
    ToEliminate(int dlvl, vector<ID> cube, int idx) : dlvl(dlvl),
        cube(cube), nodeIdx(idx) {}
    int dlvl;
    vector<ID> cube;
    int nodeIdx; //Index of node in graph maintaining state-skeleton
  };
  class ToEliminateComp {
  public:
    bool operator()(const ToEliminate & tp1, const ToEliminate & tp2) {
      if (tp1.dlvl > tp2.dlvl) return true;
      if (tp1.dlvl < tp2.dlvl) return false;
      return _IDVectorComp(tp1.cube, tp2.cube);
    }
  };

  typedef set<ToEliminate, ToEliminateComp> EliminateSet;

  bool recurCTI(State & st, EliminateSet & toEliminate, vector<Node> & skeleton) {
    while (!toEliminate.empty()) {
      if(st.m.verbosity() > Options::Verbose) {
        cout << "Size of toEliminate: " << toEliminate.size() << endl;
      }
      EliminateSet::iterator tp = toEliminate.begin();
      vector<ID> cube(tp->cube);
      SAT::Assignment asgn;
      prepareAssign(st, asgn, st.ss.opts.printCex ? -1 : tp->dlvl+1, st.ss.opts.printCex);
      SAT::Assignment lifted(asgn);
#ifdef IBM_LIFTING
      SAT::Assignment coiAsgn = asgn;
      prepareAssign(st, asgn, -1, true); 
#endif
      if (fsisConsecution(st, cube, &asgn, true, true, &lifted)) {
        mic(st, 1, cube);
        addCube(st, 1, cube);
        unrecordLits(st, tp->cube);
        toEliminate.erase(tp);
        fsisSubsumption(st);
      }
      else {
        vector<ID> pred, fullCube, inputs;
        if(st.ss.opts.printCex) {
          fullAssignOf(st, asgn, pred, inputs);
        }
        else {
#ifdef IBM_LIFTING
          fullAssignOf(st, asgn, fullCube, inputs);
          for(SAT::Assignment::iterator it = coiAsgn.begin(); it != coiAsgn.end();
              ++it) {
            it->second = asgn[it->first];
          }
          assignOf(st, coiAsgn, pred);
#else
          assignOf(st, asgn, pred);
#endif
        }
        vector<ID> cube(pred);
        set<ID> dummy;
        if(down(st, 1, dummy, cube)) {
          //Apply mic
          mic(st, 1, cube);
          addCube(st, 1, cube);
          fsisSubsumption(st);
        }
        else {
          if(!st.m.options().count("fsis_disable_lifting")) {
#ifdef IBM_LIFTING
            vector<ID> assumps;
            prepareCons(st, 1, assumps);
            assumps.insert(assumps.end(), inputs.begin(), inputs.end());
            //size_t numInputs = inputs.size();
            assumps.insert(assumps.end(), fullCube.begin(), fullCube.end());
            vector<ID> cubeNeg;
            for(vector<ID>::const_iterator it = tp->cube.begin(); it != tp->cube.end(); ++it) {
              cubeNeg.push_back(st.ev.prime(st.ev.apply(Expr::Not, *it)));
            }
            SAT::GID gid = st.cons->newGID();
            st.cons->add(cubeNeg, gid);
            bool sat = st.cons->sat(&assumps, NULL, &assumps, gid);
            assert(!sat);
            st.cons->remove(gid);
            int origSize = pred.size();
            pred.clear();
            ExprAttachment const * eat = (ExprAttachment *) st.m.constAttachment(Key::EXPR);
#if 0
            //Find the boundary between inputs and state variables
            size_t index = numInputs < assumps.size() ? numInputs - 1 : assumps.size() - 1;
            //Search backwards from startIndex for the first input
            size_t boundary;
            for(boundary = index; boundary >= 0; --boundary) {
              if(eat->isInput(assumps[boundary]) || eat->isInput(st.ev.apply(Expr::Not, assumps[boundary]))) {
                ++boundary;
                break;
              }
            }
            pred.insert(pred.end(), assumps.begin() + boundary, assumps.end());
#else
            for(vector<ID>::const_iterator it = assumps.begin();
                it != assumps.end(); ++it) {
              if(eat->isStateVar(*it) || eat->isStateVar(st.ev.apply(Expr::Not, *it))) {
                if(coiAsgn.find(*it) != coiAsgn.end() || coiAsgn.find(st.ev.apply(Expr::Not, *it)) != coiAsgn.end()) {
                  pred.push_back(*it);
                }
              }
            }
#endif
            vector<ID> pred2;
            assignOf(st, lifted, pred2);
            if(st.m.verbosity() > Options::Verbose) {
              cout << "Original cube size = " << origSize
                   << ", SAT solver lifted = " << pred2.size()
                   << ", IBM lifted = " << pred.size() << endl;
            }
            st.m.constRelease(eat);
#else
            pred.clear();
            assignOf(st, lifted, pred);
#endif
          }
          if(!initiation(st, pred))
            return false;

          addCube(st, 1, pred);

          sort(pred.begin(), pred.end());
          toEliminate.insert(ToEliminate(tp->dlvl + 1, pred));
          recordLits(st, pred);
        }
      }
    }
    return true;
  }


  bool fsisStrengthen(State & st) {
    resetLits(st);
    while (true) {
      if (st.m.verbosity() > Options::Verbose) cout << "strengthen" << endl;
      vector<ID> assumps;
      SAT::Assignment asgn;
      prepareAssign(st, asgn, st.ss.opts.printCex ? 1 : -1, st.ss.opts.printCex, st.ss.opts.printCex);
      SAT::Assignment lifted;
      if(st.ss.opts.printCex)
        prepareAssign(st, lifted, 1);
      else
        lifted = asgn;
#ifdef IBM_LIFTING
      SAT::Assignment coiAsgn = asgn;
      prepareAssign(st, asgn, -1, true, true);
#endif
      prepareError(st, 1, assumps);
      bool rv = st.cons->sat(&assumps, &asgn, NULL, SAT::NULL_GID, true, &lifted);
      if (rv) {
        vector<ID> asgnc, fullCube, inputs, nstate;
        if(st.ss.opts.printCex) {
          //Separate asgn into current state, input, and next state
          vector<ID> curState, nextState;
          fullAssignWithPrimedOf(st, asgn, curState, inputs, nextState);
          vector<ID> empty;
          addTransitionToCexTrace(st, nextState, empty);
          addTransitionToCexTrace(st, curState, inputs);
          asgnc = curState;
        }
        else {
#ifdef IBM_LIFTING
          fullAssignWithPrimedOf(st, asgn, fullCube, inputs, nstate);
          for(SAT::Assignment::iterator it = coiAsgn.begin(); it != coiAsgn.end();
              ++it) {
            it->second = asgn[it->first];
          }
          assignOf(st, coiAsgn, asgnc);
#else
          assignOf(st, asgn, asgnc);
#endif
        }
        vector<ID> cube(asgnc);
        set<ID> dummy;
        if(down(st, 1, dummy, cube)) {
          //Apply mic
          mic(st, 1, cube);
          addCube(st, 1, cube);
          fsisSubsumption(st);
        }
        else {
          if(!st.m.options().count("fsis_disable_lifting")) {
#ifdef IBM_LIFTING
            vector<ID> assumps;
            prepareCons(st, 1, assumps);
            assumps.insert(assumps.end(), inputs.begin(), inputs.end());
            //size_t numInputs = inputs.size();
            assumps.insert(assumps.end(), fullCube.begin(), fullCube.end());
            vector<ID> cubeNeg;
            for(vector<ID>::const_iterator it = nstate.begin(); it != nstate.end(); ++it) {
              cubeNeg.push_back(st.ev.prime(st.ev.apply(Expr::Not, *it)));
            }
            SAT::GID gid = st.cons->newGID();
            st.cons->add(cubeNeg, gid);
            bool sat = st.cons->sat(&assumps, NULL, &assumps, gid);
            assert(!sat);
            st.cons->remove(gid);
            int origSize = asgnc.size();
            asgnc.clear();
            ExprAttachment const * eat = (ExprAttachment *) st.m.constAttachment(Key::EXPR);
#if 0
            //Find the boundary between inputs and state variables
            size_t index = numInputs < assumps.size() ? numInputs - 1 : assumps.size() - 1;
            //Search backwards from startIndex for the first input
            size_t boundary;
            for(boundary = index; boundary >= 0; --boundary) {
              if(eat->isInput(assumps[boundary]) || eat->isInput(st.ev.apply(Expr::Not, assumps[boundary]))) {
                ++boundary;
                break;
              }
            }
            fullCube.insert(fullCube.end(), assumps.begin() + boundary, assumps.end());
#else
            for(vector<ID>::const_iterator it = assumps.begin();
                it != assumps.end(); ++it) {
              if(eat->isStateVar(*it) || eat->isStateVar(st.ev.apply(Expr::Not, *it))) {
                //Only add if in COI
                if(coiAsgn.find(*it) != coiAsgn.end() || coiAsgn.find(st.ev.apply(Expr::Not, *it)) != coiAsgn.end()) {
                  asgnc.push_back(*it);
                }
              }
            }
#endif
            vector<ID> asgnc2;
            assignOf(st, lifted, asgnc2);
            if(st.m.verbosity() > Options::Verbose) {
              cout << "Original cube size = " << origSize
                   << ", SAT solver lifted = " << asgnc2.size()
                   << ", IBM lifted = " << asgnc.size() << endl;
            }
            st.m.constRelease(eat);
#else
            asgnc.clear();
            assignOf(st, lifted, asgnc);
#endif
          }
          //Check if lifted cube satisfies initiation
          if(!initiation(st, asgnc))
            return false;

          //Add negation of cube to property
          //Property becomes P ^ !c where c is the cube
          addCube(st, 1, asgnc);

          EliminateSet toEliminate;
          sort(asgnc.begin(), asgnc.end());
          toEliminate.insert(ToEliminate(1, asgnc));
          vector<Node> dummy;
          recordLits(st, asgnc);
          bool succeeded = recurCTI(st, toEliminate, dummy);
          if(!succeeded)
            return false;
        }
      }
      else {
        if (st.m.verbosity() > Options::Informative)
          cout << "FSIS: SAT Count: " << st.cons->manager().satCount() << " " 
               << ((float) st.cons->manager().satTime() / 
                   (float) Util::get_user_cpu_time())  
               << endl;
        return true;
      }
    }
  }


  void fsisCheck(SharedState & sst) {
    State st(sst);
    fsisInitSAT(st);
    sst.stime = Util::get_user_cpu_time();
    extend(st, 0);
    bool succeeded = fsisStrengthen(st);
    if(succeeded)
      throw Safe();
    else
      throw CEX();
  }
}

namespace IC3 {

  MC::ReturnValue check(Model & m, IC3Options & opts,
                        vector<Transition> * cexTrace,
                        vector< vector<ID> > * proofCNF, 
                        vector<ID> * gprop,
                        vector<CubeSet> * cubes,
                        vector<LevClauses> * propClauses,
                        CubeSet * indCubes,
                        bool useRAT) {
    RchAttachment const * rat = (RchAttachment *) m.constAttachment(Key::RCH);
    unsigned int clb = useRAT ? rat->cexLowerBound() : 0;
    m.constRelease(rat);
    MC::ReturnValue rv;
    if (clb <= 1) {
      size_t k = opts.bmcsz ? 2 : 1;
      //size_t k = 1000;
      BMC::BMCOptions bopts;
      bopts.useCOI = false;
      bopts.lo = opts.bmcsz ? 1 : clb;
      bopts.bound = &k;
      bopts.printCex = opts.printCex;
      bopts.constraints = opts.constraints;
      bopts.iictl = opts.iictl;
      bopts.iictl_clauses = opts.iictl_clauses;
      bopts.silent = opts.silent;
      rv = BMC::check(m, bopts, cexTrace);
    }
    if (rv.returnType != MC::Unknown) {
      if(opts.printCex) {
        Expr::Manager::View * ev = m.newView();
        for(vector<Transition>::iterator it = cexTrace->begin(); it != cexTrace->end(); ++it) {
          ev->sort(it->state.begin(), it->state.end());
          ev->sort(it->inputs.begin(), it->inputs.end());
        }
      }
      return rv;
    }
    if (m.verbosity() > Options::Silent && !opts.silent)
      cout << "IC3: starting" << (opts.reverse ? " (reverse)" : "") << endl;
    int rseed = m.options()["rand"].as<int>();
    if(rseed != -1) {
      srand(rseed);
      Sim::RandomGenerator::generator.seed(static_cast<unsigned int>(rseed));
    }
    SharedState sstate(m, opts, cubes, propClauses);
    MC::ReturnValue rt;
    try {
      check(sstate, !proofCNF);
    }
    catch (CEX cex) {
      rt.returnType = MC::CEX;
      if(cexTrace != NULL) {
        assert(!cex.cexTrace.empty());
        Expr::Manager::View * ev = m.newView();
        *cexTrace = cex.cexTrace;
        reverse(cexTrace->begin(), cexTrace->end());
        for(vector<Transition>::iterator it = cexTrace->begin(); it != cexTrace->end(); ++it) {
          ev->sort(it->state.begin(), it->state.end());
          ev->sort(it->inputs.begin(), it->inputs.end());
        }
        delete ev;
      }
      if(cubes != NULL) {
        *cubes = sstate.cubes;
        vector< vector<ID> > empty;
        propClauses->push_back(LevClauses(cex.level, empty));
      }
      if(indCubes != NULL) {
        *indCubes = cex.indCubes;
      }
    }
    catch (Safe safe) {
      rt.returnType = MC::Proof;
      if(proofCNF != NULL) {
        Expr::Manager::View * ev = m.newView();
        proofCNF->insert(proofCNF->end(), safe.proof.begin(), safe.proof.end());
        for(vector< vector<ID> >::iterator it = proofCNF->begin();
            it != proofCNF->end(); ++it)
          for(vector<ID>::iterator lit = it->begin(); lit != it->end(); ++lit)
            *lit = ev->apply(Expr::Not, *lit);
        delete ev;
        if (gprop) *gprop = safe.gprop;
      }
    }
    catch (Timeout to) {
      rt.returnType = MC::Unknown;

      if (!sstate.opts.reverse) {
        // do the incremental thing here, as well
        if (indCubes) {
          int timeout = sstate.opts.timeout;
          sstate.opts.timeout = -1;
          State st(sstate);
          initSAT(st);
          renewSAT(st);
          for (uint k = 0; k <= st.cubes.size()-2; ++k) extend(st, k);
          propagateClausesSpecial(st, st.cubes.size()-2, *indCubes);
          sstate.opts.timeout = timeout;
          if (cubes && sstate.opts.incremental) {
            CubeSet result;
            set_difference(sstate.cubes.back().begin(), sstate.cubes.back().end(),
                           indCubes->begin(), indCubes->end(),
                           inserter(result, result.end()));
            sstate.cubes.back() = result;
          }
        }
        if(cubes && sstate.opts.incremental) {
          *cubes = sstate.cubes;
          // IGNORE propClauses
        }
      }

      if (useRAT) {
        RchAttachment * rat = (RchAttachment *) m.constAttachment(Key::RCH);
        Expr::Manager::View * ev = m.newView();
        for (unsigned int i = 0; i < sstate.cubes.size(); ++i) {
          const CubeSet & cs = sstate.cubes[i];
          vector< vector<ID> > lvl(cs.begin(), cs.end());
          for (vector< vector<ID> >::iterator it = lvl.begin(); it != lvl.end(); it++)
            for (vector<ID>::iterator lit = it->begin(); lit != it->end(); lit++)
              *lit = ev->apply(Expr::Not, *lit);
          if (sstate.reverse)
            rat->setKBackwardUpperBound(i, lvl);
          else
            rat->setKForwardUpperBound(i, lvl);
        }
        if (sstate.cubes.size() > 2)
          rat->updateCexLowerBound(sstate.cubes.size() - 2);
        delete ev;
        m.release(rat);
      }
    }
    catch (Trivial tr) {
      if (m.verbosity() > Options::Informative)
        cout << "IC3: trivially unsat\n";
      rt.returnType = MC::Proof;
    }
    catch (SAT::Trivial tr) {
      cout << tr.value() << endl;
      assert (false);
    }

    if(opts.stats)
      sstate.stats.print();
    
    return rt;
  }

  void clean(vector< vector<ID> > & proof) {
    for (vector< vector<ID> >::iterator it = proof.begin(); it != proof.end(); ++it)
      sort(it->begin(), it->end());
    CubeSet cs(proof.begin(), proof.end());
    proof.clear();
    proof.insert(proof.end(), cs.begin(), cs.end());
  }

  bool verifyProof(Model & m, vector< vector<ID> > & proof, vector<SAT::Clauses> * constraints, IC3Options & opts, vector<ID> * gprop = NULL) {

    if (m.verbosity() == Options::Silent) return true;

    if(m.verbosity() > Options::Informative) {
      cout << "IC3: Verifying proof" << endl;
    }
   
    SAT::Manager * propertyMgr = m.newSATManager();
    SAT::Manager * proofMgr = m.newSATManager();
    Expr::Manager::View * ev = m.newView();

    ExprAttachment const * eat = (ExprAttachment *) m.constAttachment(Key::EXPR);
    ID npi = eat->outputFnOf(eat->outputs()[0]);
    vector<ID> init(eat->initialConditions());
    m.constRelease(eat);

    vector< vector< ID> > property;
    Expr::tseitin(*ev, ev->apply(Expr::Not, npi), property);

    CNFAttachment * cnfat = (CNFAttachment *) m.constAttachment(Key::CNF);
    vector< vector<ID> > transRel = cnfat->getCNF();
    m.constRelease(cnfat);

    vector< vector<ID> > negPropertyPrimed;
    Expr::tseitin(*ev, Expr::primeFormula(*ev, npi), negPropertyPrimed);

    ID proofID = ev->btrue();
    for(unsigned i = 0; i < proof.size(); ++i) {
      ID clauseID = ev->bfalse();
      for(unsigned j = 0; j < proof[i].size(); ++j) {
        clauseID = ev->apply(Expr::Or, clauseID, proof[i][j]);
      }
      proofID = ev->apply(Expr::And, proofID, clauseID);
    }
    vector< vector<ID> > negProof;
    Expr::tseitin(*ev, ev->apply(Expr::Not, proofID), negProof);
    vector< vector<ID> > negProofPrimed(negProof);
    for (vector< vector<ID> >::iterator it = negProofPrimed.begin(); it != negProofPrimed.end(); ++it)
      Expr::primeFormulas(*ev, *it);

    // include user-provided constraints
    vector< vector<ID> > ccls;
    if (constraints)
      for (unsigned i = 0; i < constraints->size(); ++i)
        ccls.insert(ccls.end(), (*constraints)[i].begin(), (*constraints)[i].end());

    if (opts.constraints)
      for (unsigned i = 0; i < opts.constraints->size(); ++i)
        ccls.insert(ccls.end(), (*opts.constraints)[i].begin(), (*opts.constraints)[i].end());

    bool init_sat = true, prop_sat = true, proof_sat = true;

    {
      SharedState sst(m, opts);
      State _st(sst);
      initSAT(_st);
      if (sst.simpleInit) {
        SAT::Manager * initMgr = m.newSATManager();
        SAT::Manager::View* initView = initMgr->newView(*ev);
        try {
          for (size_t i = 0; i < init.size(); ++i) {
            vector<ID> cls(1, init[i]);
            initMgr->add(cls);
          }
          initMgr->add(negProof);
          init_sat = initView->sat();
        }
        catch (SAT::Trivial tr) {
          assert (!tr.value());
          init_sat = false;
        }
        delete initView;
        delete initMgr;
      }
      else {
        try {
          _st.ss.init->add(negProof);
          init_sat = _st.init->sat();
        }
        catch (SAT::Trivial tr) {
          assert (!tr.value());
          init_sat = false;
        }
      }
    }

    SAT::Manager::View* propertyView = propertyMgr->newView(*ev);
    try {
      //propertyMgr->add(property);
      propertyMgr->add(transRel);
      propertyMgr->add(proof);
      propertyMgr->add(negPropertyPrimed);
      propertyMgr->add(ccls);
      prop_sat = propertyView->sat();
    }
    catch (SAT::Trivial tr) {
      assert (!tr.value());
      prop_sat = false;
    }
    delete propertyView;

    SAT::Manager::View* proofView = proofMgr->newView(*ev);
    try {
      //proofMgr->add(property);
      if(gprop) {
        for(vector<ID>::iterator it = gprop->begin(); it != gprop->end();
            ++it) {
          vector<ID> cls;
          cls.push_back(*it);
          proofMgr->add(cls);
        }
      }
      proofMgr->add(transRel);
      proofMgr->add(proof);
      proofMgr->add(negProofPrimed);
      proofMgr->add(ccls);
      proof_sat = proofView->sat();
    } 
    catch (SAT::Trivial tr) {
      assert (!tr.value());
      proof_sat = false;
    }
    delete proofView;

    if(m.verbosity() > Options::Informative) {
      cout << "Initial condition satisfied? " << (init_sat? "No" : "Yes") << endl;
      cout << "Property inductive? " << (prop_sat? "No" : "Yes") << endl;
      cout << "Proof inductive? " << (proof_sat? "No" : "Yes") << endl;
    }

    delete ev;
    delete propertyMgr;
    delete proofMgr;

    return !(init_sat || prop_sat || proof_sat);
  }


  void postProcessProof(Model & m, vector< vector<ID> > & proof, ProofProcType type,
      IC3Options & opts, vector<ID> * gprop) {
    if(proof.empty()) //Nothing to process
      return;

    ProofPostProcState st(m, opts);
    if(gprop && !opts.iictl)
      st.gprop = *gprop;
    initProofPostProcState(st);
    
    //assert(verifyProof(m, proof, opts.constraints, opts));

    if (type == STRENGTHEN) {
      //Strengthen proof
      deriveStrongerProof(st, proof, opts);
      clean(proof);
      //assert(verifyProof(m, proof, opts.constraints, opts, gprop));
    }
    else if (type == WEAKEN) {
      //Weaken proof
      deriveWeakerProof(st, proof);
      clean(proof);
      //assert(verifyProof(m, proof, opts.constraints, opts, gprop));
    }
    else if (type == SHRINK) {
      //assert(verifyProof(m, proof, opts.constraints, opts, gprop));
    }
    else
      assert(false);
  }

  MC::ReturnValue reach(Model & m, IC3Options & opts,
                        vector< vector< vector<ID> > > & proofs,
                        vector<Transition> * cex) {

    vector< vector<ID> > rawProof;
    vector<ID> gprop;

    bool old_cycle = opts.cycle;
    opts.eqprop = false;
    opts.cycle = true;
    MC::ReturnValue rv = check(m, opts, cex, &rawProof, &gprop, NULL, NULL, NULL, false);
    opts.cycle = old_cycle;
    int timeout = opts.timeout;
    opts.timeout = -1;
    
    if(rv.returnType == MC::Proof) {

      if (rawProof.size() > 0) {
       
        assert(!gprop.empty());

        ProofPostProcState st(m, gprop, opts.constraints, opts);
        initProofPostProcState(st);
    
        assert(verifyProof(m, rawProof, opts.constraints, opts));

        if(opts.proofProc == STRENGTHEN) {
          vector< vector<ID> > strongerProof = rawProof;
          deriveStrongerProof(st, strongerProof, opts);
          strongerProof.push_back(st.gprop);
          clean(strongerProof);
          proofs.push_back(strongerProof);
          assert(verifyProof(m, strongerProof, opts.constraints, opts));
        }
        else if (opts.proofProc == WEAKEN) {
          vector< vector<ID> > weakerProof = rawProof;
          deriveWeakerProof(st, weakerProof);
          weakerProof.push_back(st.gprop);
          clean(weakerProof);
          proofs.push_back(weakerProof);
          assert(verifyProof(m, weakerProof, opts.constraints, opts));
        }
        else if (opts.proofProc == SHRINK) {
          vector< vector<ID> > smallerProof = rawProof;
          deriveSmallerProof(st, smallerProof, opts);
          smallerProof.push_back(st.gprop);
          clean(smallerProof);
          proofs.push_back(smallerProof);
          assert(verifyProof(m, smallerProof, opts.constraints, opts));
        }
      }
      else {
        rawProof.push_back(gprop);
        clean(rawProof);
        proofs.push_back(rawProof);
        assert(verifyProof(m, rawProof, opts.constraints, opts));
      }
    }

    opts.timeout = timeout;

    return rv;
  }

  MC::ReturnValue reach2(Model & m, IC3Options & opts,
                         vector<Transition> * cex,
                         vector< vector< vector<ID> > > * proofs,
                         vector<CubeSet> * cubes,
                         vector<LevClauses> * propClauses,
                         CubeSet * indCubes) {

    bool old_cycle = opts.cycle;
    opts.eqprop = false;
    opts.cycle = true;
    vector< vector<ID> > * rawProof = NULL;
    if(proofs != NULL) {
      proofs->push_back(vector< vector<ID> >());
      rawProof = &((*proofs)[0]);
    }
    vector<ID> gprop;
    MC::ReturnValue rv = check(m, opts, cex, rawProof, &gprop, cubes, propClauses, indCubes, false);
    opts.cycle = old_cycle;
    int timeout = opts.timeout;
    opts.timeout = -1;
    
    if(rv.returnType == MC::Proof && rawProof) {
      if(!opts.proofProc == NONE) 
        postProcessProof(m, *rawProof, opts.proofProc, opts, &gprop);
      if(!opts.iictl)
        rawProof->push_back(gprop);
    }
    opts.timeout = timeout;

    return rv;
  }

  bool mic(Model & m, IC3Options & opts, vector<ID> & cube) {
    
    SharedState sst(m, opts);
    State _st(sst);
    initSAT(_st);
    extend(_st, 0);

    set<ID> dummy;
    if(down(_st, 1, dummy, cube)) {
      mic(_st, 1, cube, true);
      return true;
    }
    return false;
  }
}

namespace FSIS {

  MC::ReturnValue check(Model & m, IC3::IC3Options & opts,
                        vector<Transition> * cexTrace,
                        vector< vector<ID> > * proofCNF, 
                        vector<ID> * gprop,
                        bool useRAT) {

    RchAttachment const * rat = (RchAttachment *) m.constAttachment(Key::RCH);
    unsigned int clb = useRAT ? rat->cexLowerBound() : 0;
    m.constRelease(rat);
    MC::ReturnValue rv;
    if (clb <= 0) {
      size_t k = 0;
      BMC::BMCOptions bopts;
      bopts.useCOI = false;
      bopts.lo = 0;
      bopts.bound = &k;
      bopts.printCex = opts.printCex;
      rv = BMC::check(m, bopts, cexTrace);
    }
    if (rv.returnType != MC::Unknown) {
      if(opts.printCex) {
        Expr::Manager::View * ev = m.newView();
        for(vector<Transition>::iterator it = cexTrace->begin(); it != cexTrace->end(); ++it) {
          ev->sort(it->state.begin(), it->state.end());
          ev->sort(it->inputs.begin(), it->inputs.end());
        }
      }
      return rv;
    }
    if (m.verbosity() > Options::Silent)
      cout << "FSIS: starting" << endl;
    int rseed = m.options()["rand"].as<int>();
    if(rseed != -1) {
      srand(rseed);
      Sim::RandomGenerator::generator.seed(static_cast<unsigned int>(rseed));
    }
    SharedState sstate(m, opts);
    MC::ReturnValue rt;
    try {
      fsisCheck(sstate);
    }
    catch (CEX cex) {
      rt.returnType = MC::CEX;
      if(cexTrace != NULL) {
        assert(!cex.cexTrace.empty());
        Expr::Manager::View * ev = m.newView();
        *cexTrace = cex.cexTrace;
        reverse(cexTrace->begin(), cexTrace->end());
        for(vector<Transition>::iterator it = cexTrace->begin(); it != cexTrace->end(); ++it) {
          ev->sort(it->state.begin(), it->state.end());
          ev->sort(it->inputs.begin(), it->inputs.end());
        }
        delete ev;
      }
    }
    catch (Safe safe) {
      rt.returnType = MC::Proof;
      if(proofCNF != NULL) {
        Expr::Manager::View * ev = m.newView();
        proofCNF->insert(proofCNF->end(), safe.proof.begin(), safe.proof.end());
        for(vector< vector<ID> >::iterator it = proofCNF->begin();
            it != proofCNF->end(); ++it)
          for(vector<ID>::iterator lit = it->begin(); lit != it->end(); ++lit)
            *lit = ev->apply(Expr::Not, *lit);
        delete ev;
        if (gprop) *gprop = safe.gprop;
      }
    }
    catch (Timeout to) {
      rt.returnType = MC::Unknown;

      if (useRAT) {
        RchAttachment * rat = (RchAttachment *) m.constAttachment(Key::RCH);
        Expr::Manager::View * ev = m.newView();
        for (unsigned int i = 0; i < sstate.cubes.size(); ++i) {
          const CubeSet & cs = sstate.cubes[i];
          vector< vector<ID> > lvl(cs.begin(), cs.end());
          for (vector< vector<ID> >::iterator it = lvl.begin(); it != lvl.end(); it++)
            for (vector<ID>::iterator lit = it->begin(); lit != it->end(); lit++)
              *lit = ev->apply(Expr::Not, *lit);
          if (sstate.reverse)
            rat->setKBackwardUpperBound(i, lvl);
          else
            rat->setKForwardUpperBound(i, lvl);
        }
        if (sstate.cubes.size() > 2)
          rat->updateCexLowerBound(sstate.cubes.size() - 2);
        delete ev;
        m.release(rat);
      }
    }
    catch (Trivial tr) {
      if (m.verbosity() > Options::Informative)
        cout << "IC3: trivially unsat\n";
      rt.returnType = MC::Proof;
    }
    catch (SAT::Trivial tr) {
      cout << tr.value() << endl;
      assert (false);
    }
    return rt;
  }


}
