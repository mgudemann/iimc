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

#include "FSIS.h"
#include "IC3.h"

#include "BMC.h"
#include "Error.h"
#include "Expr.h"
#include "ExprUtil.h"
#include "Model.h"
#include "SAT.h"
#include "Sim.h"
#include "SimUtil.h"
#include "ThreeValuedSimulation.h"
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
    Stats() : level(0), cubeSizeBef(0), cubeSizeIBM(0),
              cubeSizeBrute(0), numLiftCubes(0), ibmLiftTime(0), 
              bruteLiftTime(0), numBruteIter(0),
              numMicCalls(0), numUpCalls(0), numDownCalls(0),
              clauseSizeBef(0), clauseSizeAft(0), micTime(0),
              numConsPW(0), numSuccPW(0), repeats(0), numSuccDown(0), numSuccDownWithJoin(0), numDownWithJoin(0),
              numDownWithCtg(0), numSuccDownWithCtg(0)
    {
      numPropQueries.push_back(0);
      numClauses.push_back(0);
      percentProp.push_back(0);
      clauseDistBef.push_back(vector<uint64_t>());
      clauseDistAft.push_back(vector<uint64_t>());
      levInd.push_back(0);
      numGenCalls.push_back(0);
      maxDlvl.push_back(1);
      startTime = Util::get_user_cpu_time();
      startSatCalls = SAT::Manager::satCount();
      startSatTime = SAT::Manager::satTime();
    }

    void print() {
      const string ic3 = "IC3: ";
      cout << endl;
      cout << "============================ IC3 Statistics ============================" << endl;
      int64_t elapsedTime = Util::get_user_cpu_time() - startTime;
      int64_t satTime = SAT::Manager::satTime() - startSatTime;
      cout << ic3 << "Total time = " << elapsedTime / 1000000.0 << "s"
           << " (SAT time = " << satTime / 1000000.0 << "s = "
           << 100.0 * satTime / double(elapsedTime) << "%)" << endl;
      unsigned satCount = SAT::Manager::satCount() - startSatCalls;
      cout << ic3 << "Number of SAT calls = " << satCount << endl;
      cout << ic3 << "SAT calls per second = " << satCount * 1000000.0 / satTime << endl;
      cout << ic3 << "Final level reached = " << level << endl;
      for(unsigned i = 1; i < numPropQueries.size(); ++i) {
        cout << ic3 << "Number of property inductiveness queries at level "
             << i << " = " << numPropQueries[i] << endl;
      }
      uint64_t totalClauses = 0;
      for(unsigned i = 1; i < numClauses.size(); ++i) {
        cout << ic3 << "Number of clauses derived at level " << i << " = "
             << numClauses[i] << endl;
        totalClauses += numClauses[i];
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

      cout << ic3 << "Total PW Cons = " << numConsPW << endl;
      cout << ic3 << "Succ PW Cons = " << numSuccPW << endl;
      cout << ic3 << "Repeated clauses = " << repeats << endl;

      cout << "Total number of clauses = " << totalClauses << endl;
      cout << ic3 << "Successful down calls = " << numSuccDown << " / " << numDownCalls
           << " = " << 100.0 * numSuccDown / double(numDownCalls)
           << "%, involved joining = " << numSuccDownWithJoin << " / " << numDownWithJoin
           << " = " << 100.0 * numSuccDownWithJoin / double(numDownWithJoin)
           << "%, involved CTG handling = " << numSuccDownWithCtg << " / " << numDownWithCtg
           << " = " << 100.0 * numSuccDownWithCtg / double(numDownWithCtg) << "%"
           << endl;
      int maxMaxDlvl = 0;
      for (unsigned i = 1; i < maxDlvl.size(); ++i) {
        cout << ic3 << "Maximum dlvl at level " << i << " = " << maxDlvl[i] << endl;
        maxMaxDlvl = max(maxMaxDlvl, maxDlvl[i]);
      }
      cout << ic3 << "Absolute maximum dlvl = " << maxMaxDlvl << endl;
    }

    int level;                          //Final level reached
    vector<uint64_t> numPropQueries;    //Number of property inductiveness queries for each level
    vector<uint64_t> numClauses;        //Number of clauses derived at each level
    uint64_t cubeSizeBef;               //Sum of CTI cube sizes before lifting
    uint64_t cubeSizeIBM;               //Sum of CTI cube sizes after IBM lifting
    uint64_t cubeSizeBrute;             //Sum of CTI cube sizes after brute-force lifting
    uint64_t numLiftCubes;              //Number of cubes on which lifting was applied
    uint64_t ibmLiftTime;               //Total time spent in IBM lifting
    uint64_t bruteLiftTime;             //Total time spent in brute-force lifting
    uint64_t numBruteIter;              //Total number of brute-force iterations
    vector<uint64_t> numGenCalls;       //Number of calls to generalize() on a property CTI
    vector<uint64_t> levInd;            //Sum of levels at which a clause (the negation of a property CTI) is found to be inductive
    vector<int> maxDlvl;
    uint64_t numMicCalls;               //Total number of calls to MIC
    uint64_t numUpCalls;                //Total number of calls to UP
    uint64_t numDownCalls;              //Total number of calls to DOWN
    uint64_t clauseSizeBef;             //Sum of clause sizes before MIC'ing
    uint64_t clauseSizeAft;             //Sum of clause sizes after MIC'ing
    uint64_t micTime;                   //Total time spent in MIC
    vector<double> percentProp;         //Average percentage of clauses propagated for each level
    vector< vector<uint64_t> > clauseDistBef; //The distribution of clauses among the different levels before clause propagation
    vector< vector<uint64_t> > clauseDistAft; //The distribution of clauses among the different levels after clause propagation

    uint64_t numConsPW;
    uint64_t numSuccPW;
    uint64_t repeats;
    uint64_t numSuccDown;
    uint64_t numSuccDownWithJoin;
    uint64_t numDownWithJoin;
    uint64_t numDownWithCtg;
    uint64_t numSuccDownWithCtg;
    int64_t startTime;
    unsigned startSatCalls;
    uint64_t startSatTime;
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
      init(NULL), cons(NULL), icons(NULL), lift(NULL), fae(NULL),
      stem(NULL), stem_plus(NULL), ev(NULL)
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

    vector< vector<ID> > abs_tr;
    vector< vector<ID> > abs_ptr;
    ID abs_er;

    SAT::Clauses * stem;
    SAT::Clauses * stem_plus;

    Stats stats;

    Expr::Manager::View * ev;

    //For lifting
    ID actPp;
    ID actNegCp;
    ID actNegG;
    ID actNegTp;
  };

  class State {
  public:
    State(SharedState & sst) : 
      ss(sst), m(sst.m), opts(sst.opts), _ev(sst.ev ? sst.ev : sst.m.newView()), ev(*_ev), cubes(sst.cubes), infCubes(sst.infCubes), propClauses(sst.propClauses), id(0), 
      init(NULL), cons(NULL), icons(NULL), lift(NULL), fae(NULL),  faeLits(sst.faeLits)
    {
      init = sst.init ? sst.init->newView(ev, opts.backend) : NULL;
      cons = sst.cons->newView(ev, opts.backend);
      if (opts.timeout > 0)
        cons->timeout(opts.timeout);
    }
    ~State() {
      if (!ss.ev) delete _ev;
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

    set<ID> avars;
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

  void _printVector(Expr::Manager::View & ev, const vector<ID> & c) {
    for (vector<ID>::const_iterator it = c.begin(); it != c.end(); it++)
      cout << " " << Expr::stringOf(ev, *it);
    cout << endl;
  }
  void printVector(State & st, const vector<ID> & c) {
    if (st.m.verbosity() > Options::Informative)
      _printVector(st.ev, c);
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
    if (ss.opts.abstract > 0 && ss.opts.abstract < 3) return;

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

#if 0
    set<ID> tcvars, cvars;
    if (ss.opts.constraints)
      for (unsigned i = 0; i < ss.opts.constraints->size(); ++i)      
        for (SAT::Clauses::const_iterator j = (*ss.opts.constraints)[i].begin();
             j != (*ss.opts.constraints)[i].end(); ++j)
          for (vector<ID>::const_iterator jj = j->begin(); jj != j->end(); ++jj) {
            ID v = ev.op(*jj) == Expr::Not ? ev.apply(Expr::Not, *jj) : *jj;
            v = ev.primeTo(v, 0);
            tcvars.insert(v);
          }
    ExprAttachment const * eat = (ExprAttachment *) ss.m.constAttachment(Key::EXPR);
    vector<ID> cfns(eat->constraintFns());
    ss.m.constRelease(eat);
    Expr::variables(ev, cfns, tcvars);
    set<ID> slatches(latches.begin(), latches.end());
    set_intersection(tcvars.begin(), tcvars.end(), slatches.begin(), slatches.end(),
                     inserter(cvars, cvars.end()));
    if (!cvars.empty()) {
      ss.nrvars.clear();
      set<ID> tmp1, tmp2;
      set_union(nrvars.begin(), nrvars.end(), cvars.begin(), cvars.end(),
                inserter(tmp1, tmp1.end()));
      ss.nrvars = tmp1;
      set_difference(ss.rvars.begin(), ss.rvars.end(), cvars.begin(), cvars.end(),
                     inserter(tmp2, tmp2.end()));
      ss.rvars = tmp2;
    }
#endif

    if (ss.m.verbosity() > Options::Verbose)
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
      initf = exprOf(rat->forwardBddLowerBound(), st.ev, bat->order());
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
    if (use_flb || (!eat->constraintFns().empty() && !st.ss.opts.bmcsz)) {
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
      for (vector<ID>::const_iterator it = eat->constraintFns().begin(); it != eat->constraintFns().end(); ++it)
        Expr::tseitin(st.ev, *it, init_clauses);

      st.ss.icons = st.m.newSATManager();
      st.icons = st.ss.icons->newView(st.ev, st.ss.opts.backend);
      st.ss.icons->add(icons_clauses);

      st.ss.init = st.m.newSATManager();
      st.init = st.ss.init->newView(st.ev, st.ss.opts.backend);
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
      st.init = st.ss.init->newView(st.ev, st.ss.opts.backend);
      st.ss.init->add(tr0);
      // special case for k=0
      tr0.insert(tr0.end(), cons_clauses.begin(), cons_clauses.end());
      st.ss.icons = st.m.newSATManager();
      st.icons = st.ss.icons->newView(st.ev, st.ss.opts.backend);
      st.ss.icons->add(tr0);
    }

    vector< vector<ID> > error_clauses;
    ID npi;
    if (st.ss.bddTarget && rat->backwardStepsBdd() > 1) {
      st.ss.TESteps = rat->backwardStepsBdd() - 1;
      const BddAttachment * bat = (const BddAttachment *) st.m.constAttachment(Key::BDD);
      npi = exprOf(rat->backwardBddLowerBound(), st.ev, bat->order());
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

    if (st.m.verbosity() > Options::Terse) {
      ostringstream oss;
      oss << "IC3: Using " << st.opts.ctgs << " CTGs" << endl;
      cout << oss.str();
    }

    // get CNF encoding for transition relation
    CNFAttachment * cnfat = (CNFAttachment *) st.m.constAttachment(Key::CNF);
    vector< vector<ID> > cons_clauses;
    if (st.opts.abstract >= 2)
      cons_clauses = st.ss.abs_tr;
    else
      cons_clauses = cnfat->getCNF();

    if (st.ss.opts.intNodes) {
      SAT::Clauses temp = cnfat->getPlainCNF();
      for(SAT::Clauses::iterator it = temp.begin(); it != temp.end();
          ++it) {
        primeFormulas(st.ev, *it);
      }
      cons_clauses.insert(cons_clauses.end(), temp.begin(), temp.end());
    }
 
    // for internal nodes replace DAG IDs with SAT IDs 
    Expr::IDMap satIdOfId = cnfat->satIdOfId; 
    if (st.ss.opts.intNodes){
      vector<ID> * kCOI = st.ss.coi.kCOIplusInt();
      for (vector<ID>::iterator it = kCOI->begin(); it != kCOI->end(); ++it) {
	if (satIdOfId.find(*it) == satIdOfId.end())
	  assert(st.ev.op(*it) == Expr::Var);
	else{
	  *it = satIdOfId[*it];
	}
      }
    }
    
    // include user-provided constraints
    vector< vector<ID> > constraints;
    if (st.ss.opts.constraints)
      for (unsigned i = 0; i < st.ss.opts.constraints->size(); ++i) {
        cons_clauses.insert(cons_clauses.end(), 
                            (*st.ss.opts.constraints)[i].begin(), 
                            (*st.ss.opts.constraints)[i].end());
        constraints.insert(constraints.end(), 
                           (*st.ss.opts.constraints)[i].begin(),
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
    ID initf = st.ev.btrue();
    if (use_flb) {
      const BddAttachment * bat = (const BddAttachment *) st.m.constAttachment(Key::BDD);
      initf = exprOf(rat->forwardBddLowerBound(), st.ev, bat->order());
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
    vector<ID> nonImpliedConstraints;
    if (!eat->constraintFns().empty() && !st.ss.opts.bmcsz) {
      //Build a map from latch to initial value
      Expr::IDMap initial;
      for (vector<ID>::const_iterator it = init.begin(); it != init.end();
           ++it) {
        ID latch = var(st, *it);
        initial.insert(Expr::IDMap::value_type(latch, latch == *it ? 
                                               st.ev.btrue() : st.ev.bfalse()));
      }
      SAT::Manager * sman = st.m.newSATManager();
      for (vector<ID>::const_iterator it = eat->constraintFns().begin();
           it != eat->constraintFns().end(); ++it) {
        ID sub = varSub(st.ev, initial, *it);
        if (sub == st.ev.btrue())
          continue;
        //Do a semantic check
        SAT::Manager::View * sview = sman->newView(st.ev, st.ss.opts.backend);
        SAT::Clauses clauses;
        Expr::tseitin(st.ev, st.ev.apply(Expr::Not, sub), clauses);
        try {
          sview->add(clauses);
        }
        catch (SAT::Trivial tr) {
          assert(!tr.value());
          delete sview;
          continue;
        }
        bool sat = sview->sat(&init);
        if (sat) {
          nonImpliedConstraints.push_back(*it);
        }
        delete sview;
      }
      delete sman;
    }
    if (st.ss.stem) {
      if (st.m.verbosity() > Options::Informative)
        cout << "IC3: stem length: " << st.ss.opts.stem << endl;
      st.ss.bddInit = false;
      st.ss.simpleInit = false;
      st.m.constRelease(rat);

      st.ss.init = st.m.newSATManager();
      st.init = st.ss.init->newView(st.ev, st.ss.opts.backend);
      st.ss.init->add(*(st.ss.stem));

      st.ss.icons = st.m.newSATManager();
      st.icons = st.ss.icons->newView(st.ev, st.ss.opts.backend);
      st.ss.icons->add(*(st.ss.stem));
      st.ss.icons->add(*(st.ss.stem_plus));
    }
    else if (st.ss.opts.intNodes || use_flb || !nonImpliedConstraints.empty()) {
      if (st.m.verbosity() > Options::Informative)
        cout << "IC3: using SAT queries for initiation checks" << endl;
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
      for (vector<ID>::const_iterator it = nonImpliedConstraints.begin(); 
           it != nonImpliedConstraints.end(); ++it)
        Expr::tseitin(st.ev, *it, init_clauses);

      st.ss.icons = st.m.newSATManager();
      st.icons = st.ss.icons->newView(st.ev, st.ss.opts.backend);
      st.ss.icons->add(icons_clauses);

      st.ss.init = st.m.newSATManager();
      st.init = st.ss.init->newView(st.ev, st.ss.opts.backend);
      st.ss.init->add(init_clauses);
      if (st.ss.opts.intNodes) {
        SAT::Clauses temp2 = cnfat->getPlainCNF();
        st.ss.init->add(temp2);
      }

      if(st.ss.opts.constraints)
        for (unsigned i = 0; i < st.ss.opts.constraints->size(); ++i) {
          st.ss.init->add((*st.ss.opts.constraints)[i]);
        }
      if (!st.init->sat()) throw Trivial();
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
      SAT::Clauses tr0;
      if (st.opts.abstract == 3)
        tr0 = st.ss.abs_ptr;
      else
        tr0 = cnfat->getPlainCNF();
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
      st.init = st.ss.init->newView(st.ev, st.ss.opts.backend);
      st.ss.init->add(tr0);
      // special case for k=0
      tr0.insert(tr0.end(), cons_clauses.begin(), cons_clauses.end());
      st.ss.icons = st.m.newSATManager();
      st.icons = st.ss.icons->newView(st.ev, st.ss.opts.backend);
      st.ss.icons->add(tr0);
    }

    vector< vector<ID> > error_clauses;
    ID npi;
    if (st.ss.bddTarget && rat->backwardStepsBdd() > 1) {
      st.ss.TESteps = rat->backwardStepsBdd() - 1;
      const BddAttachment * bat = (const BddAttachment *) st.m.constAttachment(Key::BDD);
      npi = exprOf(rat->backwardBddLowerBound(), st.ev, bat->order());
      st.m.constRelease(bat);
      Expr::tseitin(st.ev, st.ev.apply(Expr::Not, npi), cons_clauses);
    }
    else {
      st.ss.bddTarget = false;
      if (st.opts.abstract >= 2)
        npi = st.ss.abs_er;
      else
        npi = eat->outputFnOf(eat->outputs()[0]);
      vector<ID> cube;
      Expr::conjuncts(st.ev, npi, cube);
      npi = st.ev.apply(Expr::And, cube);
    }
    if (npi == st.ev.bfalse()) throw Safe();
    if (npi == st.ev.btrue()) throw CEX();
    if(!st.ss.opts.iictl) {
      if (st.ss.opts.intNodes) {
        Expr::tseitin(st.ev, npi, error_clauses);
        for (vector< vector<ID> >::iterator it = error_clauses.begin(); it != error_clauses.end(); ++it) {
          Expr::primeFormulas(st.ev, *it);
        }
      }
      else
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
      if (st.m.verbosity() > Options::Terse)
        cout << "IC3: lifting enabled" << endl;
      //Only lift if constraints are not functions of primary inputs
      set<ID> vars;
      bool ok = true;
      vector<ID> tmp(eat->constraintFns());
      Expr::variables(st.ev, tmp, vars);
      for (set<ID>::iterator it = vars.begin(); it != vars.end(); ++it) {
        if (eat->isInput(*it)) {
          ok = false;
          break;
        }
      }
      if (!ok) {
        if (st.m.verbosity() > Options::Terse)
          cout << "IC3: Disabling lifting" << endl;
        st.opts.lift = false;
      }
      else {
        st.ss.lift = st.m.newSATManager();
        st.lift = st.ss.lift->newView(st.ev, st.ss.opts.backend);
        //Lifting query:
        //P & C & T & (!C' | !G(x,x') | P') for property CTIs and
        //P & C & T & (!C' | !G(x,x') | !t') for clause CTIs
        //C: invariant constraints
        //G(x,x'): relational constraints
        //!t: clause (negation of target cube)
        SAT::Clauses trNpi = cnfat->getPlainCNFNoConstraints(); //T
        Expr::tseitin(st.ev, st.ev.apply(Expr::Not, eat->outputFns()[0]), trNpi); //P
        vector<ID> constraints(eat->constraintFns());
        Expr::tseitin(st.ev, constraints, trNpi); //C
        st.lift->add(trNpi);

        st.ss.actPp = st.ev.newVar("_@actPp@_");
        st.ss.actNegCp = st.ev.newVar("_@actNegCp@_");
        st.ss.actNegG = st.ev.newVar("_@actNegG@_");
        st.ss.actNegTp = st.ev.newVar("_@actNegTp@_");
        //Or
        vector<ID> disj;
        disj.push_back(st.ss.actPp);
        disj.push_back(st.ss.actNegCp);
        if (st.ss.opts.negConstraints)
          disj.push_back(st.ss.actNegG);
        disj.push_back(st.ss.actNegTp);
        st.lift->add(disj);
        vector< vector<ID> > property_clauses;
        Expr::tseitin(st.ev, Expr::primeFormula(st.ev, st.ev.apply(Expr::Not, npi)), property_clauses);
        for (vector< vector<ID> >::iterator it = property_clauses.begin();
             it != property_clauses.end(); ++it) {
          it->push_back(st.ev.apply(Expr::Not, st.ss.actPp));
        }
        st.lift->add(property_clauses);

        vector<ID> negCp(eat->constraintFns());
        primeFormulas(st.ev, negCp);
        for (vector<ID>::iterator it = negCp.begin(); it != negCp.end(); ++it) {
          *it = st.ev.apply(Expr::Not, *it);
        }
        SAT::Clauses negCpClauses;
        Expr::tseitin(st.ev, st.ev.apply(Expr::Or, negCp), negCpClauses);
        //Add activation literal
        for (SAT::Clauses::iterator it = negCpClauses.begin(); it != negCpClauses.end(); ++it) {
          it->push_back(st.ev.apply(Expr::Not, st.ss.actNegCp));
        }
        st.lift->add(negCpClauses);

        if (st.ss.opts.negConstraints) {
          SAT::Clauses negConstraints(*st.ss.opts.negConstraints);
          assert(!negConstraints.empty());
          SAT::Clause orClause = negConstraints.back();
          negConstraints.pop_back();
          orClause.push_back(st.ev.apply(Expr::Not, st.ss.actNegG));
          negConstraints.push_back(orClause);
          st.lift->add(negConstraints);
        }

        st.ss.fae = st.m.newSATManager();
        st.fae = st.ss.fae->newView(st.ev, st.ss.opts.backend);
        SAT::Clauses tr = cnfat->getPlainCNF();
        st.fae->add(tr);
        st.fae->add(error_clauses_cpy);
        st.faeLits.push_back(levelVar(st, -1));
      }
    }

    st.m.constRelease(eat);
    st.m.constRelease(cnfat);
  }

  void initReverseSAT(State & st) {
    st.ss.bddInit = false;
    st.ss.eqprop = false;
    st.ss.reverse = true;
    st.ss.simpleInit = false;
    st.ss.opts.lift = false;

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

    // initial condition
    ID initf = eat->outputFnOf(eat->outputs()[0]);
    if (initf == st.ev.btrue()) throw CEX();
    if (initf == st.ev.bfalse()) throw Safe();
    SAT::Clauses initf_cnf;
    Expr::tseitin(st.ev, initf, initf_cnf);

    // get CNF encoding for transition relation
    CNFAttachment * cnfat = (CNFAttachment *) st.m.constAttachment(Key::CNF);
    vector< vector<ID> > cons_clauses = cnfat->getPlainCNF();
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

    //ID x = Expr::primeFormula(st.ev, st.ev.apply(Expr::Not, initf));
    //Expr::tseitin(st.ev, x, cons_clauses);

    st.ss.init = st.m.newSATManager();
    st.init = st.ss.init->newView(st.ev, st.ss.opts.backend);
    st.ss.init->add(initf_cnf);
    vector<ID> constraints = eat->constraintFns();
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
    vector<ID> pi;
    complement(st.ev, init, pi);
    cons_clauses.push_back(pi);

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
      st.cubes.push_back(CubeSet());
  }

  void prepareCons(State & st, int k, vector<ID> & assumps) {
    if(k == INT_MAX)
      k = st.cubes.size();
    else
      assumps.push_back(levelVar(st, k));                            // enable >= k
    // Not needed, and in the way of lconsecution.
    //ARB 2/23/13 assumps.push_back(st.ev.apply(Expr::Not, levelVar(st, k-1)));  // disable < k
    assumps.push_back(st.ev.apply(Expr::Not, levelVar(st, -1)));   // disable error
  }

  void prepareError(State & st, int k, vector<ID> & assumps) {
    assert (k > 0);
    assumps.push_back(levelVar(st, k));                            // enable >= k
    assumps.push_back(st.ev.apply(Expr::Not, levelVar(st, k-1)));  // disable < k
    assumps.push_back(levelVar(st, -1));                           // enable error
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
    COI::range latchRange = st.ss.coi.cCOI();
    for (vector<ID>::const_iterator it = latchRange.first; it != latchRange.second; ++it) {
      asgn.insert(SAT::Assignment::value_type(*it, SAT::Unknown));
      asgn.insert(SAT::Assignment::value_type(st.ev.unprime(*it), SAT::Unknown));
    }
  }

  void prepareAssign(State & st, SAT::Assignment & asgn, int dlvl = -1,
                     bool inputs = false, bool primedLatches = false,
                     bool primedInputs = false, bool internal = false) {
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
    // Ugly.
    //vector<ID> latchv(st.ss.nrvars.begin(), st.ss.nrvars.end());
    COI::range latchRange =
      st.ss.reverse || dlvl < 0 || st.ss.opts.cycle
      ? st.ss.coi.cCOI(internal)
      : st.ss.coi.kCOI(dlvl + st.ss.TESteps, internal);
    for (vector<ID>::const_iterator it = latchRange.first; it != latchRange.second; ++it) {
      asgn.insert(SAT::Assignment::value_type(*it, SAT::Unknown));
      if(primedLatches) {
        asgn.insert(SAT::Assignment::value_type(st.ev.prime(*it), SAT::Unknown));
      }
    }
  }

  void preparePrimedAssign(State & st, SAT::Assignment & asgn, int dlvl = -1, bool internal=false) {
    COI::range latchRange = 
      dlvl >= 0 && !st.ss.opts.cycle 
      ? st.ss.coi.kCOI(dlvl + st.ss.TESteps, internal) 
      : st.ss.coi.cCOI(internal);
    for (vector<ID>::const_iterator it = latchRange.first; it != latchRange.second; ++it)
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
          assert(eat->isStateVar(it->first));
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

  void assignOf(Expr::Manager::View & ev, SAT::Assignment & asgn, vector<ID> & cube) {
    for (SAT::Assignment::const_iterator it = asgn.begin(); it != asgn.end(); ++it) {
      if (it->second != SAT::Unknown)
        cube.push_back(it->second == SAT::False ? 
                       ev.apply(Expr::Not, it->first) : 
                       it->first);
     }
  }


  void assignOf(State & st, SAT::Assignment & asgn, vector<ID> & cube) {
    assignOf(st.ev, asgn, cube);
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

    if(k != INT_MAX) {
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
    else 
      st.ss.stats.repeats++;
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
    st.cons = sst.cons->newView(st.ev, st.ss.opts.backend);
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
                   bool full_init = false, SAT::Assignment * lifted = NULL,
                   SAT::GID * incremental = NULL) 
  {
    if (st.ss.opts.timeout > 0) {
      int64_t sofar = Util::get_user_cpu_time() - st.ss.stime;
      if (sofar / 1000000 >= st.ss.opts.timeout) {
        if (st.m.verbosity() > Options::Terse)
          cout << "IC3" << (st.ss.reverse ? "r" : "") << ": timeout" << endl;
        throw Timeout("IC3 timeout");
      }
    }

    vector<ID> cls, assumps, cassumps;

    SAT::GID tgid = SAT::NULL_GID;
    SAT::Manager::View * cons;
    if (k == 0 && st.icons) {
      cons = st.icons;
      for (vector<ID>::iterator it = cube.begin(); it != cube.end(); it++) {
        assumps.push_back(st.ev.prime(*it));
        cassumps.push_back(st.ev.prime(*it));
      }
      // clean up previous calls
      if (incremental && *incremental != SAT::NULL_GID)
        st.cons->remove(*incremental);
    }
    else {
      cons = st.cons;
      if (!incremental || *incremental == SAT::NULL_GID) {
        prepareCons(st, k, assumps);
        tgid = cons->newGID();
        try {
          complement(st.ev, cube, cls);
          cons->add(cls, tgid);
        }
        catch (SAT::Trivial tr) {
          assert (!tr.value());
          cons->remove(tgid);
          return true;
        }
        for (vector<ID>::iterator it = cube.begin(); it != cube.end(); it++) {
          assumps.push_back(st.ev.prime(*it));
          cassumps.push_back(st.ev.prime(*it));
        }
        if (incremental)
          *incremental = tgid;
      }
      else {
        tgid = *incremental;
        assumps.push_back(levelVar(st, k));
        for (vector<ID>::iterator it = cube.begin(); it != cube.end(); it++)
          cassumps.push_back(st.ev.prime(*it));
      }
    }

    bool rv = cons->sat(&assumps, asgn, rcore ? &cassumps : NULL, tgid, 
                        full_init, lifted);
    if (tgid != SAT::NULL_GID && (!rv || !incremental))
      cons->remove(tgid);

    if (rv)
      return false;
    else {
      if (rcore) {
        vector<ID> copy(cube);
        // reduce the cube by the unsat core  
        cube.clear();
        sort(cassumps.begin(), cassumps.end());
        for (vector<ID>::iterator it = copy.begin(); it != copy.end(); it++)
          if (binary_search(cassumps.begin(), cassumps.end(), 
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

  bool join(State & st, const set<ID> & keep, vector<ID> & cube,
            const SAT::Assignment & asgn) 
  {
    vector<ID> rcube;
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
    return true;
  }

  void mic(State & st, int k, vector<ID> & cube, bool complete = false, bool ctg = false);

  bool down(State & st, int k, const set<ID> & keep, vector<ID> & cube,
            vector<ID> * full = NULL, bool handleCtgs = false, int numJoins = -1) {
    if (numJoins < 0) //a complete down query
      ++st.ss.stats.numDownCalls;
    SAT::Assignment asgn;
    //TODO: could use the distance from the frontier instead of -1
    if (handleCtgs)
      prepareAssign(st, asgn, -1); 
    else {
      for (vector<ID>::iterator it = cube.begin(); it != cube.end(); it++)
        asgn.insert(SAT::Assignment::value_type(var(st, *it), SAT::Unknown));
    }
    int joined = 0;
    int ctgAttempts = 0;
    bool ctged = false; //only used for statistical purposes
    while (true) {
      if (!initiation(st, cube))
        return false;
      if (full) *full = cube;
      if (!consecution(st, k, cube, &asgn)) {
        if (k > 0 && handleCtgs && ctgAttempts < st.opts.ctgs) {
          if (!ctged) {
            ++st.ss.stats.numDownWithCtg;
            ctged = true;
          }
          ++ctgAttempts;
          vector<ID> ctg;
          assignOf(st, asgn, ctg);
          if (initiation(st, ctg) && consecution(st, k-1, ctg)) {
            set<ID> dummy;
            int l = k;
            for (; l <= st.ss.stats.level; ++l) {
              vector<ID> ccube(ctg);
              if (down(st, l, dummy, ccube))
                ctg = ccube;
              else
                break;
            }
            mic(st, l-1, ctg, false, true);
            ++st.ss.stats.numClauses.back();
            addCube(st, l, ctg);
            continue;
          }
        }
        if (numJoins >= 0 && joined >= numJoins)
          return false;
        ctgAttempts = 0;
        ++joined;
        if (joined == 1)
          ++st.ss.stats.numDownWithJoin;
        if (!join(st, keep, cube, asgn))
          return false;
      }
      else {
        if (numJoins < 0)
          ++st.ss.stats.numSuccDown;
        if (joined)
          ++st.ss.stats.numSuccDownWithJoin;
        if (ctged)
          ++st.ss.stats.numSuccDownWithCtg;
        return true;
      }
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

  void mic(State & st, int k, vector<ID> & cube, bool complete, bool ctg) {
    if (!ctg)
      ++st.ss.stats.numMicCalls;
    set<ID> keep;
    //if (st.ss.opts.abstract == 3) reduceCube(st, cube); // TODO: WHY CAN'T I DO THIS?
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
      for (; i < cube.size() && cnt >= 0; ++i) {
        if(keep.find(cube[i]) != keep.end())
          continue;
        vector<ID> dcube(cube.size()-1);
        for (unsigned int j = 0, l = 0; j < cube.size(); ++j)
          if (j != i)
            dcube[l++] = cube[j];
        if (down(st, k, keep, dcube, NULL, st.opts.ctgs && !ctg, ctg ? 0 : -1)) {
          cube = dcube;
          break;
        }
        if (!ctg)
          keep.insert(cube[i]);
        --cnt;
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

  int std_generalize(State & st, int lo, int hi, vector<ID> & cube, bool pursue) {
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
        if(st.icons && st.opts.bmcsz)
          prepareAssignSpecial(st, asgn);
        else
          prepareAssign(st, asgn, -1, true);
      }
      while (_lo <= _hi) {
        resetAssignment(asgn);
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
          if(st.icons && st.opts.bmcsz) {
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
      //if (down(st, k+1, dummy, ccube, NULL, st.opts.ctgs))
      if (down(st, k+1, dummy, ccube))
        cube = ccube;
      else
        break;
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

    // definitely inductive
    ++st.ss.stats.clauseSizeBef += cube.size();
    int64_t start = Util::get_user_cpu_time();
    mic(st, k, cube);
    st.ss.stats.micTime += (Util::get_user_cpu_time() - start);
    ++st.ss.stats.clauseSizeAft += cube.size();
    addCube(st, k+1, cube);
    return k+1;
  }

  int lconsecution(State & st, int lo, int hi, vector<ID> & cube, 
                   vector<SAT::Assignment> & asgns, int offset = 0)
  {
    SAT::GID gid = SAT::NULL_GID;
    vector<ID> copy(cube);
    int k = hi;
    for (; k >= lo; --k) {
      if (offset+hi-k >= static_cast<int>(asgns.size())) {
        asgns.push_back(SAT::Assignment());
        assert (offset+hi-k < static_cast<int>(asgns.size()));
        prepareAssign(st, asgns[offset+hi-k]);
      }
      else
        resetAssignment(asgns[offset+hi-k]);
      if (consecution(st, k, copy, &asgns[offset+hi-k], true, false, NULL, &gid)) {
        cube = copy;
        break;
      }
    }
    if (k < lo && gid != SAT::NULL_GID && (k > 0 || !st.icons))
      st.cons->remove(gid);
    return k;
  }

  int new_generalize(State & st, int lo, int hi, vector<ID> & cube, bool pursue) 
  {
    vector<SAT::Assignment> asgns;
    int k = lconsecution(st, lo, hi, cube, asgns);
    if (k < lo) return 0;

    // use down to push forward as far as possible
    set<ID> dummy;
    for (; k < hi; ++k) {
      vector<ID> ccube(cube);
      join(st, dummy, ccube, asgns[hi-(k+1)]);
      if (!down(st, k+1, dummy, ccube))
        break;
      cube = ccube;
    }

    ++st.ss.stats.numClauses.back();

    // definitely inductive
    ++st.ss.stats.clauseSizeBef += cube.size();
    int64_t start = Util::get_user_cpu_time();
    mic(st, k, cube);
    st.ss.stats.micTime += (Util::get_user_cpu_time() - start);
    ++st.ss.stats.clauseSizeAft += cube.size();
    addCube(st, k+1, cube);
    return k+1;    
  }

  int pri_generalize(State & st, int lo, int hi, vector<ID> & cube, bool pursue) 
  {
    vector<SAT::Assignment> asgns;
    vector<ID> core(cube);
    set<ID> dummy;
    bool first = true;
    int k = lo;
    while (k < hi) {
      k = lconsecution(st, lo, hi, core, asgns);
      if (k < lo) {
        if (first) {
          assert (lo == 0);
          return 0;
        }
        cube = core;
        break;
      }
      else if (k == hi) {
        cube = core;
        break;
      }
      first = false;
      vector<ID> copy(cube), full;
      for (int j = k+1; j <= hi; ++j) {
        join(st, dummy, copy, asgns[hi-j]);
        if (copy.size() == cube.size())
          break;
        // guaranteed to get here when j == k+1
        if (!down(st, j, dummy, copy, &full)) {
          cube = core;
          goto DONE;
        }
        ++k;
        lo = k+1;
        cube = full;
        core = copy;
      }
    }
  DONE:

    ++st.ss.stats.numClauses.back();

    // definitely inductive
    ++st.ss.stats.clauseSizeBef += cube.size();
    int64_t start = Util::get_user_cpu_time();
    mic(st, k, cube);
    st.ss.stats.micTime += (Util::get_user_cpu_time() - start);
    ++st.ss.stats.clauseSizeAft += cube.size();
    addCube(st, k+1, cube);
    return k+1;    
  }

  int rch_generalize(State & st, int lo, int hi, vector<ID> & cube, bool pursue) {

    int k = lo;

    if (!st.opts.pushLast) {
      // use down to push forward as far as possible
      set<ID> dummy;
      for (; k < hi; ++k) {
        vector<ID> ccube(cube);
        //if (down(st, k+1, dummy, ccube, NULL, st.opts.ctgs))
        if (down(st, k+1, dummy, ccube))
          cube = ccube;
        else
          break;
      }
    }

    ++st.ss.stats.numClauses.back();
    ++st.ss.stats.clauseSizeBef += cube.size();
    int64_t start = Util::get_user_cpu_time();
    mic(st, k, cube);
    st.ss.stats.micTime += (Util::get_user_cpu_time() - start);

    if (st.opts.pushLast) {
      // use down to push forward as far as possible
      set<ID> dummy;
      for (; k < hi; ++k) {
        vector<ID> ccube(cube);
        //if (down(st, k+1, dummy, ccube, NULL, st.opts.ctgs))
        if (down(st, k+1, dummy, ccube))
          cube = ccube;
        else
          break;
      }
    }
    ++st.ss.stats.clauseSizeAft += cube.size();

    // definitely inductive
    addCube(st, k+1, cube);
    return k+1;
  }


  int generalize(State & st, int lo, int hi, vector<ID> & cube, bool pursue) 
  {
    if (!pursue && st.opts.gen != 3) {
      // if it's inductive at lo+1, this cube has probably already been
      // taken care of
      vector<ID> assumps(cube);
      prepareCons(st, lo+1, assumps);
      if (!st.cons->sat(&assumps))
        return INT_MAX;
      // inductive relative only to lo
      hi = lo;
    }

    assert(st.opts.gen != 3 || lo >= 0);
    lo = max(0, lo);
    if (lo == 0 && !initiation(st, cube))
      return 0;

    switch (st.opts.gen) {
    case 0:
      return std_generalize(st, lo, hi, cube, pursue);
    case 1:
      return new_generalize(st, lo, hi, cube, pursue);
    case 2:
      return pri_generalize(st, lo, hi, cube, pursue);
    case 3:
      return rch_generalize(st, lo, hi, cube, pursue);
    default:
      assert(false);
    }
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

      if (!st.ss.ev)
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

      if (!st.ss.ev)
        st.ev.end_local();
    }

    if (st.m.verbosity() > Options::Informative && parts.size() > 0) {
      cout << "Parts at " << k+1 << " (" << parts.size() << "):";
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
    COI::range latchRange = st.ss.coi.cCOI();
    set<ID> allpart(latchRange.first, latchRange.second);
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
    assumps.push_back(st.ev.apply(Expr::Not, st.ss.actNegTp));
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

  void liftPropCti(State & st, int k, vector<ID> & cube, vector<ID> & inputs, vector<ID> & nsInputs) {
    //liftAdd(st, cube, false);

    int64_t start = Util::get_user_cpu_time();
    unsatCoreLift(st, k, cube, inputs, nsInputs);
    st.ss.stats.ibmLiftTime += (Util::get_user_cpu_time() - start);
    st.ss.stats.cubeSizeIBM += cube.size();
    //liftAdd(st, cube, false);

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

  void propagateClauses(State & st, int k, bool trivial, bool shortCircuit, 
                        bool possible = true) {

    if (st.m.verbosity() > Options::Informative) cout << "propagateClauses " << endl;

    st.ss.stats.percentProp.push_back(0.0);

    st.ss.stats.clauseDistBef.push_back(vector<uint64_t>());

    for(int i = 1; i <= k+1; ++i) {
      st.ss.stats.clauseDistBef.back().push_back(st.cubes[i].size());
    }
    
    //Reduce infCubes
    bool reduced = true;
    while (reduced) {
      reduced = false;
      CubeSet newInfCubes;
      for (CubeSet::iterator it = st.infCubes.begin(); it != st.infCubes.end();
           ++it) {
        vector<ID> cube(*it);
        bool ind = consecution(st, INT_MAX, cube);
        assert(ind);
        if (cube.size() < it->size()) {
          addCubeToManager(st, INT_MAX, cube, true);
          reduced = true;
        }
        sort(cube.begin(), cube.end());
        newInfCubes.insert(cube);
      }
      st.infCubes = newInfCubes;
    }

    SubsumptionUniverse su;
    if (!trivial) {
      for (int i = 1; i <= k+1; ++i)
        su.add(st.cubes[i], i);
      if(st.opts.inf || st.opts.inf_weak)
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
      if (st.m.verbosity() > Options::Informative)
        cout << i << " " << icubes.size() << " " << next.size() << endl;
      st.ss.stats.percentProp.back() += (numProp / (double) total);
      if (icubes.empty() && possible) {
        if (shortCircuit && !st.ss.opts.incremental) {
          throw Safe();
        }
        if (st.opts.abstract == 3 && st.cubes.size() > static_cast<unsigned int>(k+2))
          k++;
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
        vector<ID> cp(*it);
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


    if(st.opts.inf || st.opts.inf_weak || st.opts.inf_vweak) {
      int promoted = 0;
      CubeSet & kcubes = st.cubes.back();
      for (CubeSet::iterator it = kcubes.begin(); it != kcubes.end();) {
        vector<ID> cube = *it;
        if (consecution(st, INT_MAX, cube)) {
          ++promoted;
          CubeSet::iterator tmp = it;
          it++;
          kcubes.erase(tmp);
          sort(cube.begin(), cube.end());
          st.infCubes.insert(cube);
        }
        else
          it++;
      }
      //cout << "Promoted " << promoted << " clauses to F_inf" << endl;
    }

    if(st.opts.inf || st.opts.inf_weak || st.opts.inf_vweak) {
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
    vector< vector<ID> > cons_clauses = cnfat->getPlainCNF();
    st.m.constRelease(cnfat);
    if(st.ss.opts.constraints) {
      for (unsigned i = 0; i < st.ss.opts.constraints->size(); ++i)
        cons_clauses.insert(cons_clauses.end(),
                            (*st.ss.opts.constraints)[i].begin(),
                            (*st.ss.opts.constraints)[i].end());
    }

    if(st.ss.reverse) {
      ExprAttachment const * eat = (ExprAttachment *) st.m.constAttachment(Key::EXPR);
      vector<ID> latches(eat->stateVars());
 
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
      st.m.constRelease(eat);
    }


    sst.cons->add(cons_clauses);
    st.cons = sst.cons->newView(st.ev, st.ss.opts.backend);

    CubeSet cubes = st.cubes[k+1];
    cubes.insert(st.infCubes.begin(), st.infCubes.end());

    if(st.opts.initCube) {
      if(st.ss.simpleInit) {
        //Need to change st.ss.initially which is used by consecution
        st.ss.initially.clear();
        st.ss.initially.insert(st.opts.initCube->begin(), st.opts.initCube->end());
      }
      else {
        assert(!st.ss.bddInit);
        delete st.icons;
        delete st.ss.icons;
        delete st.init;
        delete st.ss.init;
        SAT::Clauses init_clauses;
        for (vector<ID>::const_iterator it = st.opts.initCube->begin();
             it != st.opts.initCube->end(); ++it) {
          vector<ID> cls;
          cls.push_back(*it);
          init_clauses.push_back(cls);
        }
        SAT::Clauses icons_clauses(cons_clauses);
        icons_clauses.insert(icons_clauses.end(), init_clauses.begin(), init_clauses.end());
        ExprAttachment const * eat = (ExprAttachment *) st.m.constAttachment(Key::EXPR);
        for (vector<ID>::const_iterator it = eat->constraintFns().begin(); it != eat->constraintFns().end(); ++it)
          Expr::tseitin(st.ev, *it, init_clauses);
        st.m.constRelease(eat);

        st.ss.icons = st.m.newSATManager();
        st.icons = st.ss.icons->newView(st.ev, st.ss.opts.backend);
        st.ss.icons->add(icons_clauses);

        st.ss.init = st.m.newSATManager();
        st.init = st.ss.init->newView(st.ev, st.ss.opts.backend);
        st.ss.init->add(init_clauses);

        if(st.ss.opts.constraints)
          for (unsigned i = 0; i < st.ss.opts.constraints->size(); ++i) {
            st.ss.init->add((*st.ss.opts.constraints)[i]);
          }

      }
      //Remove clauses that are not implied by the provided initial condition
      for(CubeSet::iterator it = cubes.begin(); it != cubes.end();) {
        vector<ID> cube = *it;
        if(!initiation(st, cube))
          cubes.erase(it++);
        else
          ++it;
      }
    }

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

      sst.cons->add(cons_clauses);
      st.cons = sst.cons->newView(st.ev, st.ss.opts.backend);

      cubes = next;

      for(CubeSet::const_iterator it = cubes.begin(); it != cubes.end(); ++it)
        addCubeToManager(st, 1, *it, true);
    }
  }

  int blconsecution(State & st, int lo, int hi, vector<ID> & cube) {
    SAT::GID gid = SAT::NULL_GID;
    vector<ID> copy(cube);
    int k = hi;
    for (; k >= lo; --k) {
      if (consecution(st, k, copy, NULL, false, false, NULL, &gid)) {
        cube = copy;
        break;
      }
    }
    if (k < lo) st.cons->remove(gid);
    return k;
  }

  void liftClsCti(State & st, vector<ID> & curState, vector<ID> & inputs, const vector<ID> & target) {
    vector<ID> assumps;
    //disable P'
    assumps.push_back(st.ev.apply(Expr::Not, st.ss.actPp));
    assumps.insert(assumps.end(), curState.begin(), curState.end());
    assumps.insert(assumps.end(), inputs.begin(), inputs.end());
    vector<ID> notTargetPr;
    complement(st.ev, target, notTargetPr);
    primeFormulas(st.ev, notTargetPr);
    notTargetPr.push_back(st.ev.apply(Expr::Not, st.ss.actNegTp));
    SAT::GID gid = st.lift->newGID();
    st.lift->add(notTargetPr, gid);
    bool sat = st.lift->sat(&assumps, NULL, &assumps);
    st.lift->remove(gid);
    assert(!sat);
    curState.clear();
    ExprAttachment const * eat = (ExprAttachment *) st.m.constAttachment(Key::EXPR);
    for (vector<ID>::const_iterator it = assumps.begin(); it != assumps.end(); ++it) {
      if (eat->isStateVar(*it) || eat->isStateVar(st.ev.apply(Expr::Not, *it))) {
        curState.push_back(*it);
      }
    }
    st.m.constRelease(eat);
  }

  struct ToPush {
    ToPush(int k, int dlvl, vector<ID> cube, vector<ID> gen, int idx = 0) : 
      k(k), dlvl(dlvl), cube(cube), lastGen(gen), nodeIdx(idx)  {}
    int k;
    int dlvl;
    vector<ID> cube;
    vector<ID> lastGen;
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

  void pushGeneralization(State & st, int toK, PushSet & toPush, 
                          vector<Node> & skeleton) 
  {
    while (!toPush.empty()) {
      PushSet::iterator tp = toPush.begin();
      vector<ID> cube(tp->cube);

      SAT::Assignment asgn;
        prepareAssign(st, asgn, tp->dlvl+1,
              st.ss.opts.printCex || st.ss.opts.lift, false, false, st.ss.opts.intNodes);

      bool cons = false;
      int n;
      if (st.ss.opts.leapfrog) {
        st.ss.stats.numConsPW++;
        vector<ID> lastGen(tp->lastGen);
        n = blconsecution(st, tp->k, toK, lastGen);
        cons = n >= tp->k;
        ++n;
        if (cons) {
          st.ss.stats.numSuccPW++;
          cube = lastGen;
          addCube(st, n, cube);
        }
      }
      if (!cons) {
        cons = consecution(st, tp->k, cube, &asgn, true, true);
        if (cons) n = generalize(st, tp->k, toK, cube, false);
      }
      if (cons) {
        if (n <= toK) {
          toPush.insert(ToPush(n, tp->dlvl, tp->cube, cube, tp->nodeIdx));
        }
        else {
          unrecordLits(st, tp->cube);
        }
        toPush.erase(tp);
      }
      else {
        vector<ID> pred, inputs;
        if(st.ss.opts.printCex || st.ss.opts.lift) {
          fullAssignOf(st, asgn, pred, inputs);
          if (st.ss.opts.lift)
            liftClsCti(st, pred, inputs, cube);
        }
        else {
          assignOf(st, asgn, pred);
        }
        vector<ID> cube(pred);
        int n = 0;
        if (tp->k > 0)
          n = st.opts.gen == 3 ? tp->k - 1 : generalize(st, tp->k-2, toK, cube, true);
        if ((n == 0 && st.opts.gen != 3) || (st.opts.gen == 3 && n == -1)) {
          if (st.opts.minCex && (tp->dlvl+3 > toK + 2)) {
            if (st.m.verbosity() > Options::Informative)
              cout << "Ignoring counterexample of length " << tp->dlvl+3 << endl;
            return;
          }
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
            if(st.icons && st.opts.bmcsz) {
              init2 = st.cex.back();
              popBackTransition(st);
            }
            for(vector<Transition>::const_reverse_iterator rit = trace.rbegin();
                rit != trace.rend(); ++rit) {
              addTransitionToCexTrace(st, rit->state, rit->inputs);
            }
            //Add back initial transition(s)
            if(st.icons && st.opts.bmcsz)
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
          if(st.ss.opts.printCex)
            skeleton.push_back(Node(pred, inputs, tp->nodeIdx));
          toPush.insert(ToPush(n, tp->dlvl + 1, pred, cube, skeleton.size() - 1));
          st.ss.stats.maxDlvl.back() = max(st.ss.stats.maxDlvl.back(), tp->dlvl + 1);
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
    st.ss.stats.maxDlvl.push_back(0);

    while (true) {
      if (st.m.verbosity() > Options::Verbose) cout << "strengthen" << endl;
      vector<ID> assumps;
      prepareError(st, k, assumps);
      SAT::Assignment asgn;
      prepareAssign(st, asgn, 1, st.ss.opts.printCex || st.ss.opts.lift,
                    false, st.ss.opts.lift, st.ss.opts.intNodes);

      bool rv = st.cons->sat(&assumps, &asgn, NULL, SAT::NULL_GID, true);
      ++st.ss.stats.numPropQueries.back();
      if (rv) {
        vector<ID> asgnc, inputs;
        if(st.ss.opts.printCex && !st.ss.opts.lift) {
          //Separate asgn into current state, input, and next state
          vector<ID> curState;
          fullAssignOf(st, asgn, asgnc, inputs);
          addTransitionToCexTrace(st, asgnc, inputs);
        }
        else if(st.ss.opts.lift) {
          ++st.ss.stats.numLiftCubes;
          //Separate asgn into current state, input, and primed-input
          vector<ID> nsInputs;
          fullAssignWithPrimedInputsOf(st, asgn, asgnc, inputs, nsInputs);
          st.ss.stats.cubeSizeBef += asgnc.size();
          if(st.m.verbosity() > Options::Verbose)
            cout << "Before lifting: " << asgnc.size() << endl;
          //Lift asgnc
          liftPropCti(st, k, asgnc, inputs, nsInputs);
          if (st.opts.printCex)
            addTransitionToCexTrace(st, asgnc, inputs);
        }
        else {
          assignOf(st, asgn, asgnc);
        }
        first = false;
        vector<ID> cube(asgnc);
        ++st.ss.stats.numGenCalls.back();
        int n = st.opts.gen == 3 ? k - 1 : generalize(st, k-2, k, cube, true);
        st.ss.stats.levInd.back() += (n - 1);
        if (n == 0 && st.opts.gen != 3) {
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
          if(st.ss.opts.printCex)
            skeleton.push_back(Node(asgnc, inputs, -1));
          toPush.insert(ToPush(n, 1, asgnc, cube, 0));
          st.ss.stats.maxDlvl.back() = max(st.ss.stats.maxDlvl.back(), 1);
          recordLits(st, asgnc);
          pushGeneralization(st, k, toPush, skeleton);
        }
        if(st.ss.opts.printCex)
          popBackTransition(st);
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

  void _check(SharedState & sst, bool shortCircuit = true, bool renew = false) {
    State st(sst);
    if (sst.opts.reverse)
      initReverseSAT(st);
    else
      initSAT(st);
    if(sst.opts.incremental || renew) {
      renewSAT(st);
    }
    extend(st, 0);
    for (int k = 1;; ++k) {
      if (st.m.verbosity() > Options::Informative) cout << "Level " << k << endl;
      extend(st, k);
      bool trivial = strengthen(st, k);
      propagateClauses(st, k, trivial, shortCircuit);
      renewSAT(st);
    }
  }

  bool verifyProof(Model & m, vector< vector<ID> > & proof, vector<SAT::Clauses> * constraints, IC3Options & opts, vector<ID> * gprop = NULL) {
    if (!opts.verify) return true;

    if (m.verbosity() == Options::Silent) return true;

    if(m.verbosity() > Options::Informative) {
      cout << "IC3: Verifying proof" << endl;
    }
   
    SAT::Manager * propertyMgr = m.newSATManager();
    SAT::Manager * proofMgr = m.newSATManager();
    Expr::Manager::View * ev = m.newView();

    ExprAttachment const * eat = (ExprAttachment *) m.constAttachment(Key::EXPR);
    ID npi;
    if (gprop && !gprop->empty()) {
      vector<ID> cube;
      complement(*ev, *gprop, cube);
      npi = ev->apply(Expr::And, cube);
    }
    else
      npi = eat->outputFnOf(eat->outputs()[0]);
    vector<ID> init(eat->initialConditions());
    m.constRelease(eat);

    vector< vector< ID> > property;
    Expr::tseitin(*ev, ev->apply(Expr::Not, npi), property);

    CNFAttachment * cnfat = (CNFAttachment *) m.constAttachment(Key::CNF);
    vector< vector<ID> > transRel;
    if (gprop && !gprop->empty()) {
      transRel = cnfat->getPlainCNF();
      transRel.push_back(*gprop);
    }
    else
      transRel = cnfat->getCNF();
    m.constRelease(cnfat);

    vector< vector<ID> > negPropertyPrimed;
    Expr::tseitin(*ev, Expr::primeFormula(*ev, npi), negPropertyPrimed);

    ID proofID = ev->btrue();
    for(unsigned i = 0; i < proof.size(); ++i)
      proofID = ev->apply(Expr::And, ev->apply(Expr::Or, proof[i]), proofID);
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
        SAT::Manager::View* initView = initMgr->newView(*ev, opts.backend);
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

    SAT::Manager::View* propertyView = propertyMgr->newView(*ev, opts.backend);
    try {
      propertyMgr->add(transRel);
      propertyMgr->add(ccls);
      propertyMgr->add(proof);
      propertyMgr->add(negPropertyPrimed);
      prop_sat = propertyView->sat();
    }
    catch (SAT::Trivial tr) {
      assert (!tr.value());
      prop_sat = false;
    }
    delete propertyView;

    SAT::Manager::View* proofView = proofMgr->newView(*ev, opts.backend);
    try {
      proofMgr->add(transRel);
      proofMgr->add(ccls);
      proofMgr->add(proof);
      proofMgr->add(negProofPrimed);
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

  void minimalCore(SAT::Manager::View * sv, const vector<ID> & assumps, 
                   vector<ID> core) 
  {
    for (unsigned int j = 0; j < core.size();) {
      vector<ID> ccore;
      if (j > 0) 
        ccore.insert(ccore.end(), core.begin(), core.begin()+j-1);
      if (j < core.size()-1) 
        ccore.insert(ccore.end(), core.begin()+j+1, core.end());
      vector<ID> _assumps(assumps);
      _assumps.insert(_assumps.end(), ccore.begin(), ccore.end());
      if (!sv->sat(&_assumps, NULL, &ccore))
        core = ccore;
      else
        ++j;
    }
  }

  AbsPattern * pattern(SharedState & sst) {
    if (sst.opts.abs_patterns.empty())
      sst.opts.abs_patternMap.clear();
    if (sst.opts.abs_pattern == 0)
      return NULL;
    int patid = sst.opts.abs_pattern;
    if (sst.opts.abs_patternMap.find(patid) == sst.opts.abs_patternMap.end()) {
      sst.opts.abs_patterns.push_back(AbsPattern());
      sst.opts.abs_patternMap.insert(
        PatternMap::value_type(patid, sst.opts.abs_patterns.size()-1));
    }
    int patidx = sst.opts.abs_patternMap[patid];
    return &sst.opts.abs_patterns[patidx];
  }

  void updatePattern(SharedState & sst, const set<ID> & concrete) {
    AbsPattern * pat = pattern(sst);
    if (!pat) return;
    set<ID> curr, next;
    for (vector< set<ID> >::const_iterator i = pat->concrete.begin();
         i != pat->concrete.end(); ++i)
      curr.insert(i->begin(), i->end());
    set_difference(concrete.begin(), concrete.end(),
                   curr.begin(), curr.end(),
                   inserter(next, next.end()));
    if (!next.empty()) {
      pat->cnt++;
      pat->concrete.push_back(next);
    }
  }

  void oaCheck(SharedState & sst, bool shortCircuit) {
    sst.stime = Util::get_user_cpu_time();

    sst.opts.printCex = true;
    bool optsprop = sst.opts.propagate;
    sst.opts.propagate = false;

    Expr::Manager::View * ev = sst.m.newView();
    ev->begin_local();
    sst.ev = ev;

    ExprAttachment const * eat = (ExprAttachment *) sst.m.constAttachment(Key::EXPR);
    vector<ID> inputs(eat->inputs());
    ID npi = eat->outputFnOf(eat->outputs())[0];
    vector<ID> init(eat->initialConditions());
    vector<ID> constraints = eat->constraintFns();
    vector<ID> latches = eat->stateVars();
    vector<ID> fns = eat->nextStateFnOf(latches);
    sst.m.constRelease(eat);

    // obtain initial set of concrete states
    set<ID> concrete, si(inputs.begin(), inputs.end()), vs;
    AbsPattern * pat = pattern(sst);
    if (pat) {
      unsigned int sz = 0;
      for (vector< set<ID> >::const_iterator i = pat->concrete.begin();
           i != pat->concrete.end(); ++i)
        sz += i->size();
      if(sst.m.verbosity() > Options::Informative)
        cout << "Abstract: pattern " << sst.opts.abs_pattern
             << " " << pat->concrete.size() << " " << sz << endl;
    }
    if (pat && !pat->resume.empty()) {
      // from an interrupted run
      concrete.insert(pat->resume.begin(), pat->resume.end());
    }
    else if (pat && !pat->concrete.empty()) {
      // from the pattern dictionary
      if (sst.opts.abs_prunehi >= 0
          && pat->cnt < sst.opts.abs_prunehi 
          && (int) pat->concrete.size() > sst.opts.abs_prunelo)
        pat->concrete.erase(pat->concrete.begin());
      for (vector< set<ID> >::const_iterator i = pat->concrete.begin();
           i != pat->concrete.end(); ++i)
        if (!i->empty())
          concrete.insert(i->begin(), i->end());
    }
    else {
      // new pattern, so form a fresh initial set
      if (!sst.opts.iictl)
        Expr::variables(*ev, npi, vs);
      set_difference(vs.begin(), vs.end(), si.begin(), si.end(), 
                     inserter(concrete, concrete.end()));
      for (unsigned int i = 0; i < latches.size(); ++i)
        if (fns[i] == ev->btrue() || fns[i] == ev->bfalse())
          concrete.insert(latches[i]);
      if (concrete.size() == latches.size()) {
        concrete.clear();
        for (unsigned int i = 0; i < latches.size(); ++i)
          if (fns[i] == ev->btrue() || fns[i] == ev->bfalse())
            concrete.insert(latches[i]);
      }
    }

    // construct the full TR; activation literals control latch concretization
    Expr::IDMap act2latch;
    vector<ID> tr, acts;
    for (unsigned int i = 0; i < latches.size(); ++i) {
      if (concrete.find(latches[i]) == concrete.end()) {
        ostringstream buf;
        buf << "ic3_act:" << i;
        ID act = ev->newVar(buf.str());
        acts.push_back(act);
        act2latch.insert(Expr::IDMap::value_type(act, latches[i]));
        tr.push_back(ev->apply(Expr::Or, 
                               ev->apply(Expr::Not, act), 
                               ev->apply(Expr::Equiv, ev->prime(latches[i]), fns[i])));
      }
      else
        tr.push_back(ev->apply(Expr::Equiv, ev->prime(latches[i]), fns[i]));
    }
    set<ID> sacts;
    for (vector<ID>::const_iterator i = acts.begin(); i != acts.end(); ++i)
      sacts.insert(ev->apply(Expr::Not, *i));
    SAT::Clauses cnf, _fulltr;
    for(vector<ID>::const_iterator it = constraints.begin();
        it != constraints.end(); ++it)
      if(*it != ev->btrue()) { //Ignore trivial constraints
        vector<ID> lits;
        if (Expr::isClause(*ev, *it, &lits)) {
          cnf.push_back(lits);
          for (vector<ID>::iterator it = lits.begin(); it != lits.end(); ++it)
            *it = ev->prime(*it);
          cnf.push_back(lits);
        }
        else {
          tr.push_back(*it);
          tr.push_back(Expr::primeFormula(*ev, *it));
        }
      }
    Expr::tseitin(*ev, tr, cnf);
    vector<ID> extinputs(inputs);
    extinputs.insert(extinputs.end(), acts.begin(), acts.end());
    CNF::simplify(sst.m, cnf, _fulltr, extinputs, latches, fns, true, ev);
    if (sst.opts.constraints)
      for (unsigned i = 0; i < sst.opts.constraints->size(); ++i)
        _fulltr.insert(_fulltr.end(), 
                       (*sst.opts.constraints)[i].begin(),
                       (*sst.opts.constraints)[i].end());
    // _fulltr is the plain TR, fulltr has the property as well
    SAT::Clauses fulltr = _fulltr;
    if (!sst.opts.iictl)
      Expr::tseitin(*ev, ev->apply(Expr::Not, npi), fulltr);

    SAT::Clauses initClss;
    // add initial condition (cube)
    for (vector<ID>::const_iterator it = init.begin(); it != init.end(); ++it) {
      vector<ID> cls;
      cls.push_back(*it);
      initClss.push_back(cls);
    }
    if (sst.opts.bmcsz) {
      // step back one timestep
      initClss.insert(initClss.end(), _fulltr.begin(), _fulltr.end());
      for (vector< vector<ID> >::iterator it = initClss.begin(); 
           it != initClss.end(); ++it)
        for (vector<ID>::iterator l = it->begin(); l != it->end(); ++l)
          if (sacts.find(*l) == sacts.end())
            *l = Expr::primeFormula(*ev, *l, -1);
    }

    // target
    SAT::Clauses err;
    if (!sst.opts.iictl)
      Expr::tseitin(*ev, npi, err);
    else
      err = *(sst.opts.iictl_clauses);
    sst.abs_er = npi; // may be ignored (IICTL)

    vector<ID> remActs(acts);
    int longestCex = 0;
    while (true) {
      if(sst.m.verbosity() > Options::Informative)
        cout << "Abstract: concrete: " << concrete.size() << endl;

      // construct abstract TR
      vector<ID> tr, sfns(fns), sinputs(inputs);
      for (unsigned int i = 0; i < latches.size(); ++i) {
        ID f = fns[i];
        if (concrete.find(latches[i]) == concrete.end()) {
          ostringstream buf;
          buf << "ic3_abs:" << i;
          f = ev->newVar(buf.str());
          sfns[i] = f;
          sinputs.push_back(f);
        }
        tr.push_back(ev->apply(Expr::Equiv, ev->prime(latches[i]), f));
      }
      SAT::Clauses cnf;
      for(vector<ID>::const_iterator it = constraints.begin();
          it != constraints.end(); ++it)
        if(*it != ev->btrue()) { //Ignore trivial constraints
          vector<ID> lits;
          if (Expr::isClause(*ev, *it, &lits)) {
            cnf.push_back(lits);
            for (vector<ID>::iterator it = lits.begin(); it != lits.end(); ++it)
              *it = ev->prime(*it);
            cnf.push_back(lits);
          }
          else {
            tr.push_back(*it);
            tr.push_back(Expr::primeFormula(*ev, *it));
          }
        }
      sst.abs_tr.clear();
      sst.abs_ptr.clear();
      if (sst.opts.bmcsz) {
        // make both a plain TR and one with the property
        Expr::tseitin(*ev, tr, cnf);
        CNF::simplify(sst.m, cnf, sst.abs_ptr, sinputs, latches, sfns, true, ev);
        sst.abs_tr = sst.abs_ptr;
        if (!sst.opts.iictl)
          Expr::tseitin(*ev, ev->apply(Expr::Not, npi), sst.abs_tr);
      }
      else {
        // just one with the property
        if (!sst.opts.iictl)
          tr.push_back(ev->apply(Expr::Not, npi));
        Expr::tseitin(*ev, tr, cnf);
        CNF::simplify(sst.m, cnf, sst.abs_tr, sinputs, latches, sfns, true, ev);
      }

      if(sst.m.verbosity() > Options::Informative)
        cout << "Abstraction: TR size: " << sst.abs_tr.size() << endl;

      bool ic3 = false;
      try {
        if (sst.opts.timeout > 0) {
          int64_t sofar = Util::get_user_cpu_time() - sst.stime;
          if (sofar / 1000000 >= sst.opts.timeout) {
            if (sst.m.verbosity() > Options::Terse)
              cout << "IC3: timeout" << endl;
            throw Timeout("IC3 timeout");
          }
        }

        if (longestCex <= sst.opts.abs_bmc 
            && sst.opts.abs_bmctimeout <= Util::get_user_cpu_time() - sst.stime) {
          MC::AlternateModel am;
          am.init = init;
          am.inputs = sinputs;
          am.latches = latches;
          am.fns = sfns;
          am.tr = sst.abs_tr;
          am.err = npi; // may be ignored (IICTL)
          if (sst.opts.bmcsz) am.ptr = sst.abs_ptr;
          BMC::BMCOptions bopts;
          if (sst.opts.iictl) {
            bopts.iictl = sst.opts.iictl;
            bopts.iictl_clauses = sst.opts.iictl_clauses;
          }
          // if bmcsz (from FAIR), don't look for 0-step cex
          bopts.lo = max(sst.opts.bmcsz ? 1 : 0, longestCex-1);
          size_t k = sst.opts.abs_bmc;
          bopts.bound = &k;
          bopts.printCex = true;
          bopts.am = &am;
          bopts.timeout = sst.opts.abs_bmctimeout;
          bopts.useCOI = false;  // WHY?
          bopts.constraints = sst.opts.constraints;
          bopts.ev = ev;
          vector<Transition> cexTrace;
          MC::ReturnValue rv = BMC::check(sst.m, bopts, &cexTrace);
          if (rv.returnType == MC::CEX) {
            longestCex = cexTrace.size();
            vector<Transition> rev;
            for (vector<Transition>::const_reverse_iterator i = cexTrace.rbegin();
                 i != cexTrace.rend(); ++i)
              rev.push_back(*i);
            throw CEX(rev);
          }
          else 
            longestCex = sst.opts.abs_bmc+1;
        }
        ic3 = true;
        randomVars(sst, *ev, latches, sfns);
        _check(sst, false, true);
        assert (false);
      }
      catch (CEX cex) {
        // try to concretize
        SAT::Clauses _fulltr(fulltr);
        SAT::Manager * consMgr = sst.m.newSATManager();
        SAT::Manager::View * cons = consMgr->newView(*ev, sst.opts.backend);
        cons->timeout(sst.opts.timeout);

        if(sst.m.verbosity() > Options::Informative)
          cout << "Abstract: cex length: " << cex.cexTrace.size() << endl;
        // if bmcsz && ic3: need the 0-step vector; otherwise, already
        // covered by initClss above
        int j = sst.opts.bmcsz && ic3 && cex.cexTrace.size() == 2 ? 0 : 1;
        int k = sst.opts.bmcsz ? 0 : 1;
        SAT::Assignment asgn;
        if (sst.opts.bmcsz) {
          for (vector<ID>::const_iterator j = latches.begin(); j != latches.end(); ++j)
            asgn.insert(SAT::Assignment::value_type(ev->prime(*j, -1), SAT::Unknown));
          for (vector<ID>::const_iterator j = inputs.begin(); j != inputs.end(); ++j)
            asgn.insert(SAT::Assignment::value_type(ev->prime(*j, -1), SAT::Unknown));
        }
        if (k > 0) {
          for (vector<ID>::const_iterator j = latches.begin(); j != latches.end(); ++j)
            asgn.insert(SAT::Assignment::value_type(*j, SAT::Unknown));
          for (vector<ID>::const_iterator j = inputs.begin(); j != inputs.end(); ++j)
            asgn.insert(SAT::Assignment::value_type(*j, SAT::Unknown));
        }
        cons->add(initClss);
        vector<ID> assumps;
        for (vector<Transition>::const_reverse_iterator i = cex.cexTrace.rbegin()+j;
             i != cex.cexTrace.rend(); ++i, ++k) {
          if (i+1 == cex.cexTrace.rend()) {
            SAT::Clauses _err(err);
            for (SAT::Clauses::iterator j = _err.begin(); j != _err.end(); ++j)
              for (vector<ID>::iterator jj = j->begin(); jj != j->end(); ++jj)
                if (*jj != ev->btrue() && *jj != ev->bfalse())
                  *jj = Expr::primeFormula(*ev, *jj, k);
            cons->add(_err);
          }
          else {
            for (vector<ID>::const_iterator j = i->state.begin();
                 j != i->state.end(); ++j) {
              ID v = *j;
              if (ev->op(v) == Expr::Not) v = ev->apply(Expr::Not, v);
              if (concrete.find(v) != concrete.end())
                assumps.push_back(ev->prime(*j, k));
            }
          }
          for (vector<ID>::const_iterator j = latches.begin(); j != latches.end(); ++j)
            asgn.insert(SAT::Assignment::value_type(ev->prime(*j, k), SAT::Unknown));
          for (vector<ID>::const_iterator j = inputs.begin(); j != inputs.end(); ++j)
            asgn.insert(SAT::Assignment::value_type(ev->prime(*j, k), SAT::Unknown));
          if (k > 0) {
            cons->add(_fulltr);
            for (SAT::Clauses::iterator j = _fulltr.begin(); j != _fulltr.end(); ++j) {
              for (vector<ID>::iterator l = j->begin(); l != j->end(); ++l)
                if (sacts.find(*l) == sacts.end())
                  *l = Expr::primeFormula(*ev, *l);  // for next iteration
            }
          }
        }

        vector<ID> _assumps(assumps), core(remActs);
        _assumps.insert(_assumps.end(), acts.begin(), acts.end());
        // can it be concretized?
        if (cons->sat(&_assumps, &asgn, &core)) {
          --k; // last level
          vector<Transition> ct(k + (sst.opts.bmcsz ? 2 : 1));
          set<ID> sinputs(inputs.begin(), inputs.end());
          for (SAT::Assignment::const_iterator i = asgn.begin(); 
               i != asgn.end(); ++i) {
            int numPrimes = ev->nprimes(i->first);
            ID id = ev->unprime(i->first, numPrimes);
            ID v = i->second == SAT::True ? id : ev->apply(Expr::Not, id);
            if(sinputs.find(id) != sinputs.end())
              ct[k-numPrimes].inputs.push_back(v);
            else
              ct[k-numPrimes].state.push_back(v);
          }
          cex.cexTrace = ct;

          delete cons;
          delete consMgr;

          if (acts.size() > remActs.size() && (sst.opts.iictl || sst.opts.fair)) {
            if (!ic3) { // BMC
              // extract core acts from cex.cexTrace.size()-1 unrolling
              int j = 1;
              int k = sst.opts.bmcsz ? 0 : 1;
              SAT::Clauses _fulltr(fulltr);
              SAT::Manager * consMgr = sst.m.newSATManager();
              SAT::Manager::View * cons = consMgr->newView(*ev, sst.opts.backend);
              cons->timeout(sst.opts.timeout);
              cons->add(initClss);
              for (vector<Transition>::const_reverse_iterator 
                     i = cex.cexTrace.rbegin()+j;
                   i+1 != cex.cexTrace.rend(); ++i, ++k) {
                if (i+2 == cex.cexTrace.rend()) {
                  SAT::Clauses _err(err);
                  for (SAT::Clauses::iterator j = _err.begin(); j != _err.end(); ++j)
                    for (vector<ID>::iterator jj = j->begin(); jj != j->end(); ++jj)
                      if (*jj != ev->btrue() && *jj != ev->bfalse())
                        *jj = Expr::primeFormula(*ev, *jj, k);
                  cons->add(_err);
                }
                if (k > 0) {
                  cons->add(_fulltr);
                  for (SAT::Clauses::iterator j = _fulltr.begin(); 
                       j != _fulltr.end(); ++j) {
                    for (vector<ID>::iterator l = j->begin(); l != j->end(); ++l)
                      if (sacts.find(*l) == sacts.end())
                      *l = Expr::primeFormula(*ev, *l);  // for next iteration
                  }
                }
              }
              vector<ID> assumps;
              for (vector<ID>::const_iterator i = acts.begin(); i != acts.end(); ++i)
                if (concrete.find(act2latch[*i]) != concrete.end())
                  assumps.push_back(*i);
              cout << "BEFORE (cex BMC): " << assumps.size() << endl;
              bool rv = cons->sat(&assumps, NULL, &assumps);
              assert (!rv);
              cout << "AFTER (cex BMC): " << assumps.size() << endl;
              set<ID> nc;
              for (vector<ID>::const_iterator i = assumps.begin(); 
                   i != assumps.end(); ++i)
                nc.insert(act2latch[*i]);
              updatePattern(sst, nc);
              delete cons;
              delete consMgr;
            }
            else {
              // extract core acts based on which are needed for generated clauses
              SAT::Manager * consMgr = sst.m.newSATManager();
              SAT::Manager::View * cons = consMgr->newView(*ev, sst.opts.backend);
              cons->timeout(sst.opts.timeout);
              cons->add(fulltr);
              vector<ID> keep, rem;
              for (vector<ID>::const_iterator i = acts.begin(); i != acts.end(); ++i)
                if (concrete.find(act2latch[*i]) != concrete.end())
                  rem.push_back(*i);
              for (unsigned int k = sst.cubes.size()-1; k > 0; --k) {
                for (CubeSet::const_iterator i = sst.cubes[k].begin();
                     i != sst.cubes[k].end(); ++i) {
                  vector<ID> cls;
                  complement(*ev, *i, cls);
                  cons->add(cls);
                }
                if (k+1 == sst.cubes.size() || sst.cubes[k+1].empty()) continue;
                vector<ID> disj;
                for (CubeSet::const_iterator i = sst.cubes[k+1].begin();
                     i != sst.cubes[k+1].end(); ++i) {
                  vector<ID> cube(*i);
                  Expr::primeFormulas(*ev, cube);
                  disj.push_back(ev->apply(Expr::And, cube));
                }
                ID target = ev->apply(Expr::Or, disj);
                SAT::Clauses targetcnf;
                Expr::tseitin(*ev, target, targetcnf);
                SAT::GID gid = cons->newGID();
                cons->add(targetcnf, gid);
                vector<ID> assumps(keep), core(rem);
                assumps.insert(assumps.end(), core.begin(), core.end());
                bool rv = cons->sat(&assumps, NULL, &core);
                assert (!rv);
                cons->remove(gid);
                keep.insert(keep.end(), core.begin(), core.end());
                set<ID> score(core.begin(), core.end());
                for (vector<ID>::iterator i = rem.begin(); i != rem.end();)
                  if (score.find(*i) != score.end())
                    rem.erase(i);
                  else
                    ++i;
              }
              cout << "BEFORE (cex IC3): " << acts.size()-remActs.size() << endl;
              cout << "AFTER (cex IC3): " << keep.size() << endl;
              set<ID> nc;
              for (vector<ID>::const_iterator i = keep.begin(); 
                   i != keep.end(); ++i)
                nc.insert(act2latch[*i]);
              updatePattern(sst, nc);
              delete cons;
              delete consMgr;
            }
          }

          if (optsprop) {
            // propagate truly inductive clauses (e.g., for FAIR, IICTL)
            sst.opts.propagate = true;

#if 1
            if (sst.cubes.size() > 1) {
              if (sst.opts.initCube) {
                SAT::Manager * initMgr = sst.m.newSATManager();
                SAT::Manager::View * init = initMgr->newView(*ev, sst.opts.backend);
                for (vector<ID>::const_iterator i = sst.opts.initCube->begin();
                     i != sst.opts.initCube->end(); ++i) {
                  vector<ID> cls;
                  cls.push_back(*i);
                  init->add(cls);
                }
                for (unsigned int k = 1; k < sst.cubes.size(); ++k)
                  for (CubeSet::const_iterator i = sst.cubes[k].begin();
                       i != sst.cubes[k].end(); ++i) {
                    vector<ID> cube(*i);
                    if (init->sat(&cube))
                      sst.cubes[k].erase(i);
                  }
                delete init;
                delete initMgr;
              }

              consMgr = sst.m.newSATManager();
              cons = consMgr->newView(*ev, sst.opts.backend);
              cons->add(sst.abs_ptr);

              SAT::Clauses constraints;
              if(sst.opts.constraints) {
                for (unsigned i = 0; i < sst.opts.constraints->size(); ++i)
                  constraints.insert(constraints.end(),
                                     (*sst.opts.constraints)[i].begin(),
                                     (*sst.opts.constraints)[i].end());
              }
              cons->add(constraints);

              unsigned int k = 1;
              if (sst.cubes[k].empty()) ++k;
              for (; !sst.cubes[k].empty(); ++k) {
                bool pconv = k+1 == sst.cubes.size() || sst.cubes[k+1].empty();
                if(sst.m.verbosity() > Options::Informative)
                  cout << k << " " << sst.cubes[k].size() 
                       << (pconv ? "*" : "") << endl;
                if (k+1 == sst.cubes.size())
                  sst.cubes.push_back(CubeSet());
                SAT::GID gid = cons->newGID();
                for (unsigned int kk = k; kk < sst.cubes.size(); ++kk)
                  for (CubeSet::const_iterator i = sst.cubes[kk].begin();
                       i != sst.cubes[kk].end(); ++i) {
                    vector<ID> cls;
                    complement(*ev, *i, cls);
                    cons->add(cls, gid);
                  }
                bool dropped = false;
                for (CubeSet::const_iterator i = sst.cubes[k].begin();
                     i != sst.cubes[k].end(); ++i) {
                  vector<ID> cube(*i);
                  Expr::primeFormulas(*ev, cube);
                  if (!cons->sat(&cube))
                    sst.cubes[k+1].insert(*i);
                  else
                    dropped = true;
                }
                cons->remove(gid);
                if (!dropped && pconv) {
                  SubsumptionUniverse su;
                  su.add(sst.cubes[k], 1);
                  su.reduce(sst.cubes[k], 1);
                  cex.indCubes = sst.cubes[k];
                  break;
                }
              }
              delete cons;
              delete consMgr;
              if(sst.m.verbosity() > Options::Informative)
                cout << "Abstract: inductive: " << cex.indCubes.size() << endl;
            }
#endif
          }

          if (pat) pat->resume.clear();
          throw cex;
        }
        else {
          // can't be concretized, so use core to direct choice of more latches
          if(sst.m.verbosity() > Options::Informative)
            cout << "Abstract: core: " << core.size() << endl;

          //minimalCore(cons, assumps, core);
          //cout << "Abstract: reduced core: " << core.size() << endl;

          unsigned int sz = concrete.size();
          for (vector<ID>::const_iterator j = core.begin(); j != core.end(); ++j)
            //pair<set<ID>::iterator, bool> rv = concrete.insert(act2latch[*j]);
            concrete.insert(act2latch[*j]);
          set<ID> score(core.begin(), core.end());
          for (vector<ID>::iterator j = remActs.begin(); j != remActs.end();)
            if (score.find(*j) != score.end())
              remActs.erase(j);
            else
              ++j;
          assert (concrete.size() > sz);

          delete cons;
          delete consMgr;
        }
      }
      catch (Safe safe) {
        // it's a proof
        if (acts.size() > remActs.size() && (sst.opts.iictl || sst.opts.fair)) {
          SAT::Manager * consMgr = sst.m.newSATManager();
          SAT::Manager::View * cons = consMgr->newView(*ev, sst.opts.backend);
          cons->timeout(sst.opts.timeout);
          cons->add(fulltr);
          CubeSet cubes = safe.proof;
          SAT::Clauses p;
          vector<ID> disj;
          for (CubeSet::const_iterator i = cubes.begin(); i != cubes.end(); ++i) {
            vector<ID> cube(*i), cls;
            disj.push_back(ev->apply(Expr::And, cube));
            complement(*ev, cube, cls);
            p.push_back(cls);
          }
          cons->add(p);
          vector<ID> errcl;
          for (SAT::Clauses::const_iterator i = err.begin(); i != err.end(); ++i) {
            vector<ID> cube(*i);
            errcl.push_back(ev->apply(Expr::Or, cube));
          }
          disj.push_back(ev->apply(Expr::And, errcl));
          SAT::Clauses er;
          Expr::tseitin(*ev, Expr::primeFormula(*ev, ev->apply(Expr::Or, disj)), er);
          cons->add(er);
          vector<ID> assumps;
          for (vector<ID>::const_iterator i = acts.begin(); i != acts.end(); ++i)
            if (concrete.find(act2latch[*i]) != concrete.end())
              assumps.push_back(*i);
          cout << "BEFORE (safe): " << assumps.size() << endl;
          bool rv = cons->sat(&assumps, NULL, &assumps);
          assert (!rv);
          cout << "AFTER (safe): " << assumps.size() << endl;
          set<ID> nc;
          for (vector<ID>::const_iterator i = assumps.begin(); i != assumps.end(); ++i)
            nc.insert(act2latch[*i]);
          updatePattern(sst, nc);
          delete cons;
          delete consMgr;
        }
        if (pat) pat->resume.clear();
        throw safe;
      }
      catch (Timeout to) {
        // save the current concrete set
        if (pat) {
          pat->resume.clear();
          pat->resume.insert(concrete.begin(), concrete.end());
        }
        throw to;
      }

      sst.rvars.clear();
      sst.nrvars.clear();
      sst.base_constraints.clear();
    }
  }

  void uaCheck(SharedState & sst, bool shortCircuit = true) {
    sst.stime = Util::get_user_cpu_time();

    Expr::Manager::View * ev = sst.m.newView();

    ExprAttachment const * eat = (ExprAttachment *) sst.m.constAttachment(Key::EXPR);
    vector<ID> inputs(eat->inputs()), frozen(eat->inputs());
    ID npi = eat->outputFnOf(eat->outputs())[0];
    vector<ID> init(eat->initialConditions());
    SAT::Clauses err;
    Expr::tseitin(*ev, Expr::primeFormula(*ev, npi), err);
    vector<ID> constraints = eat->constraintFns();
    vector<ID> latches = eat->stateVars();
    vector<ID> fns = eat->nextStateFnOf(latches);
    sst.m.constRelease(eat);

    SAT::Manager * consMgr = sst.m.newSATManager();
    CNFAttachment * cnfat = (CNFAttachment *) sst.m.constAttachment(Key::CNF);
    SAT::Clauses tr(cnfat->getCNF());
    consMgr->add(tr);
    sst.m.constRelease(cnfat);
    SAT::Manager::View * cons = consMgr->newView(*ev, sst.opts.backend);

    SAT::GID gid = cons->newGID();
    cons->add(err, gid);
    vector<ID> assumps;
    for (vector<ID>::iterator it = frozen.begin(); it != frozen.end(); ++it) {
      ID act = var(*ev);
      assumps.push_back(act);
      vector<ID> cls;
      cls.push_back(ev->apply(Expr::Not, act));
      cls.push_back(ev->apply(Expr::Not, *it));
      cons->add(cls, gid);
      cls.clear();
      cls.push_back(ev->apply(Expr::Not, act));
      cls.push_back(ev->apply(Expr::Not, ev->prime(*it)));
      cons->add(cls, gid);
    }
    vector<ID> cassumps(assumps);
    while (!cons->sat(&assumps, NULL, &cassumps)) {
      minimalCore(cons, vector<ID>(), cassumps);
      set<ID> core(cassumps.begin(), cassumps.end());
      bool changed = false;
      for (unsigned int i = 0; i < assumps.size(); ++i)
        if (core.find(assumps[i]) != core.end()) {
          changed = true;
          assumps.erase(assumps.begin()+i);
          frozen.erase(frozen.begin()+i);
          break;
        }
      if (!changed) break;
      cassumps = assumps;
    }
    cons->remove(gid);
    
    cout << "Abstraction: frozen after err: " << frozen.size() << endl;

    vector<SAT::Clauses> dummy;
    bool wasnull = false;
    if (!sst.opts.constraints) {
      wasnull = true;
      sst.opts.constraints = &dummy;
    }

    vector<ID> units;
    bool mkunits = true, mktr = sst.opts.abstract == 2;
    while (true) {
      cout << "Abstraction: frozen: " << frozen.size() << endl;

      vector<ID> sfns(fns);
      ThreeValued::Map sub;
      if (mkunits) {
        units.clear();

        for (vector<ID>::iterator it = frozen.begin(); it != frozen.end(); ++it)
          sub.insert(ThreeValued::Map::value_type(*it, ThreeValued::TVFalse));
        ThreeValued::Map justpi(sub);
        for (unsigned int i = 0; i < init.size(); ++i)
          if (ev->op(init[i]) == Expr::Var)
            sub.insert(ThreeValued::Map::value_type(init[i], ThreeValued::TVTrue));
          else
            sub.insert(ThreeValued::Map::value_type(ev->apply(Expr::Not, init[i]), 
                                                    ThreeValued::TVFalse));
        bool changed = true;
        while (changed) {
          ThreeValued::Folder tvf(*ev, sub);
          ev->fold(tvf, sfns);
          changed = false;
          ThreeValued::Map newsub(justpi);
          for (unsigned int i = 0; i < sfns.size(); ++i) {
            assert (sub.find(sfns[i]) != sub.end());
            assert (sub.find(latches[i]) != sub.end());
            ThreeValued::TV v = sub[sfns[i]];
            if (sub[latches[i]] == ThreeValued::TVX) v = ThreeValued::TVX;
            if (v != sub[latches[i]]) {
              v = ThreeValued::TVX;
              changed = true;
            }
            newsub.insert(ThreeValued::Map::value_type(latches[i], v));
          }
          sub = newsub;
        }
        for (unsigned int i = 0; i < sfns.size(); ++i) {
          ThreeValued::TV v = sub[latches[i]];
          if (v != ThreeValued::TVX)
            units.push_back(ev->apply(Expr::Equiv, latches[i], 
                                      v == ThreeValued::TVTrue ? ev->btrue() 
                                      : ev->bfalse()));
        }
        mkunits = !units.empty();
      }

      cout << "Abstraction: units: " << units.size() << endl;

      if (mktr) {
        /* TODO:
         *  - eq reduction
         *  - simplify
         *  - switch to Fabio's?
         */
        Expr::IDMap fsub;
        for (vector<ID>::iterator it = frozen.begin(); it != frozen.end(); ++it)
          fsub.insert(Expr::IDMap::value_type(*it, ev->bfalse()));
        vector<unsigned int> equiv;
        ID snpi = npi;
        if (mkunits) {
          bool havetrue = false, havefalse = false;
          for (unsigned int i = 0; i < sfns.size(); ++i) {
            ThreeValued::TV v = sub[latches[i]];
            if (v != ThreeValued::TVX) {
              sfns[i] = v == ThreeValued::TVTrue ? ev->btrue() : ev->bfalse();
              fsub.insert(Expr::IDMap::value_type(latches[i], sfns[i]));
              if (v == ThreeValued::TVTrue) {
                if (havetrue) equiv.push_back(i);
                havetrue = true;
              }
              else if (v == ThreeValued::TVFalse) {
                if (havefalse) equiv.push_back(i);
                havefalse = true;
              }
            }
          }
          Expr::varSub(*ev, fsub, sfns);
          snpi = Expr::varSub(*ev, fsub, snpi);
        }

        vector<ID> tr;
        sst.abs_er = snpi;
        tr.push_back(ev->apply(Expr::Not, snpi));
        sst.abs_tr.clear();
        vector<unsigned int>::iterator eq = equiv.begin();
        // ADAPTED FROM CNFAttachment.cpp
        vector<ID> clatches, cfns;
        for (unsigned int i = 0; i < latches.size(); ++i) {
          while (eq != equiv.end() && i > *eq) ++eq;
          if (eq != equiv.end() && i == *eq) continue;
          clatches.push_back(latches[i]);
          cfns.push_back(sfns[i]);
          tr.push_back(ev->apply(Expr::Equiv, ev->prime(latches[i]), sfns[i]));
        }
        SAT::Clauses cnf;
        for(vector<ID>::const_iterator it = constraints.begin();
            it != constraints.end(); ++it)
          if(*it != ev->btrue()) { //Ignore trivial constraints
            vector<ID> lits;
            if (Expr::isClause(*ev, *it, &lits)) {
              cnf.push_back(lits);
              for (vector<ID>::iterator it = lits.begin(); it != lits.end(); ++it)
                *it = ev->prime(*it);
              cnf.push_back(lits);
            }
            else {
              tr.push_back(*it);
              tr.push_back(Expr::primeFormula(*ev, *it));
            }
          }
        Expr::tseitin(*ev, tr, cnf);
        CNF::simplify(sst.m, cnf, sst.abs_tr, inputs, clatches, cfns);
        CNFAttachment * cnfat = (CNFAttachment *) sst.m.constAttachment(Key::CNF);
        if (sst.abs_tr.size() > cnfat->getCNF().size()) {
          mktr = false;
          sst.opts.abstract = 1;
          cout << "Abstraction: no longer making TR" << endl;
        }
        sst.m.constRelease(cnfat);

        cout << "Abstraction: TR size: " << sst.abs_tr.size() << endl;
        // END ADAPT
      }

      if (!frozen.empty()) {
        SAT::Clauses clss;
        for (vector<ID>::iterator it = frozen.begin(); it != frozen.end(); ++it) {
          vector<ID> cls;
          cls.push_back(ev->apply(Expr::Not, *it));
          clss.push_back(cls);
          cls.clear();
          cls.push_back(ev->apply(Expr::Not, ev->prime(*it)));
          clss.push_back(cls);
        }
        if (!units.empty() && !mktr)
          for (vector<ID>::iterator it = units.begin(); it != units.end(); ++it) {
            vector<ID> cls;
            cls.push_back(*it);
            clss.push_back(cls);
          }
        sst.opts.constraints->push_back(clss);
      }
      else
        sst.opts.abstract = 0;

      try {
        _check(sst, false, true);
        assert (false);
      }
      catch (CEX cex) {
        if (wasnull) sst.opts.constraints = NULL;
        delete ev;
        delete cons;
        delete consMgr;
        throw cex;
      }
      catch (Safe safe) {
        if (frozen.empty()) {
          if (wasnull) sst.opts.constraints = NULL;
          delete ev;
          delete cons;
          delete consMgr;
          throw safe;
        }

        sst.opts.constraints->pop_back();

        vector<ID> nfrozen(frozen);
        for (vector<ID>::iterator it = nfrozen.begin(); it != nfrozen.end(); ++it)
          *it = ev->apply(Expr::Not, *it);
        vector<ID> npfrozen(frozen);
        for (vector<ID>::iterator it = npfrozen.begin(); it != npfrozen.end(); ++it)
          *it = ev->apply(Expr::Not, ev->prime(*it));

        SAT::Clauses prf(safe.proof.begin(), safe.proof.end());
        SAT::Clauses npprf(prf);
        for(vector< vector<ID> >::iterator it = prf.begin(); it != prf.end(); ++it)
          for(vector<ID>::iterator lit = it->begin(); lit != it->end(); ++lit)
            *lit = ev->apply(Expr::Not, *lit);
        for(vector< vector<ID> >::iterator it = npprf.begin(); it != npprf.end(); ++it)
          for(vector<ID>::iterator lit = it->begin(); lit != it->end(); ++lit)
            *lit = ev->prime(*lit);

        if (!units.empty()) {
          set<ID> funits;
          while (true) {
            vector<ID> disj;
            for (SAT::Clauses::iterator it = npprf.begin(); it != npprf.end(); ++it)
              disj.push_back(ev->apply(Expr::And, *it));
            disj.push_back(Expr::primeFormula(*ev, npi));
            SAT::Clauses npprf_cnf;
            Expr::tseitin(*ev, ev->apply(Expr::Or, disj), npprf_cnf);
            gid = cons->newGID();
            cons->add(prf, gid);
            cons->add(npprf_cnf, gid);
            vector<ID> assumps, cunits(units);
            assumps.insert(assumps.end(), nfrozen.begin(), nfrozen.end());
            assumps.insert(assumps.end(), npfrozen.begin(), npfrozen.end());
            vector<ID> _assumps(assumps);
            _assumps.insert(_assumps.end(), cunits.begin(), cunits.end());
            if (cons->sat(&_assumps, NULL, &cunits))
              assert (false);
            minimalCore(cons, assumps, cunits);
            cons->remove(gid);
            for (vector<ID>::iterator it = cunits.begin(); it != cunits.end(); ++it) {
              if (funits.find(*it) != funits.end()) continue;
              vector<ID> cls;
              cls.push_back(*it);
              prf.push_back(cls);
              cls.clear();
              cls.push_back(ev->apply(Expr::Not, ev->prime(*it)));
              npprf.push_back(cls);
            }
            unsigned int sz = funits.size();
            funits.insert(cunits.begin(), cunits.end());
            if (funits.size() == sz) break;
          }
          units.clear();
          units.insert(units.end(), funits.begin(), funits.end());

          cout << "Abstract: critical units: " << units.size() << endl;
        }

        cout << (prf.size() > 0 ? "*" : "") << "Abstraction: prf before: " 
             << prf.size() << endl;

        set<ID> drop;
        gid = cons->newGID();
        cons->add(prf, gid);
        cons->add(err, gid);
        vector<ID> cassumps(nfrozen);
        cassumps.insert(cassumps.end(), npfrozen.begin(), npfrozen.end());
        if (!cons->sat(&cassumps, NULL, &cassumps)) {
          minimalCore(cons, vector<ID>(), cassumps);
          for (vector<ID>::iterator c = cassumps.begin(); c != cassumps.end(); ++c) {
            ID pi = ev->nprimes(*c) == 1 ? ev->unprime(*c) : *c;
            drop.insert(ev->apply(Expr::Not, pi));
            if (sst.opts.abs_onedrop) break;
          }
          for (vector<ID>::iterator c = nfrozen.begin(); c != nfrozen.end();)
            if (drop.find(ev->apply(Expr::Not, *c)) != drop.end())
              nfrozen.erase(c);
            else
              ++c;
          for (vector<ID>::iterator c = npfrozen.begin(); c != npfrozen.end();)
            if (drop.find(ev->apply(Expr::Not, ev->unprime(*c))) != drop.end())
              npfrozen.erase(c);
            else
              ++c;
        }
        else
          assert (false);
        cons->remove(gid);

        gid = cons->newGID();
        cons->add(prf, gid);
        for (SAT::Clauses::iterator it = prf.begin(); 
             it != prf.end() && (drop.empty() || !sst.opts.abs_onedrop);
             ++it) {
          while (drop.empty() || !sst.opts.abs_onedrop) {
            vector<ID> cassumps(nfrozen), assumps(*it);
            for (vector<ID>::iterator j = assumps.begin(); j != assumps.end(); ++j)
              *j = ev->apply(Expr::Not, ev->prime(*j));
            assumps.insert(assumps.end(), npfrozen.begin(), npfrozen.end());
            vector<ID> _assumps(assumps);
            _assumps.insert(_assumps.end(), cassumps.begin(), cassumps.end());
            if (cons->sat(&_assumps, NULL, &cassumps) || cassumps.empty())
              break;
            minimalCore(cons, assumps, cassumps);

            for (vector<ID>::iterator c = cassumps.begin(); c != cassumps.end(); ++c) {
              drop.insert(ev->apply(Expr::Not, *c));
              if (sst.opts.abs_onedrop) break;
            }
            for (vector<ID>::iterator c = nfrozen.begin(); c != nfrozen.end();)
              if (drop.find(ev->apply(Expr::Not, *c)) != drop.end())
                nfrozen.erase(c);
              else
                ++c;
            for (vector<ID>::iterator c = npfrozen.begin(); c != npfrozen.end();)
              if (drop.find(ev->apply(Expr::Not, ev->unprime(*c))) != drop.end())
                npfrozen.erase(c);
              else
                ++c;
          }
        }

        if (drop.empty()) {
          // prf on abstraction is inductive
          if (wasnull) sst.opts.constraints = NULL;
          delete ev;
          delete cons;
          delete consMgr;
          throw safe; // TODO: update proof to include previous proofs as well
        }

        if (sst.opts.abs_strict > 0) {
          /* TODO: much better prf reduction */
          bool done = false, changed = false;
          SAT::Clauses::iterator curr = prf.begin();
          while (!done) {
            // not quite efficient yet: redo some checks when inductive
            if (curr == prf.end()) curr = prf.begin();
            done = curr == prf.begin();
            cons->remove(gid);
            gid = cons->newGID();
            cons->add(prf, gid);
            for (; curr != prf.end(); ++curr) {
              vector<ID> assumps(*curr);
              for (vector<ID>::iterator j = assumps.begin(); j != assumps.end(); ++j)
                *j = ev->apply(Expr::Not, ev->prime(*j));
              if (sst.opts.abs_strict == 1)
                assumps.insert(assumps.end(), nfrozen.begin(), nfrozen.end());
              if (cons->sat(&assumps)) {
                changed = true;
                done = false;
                prf.erase(curr);
                break;
              }
            }
          }
          if (!changed) {
            cons->add(err, gid);
            changed = cons->sat();
          }
          cons->remove(gid);

          // prf has become inductive
          if (sst.opts.abs_strict == 2 && prf.size() > 0) {
            sst.opts.constraints->push_back(prf);
            cons->add(prf);
          }
        }
        else {
          cons->remove(gid);
          SAT::Clauses ic;
          for (vector<ID>::iterator i = init.begin(); i != init.end(); ++i) {
            vector<ID> cls;
            cls.push_back(*i);
            ic.push_back(cls);
          }
          gid = cons->newGID();
          cons->add(ic, gid);
          for (SAT::Clauses::iterator i = prf.begin(); i != prf.end();) {
            vector<ID> assumps(*i);
            for (vector<ID>::iterator j = assumps.begin(); j != assumps.end(); ++j)
              *j = ev->apply(Expr::Not, ev->prime(*j));
            assumps.insert(assumps.end(), nfrozen.begin(), nfrozen.end());
            assumps.insert(assumps.end(), npfrozen.begin(), npfrozen.end());
            if (cons->sat(&assumps))
              prf.erase(i);
            else
              ++i;
          }
          cons->remove(gid);
        }

        cout << (prf.size() > 0 ? "**" : "") << "Abstraction: prf after: " 
             << prf.size() << endl;

        for (vector<ID>::iterator it = frozen.begin(); it != frozen.end();)
          if (drop.find(*it) != drop.end())
            frozen.erase(it);
          else
            ++it;

        sst.cubes.clear();
        sst.cubes.push_back(CubeSet());
        if (!sst.opts.abs_strict) {
          CubeSet start;
          for (SAT::Clauses::iterator i = prf.begin(); i != prf.end(); ++i) {
            vector<ID> cube(*i);
            for (vector<ID>::iterator j = cube.begin(); j != cube.end(); ++j)
              *j = ev->apply(Expr::Not, *j);
            sort(cube.begin(), cube.end());
            start.insert(cube);
          }
          sst.cubes.push_back(start);
        }
        sst.infCubes.clear();
        sst.propClauses.clear();
        sst.partition.clear();
        sst.last_partition.clear();
        sst.rvars.clear();
        sst.nrvars.clear();
        sst.base_constraints.clear();
      }
    }
  }

  void check(SharedState & sst, bool shortCircuit = true) {
    if (sst.opts.abstract == 0) {
      sst.stime = Util::get_user_cpu_time();
      _check(sst, shortCircuit);
    }
    else if (sst.opts.abstract == 3) {
      oaCheck(sst, shortCircuit);
    }
    else {
      uaCheck(sst, shortCircuit);
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
        st.transRel = cnfat->getCNF();
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
      Expr::primeFormulas(*st.ev, cube);
      st.npi = st.ev->apply(Expr::And, cube);
      st.negGPropertyPrimed.insert(st.negGPropertyPrimed.end(),
                                   cube.begin(), cube.end());
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
      SAT::Manager::View* satView = satMgr->newView(*st.ev, st.opts.backend);
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

#if 0
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
#endif

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
    bool timedout = true;
    int timeout = st.m.options()["fair_pp_timeout"].as<int>();
    while(reduced) {
      reduced = false;
      SAT::Clauses nproof;
      for (SAT::Clauses::const_iterator it = proof.begin(); it != proof.end(); ++it) {
        vector<ID> cube;
        complement(_st.ev, *it, cube);
        if (!timedout && timeout > 0) {
          int64_t elapsed = Util::get_user_cpu_time() - startTime;
          if (elapsed > timeout)
            timedout = true;
        }
        if (!timedout)
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
      cout << "Time elapsed (stronger) = " << (endTime - startTime) / 1000000.0 << "s" << endl;
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
    //State of SAT manager after next statement: T & P
    //P is either included with the transition relation or is a generalized
    //property that has been added in the previous statement
    satMgr->add(st.transRel);

    Expr::Manager::View* & ev = st.ev;

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
      ID rep2 = ev->newVar("_npprep_");
      SAT::Clauses negPropPrimedCNFwithRep(st.negPropPrimedCNF);
      for(SAT::Clauses::iterator it = negPropPrimedCNFwithRep.begin();
          it != negPropPrimedCNFwithRep.end(); ++it) {
        it->push_back(ev->apply(Expr::Not, rep2));
      }
      negPropOrProofClauses.insert(negPropOrProofClauses.end(), negPropPrimedCNFwithRep.begin(), negPropPrimedCNFwithRep.end());
      //Form the OR of the two representatives
      ID r = ev->apply(Expr::Or, repClause1[0], rep2);
      Expr::tseitin(*ev, r, negPropOrProofClauses);
    }

    //State of SAT manager after next statement: F ^ P ^ T ^ (!F' v !P')
    satMgr->add(negPropOrProofClauses);

    //unordered_set<ID> propCube(st.negGPropertyPrimed.begin(), st.negGPropertyPrimed.end());

    SAT::Manager::View* satView = satMgr->newView(*ev, st.opts.backend);

    assert(!(satView->sat(&clauseVars)));

    COI::range latchRange = st.coi.cCOI();
    //Prepare primed assignment
    SAT::Assignment asgn;
    for(vector<ID>::const_iterator it = latchRange.first; it != latchRange.second; ++it) {
      asgn.insert(SAT::Assignment::value_type(ev->prime(*it), SAT::Unknown));
    }
 
    set<unsigned> clauseVarsIndices;
    for(unsigned i = 0; i < clauseVars.size(); ++i) {
      clauseVarsIndices.insert(i);
    }

    set<unsigned> keep;

    int timeout = st.m.options()["fair_pp_timeout"].as<int>();
    while(!clauseVarsIndices.empty()) {
      if (timeout > 0) {
        int64_t elapsed = Util::get_user_cpu_time() - startTime;
        if (elapsed > timeout)
          break;
      }
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
        if (st.m.options()["fair_weakenPfEfrt"].as<int>() < 1) {
          clauseVars[index] = ev->apply(Expr::Not, clauseVars[index]);
          continue;
        }
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
      cout << "Time elapsed (weaker) = " << (endTime - startTime) / 1000000.0 << "s" << endl;
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
    assert(verifyProof(st.m, proof, opts.constraints, opts, &st.gprop));
    bool weakened = deriveWeakerProof(st, proof);
    assert(verifyProof(st.m, proof, opts.constraints, opts, &st.gprop));

    while(weakened && !proof.empty()) {
      strengthened = deriveStrongerProof(st, proof, opts, true);
      assert(verifyProof(st.m, proof, opts.constraints, opts, &st.gprop));
      weakened = false;
      if(strengthened && !proof.empty()) {
        weakened = deriveWeakerProof(st, proof);
        assert(verifyProof(st.m, proof, opts.constraints, opts, &st.gprop));
      }
    }

    int64_t endTime = Util::get_user_cpu_time();

    if(st.m.verbosity() > Options::Informative) {
      cout << "IC3: Smaller proof derived: ";
      printProofSize(proof);
      cout << "Time elapsed (smaller) = " << (endTime - startTime) / 1000000.0 << "s" << endl;
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
                        bool useRAT,
                        bool * bmcProof) {
    RchAttachment const * rat = (RchAttachment *) m.constAttachment(Key::RCH);
    unsigned int clb = useRAT ? rat->cexLowerBound() : 0;
    if (opts.useRAT_stem && rat->hasTvInfo() && opts.stem == 0)
      opts.stem = rat->stemLength();
    m.constRelease(rat);
    MC::ReturnValue rv;
    SAT::Clauses unrolling1, unrolling2;
    if (clb <= 1 || opts.stem > 0) {
      size_t k = opts.bmcsz ? 2 : max(1, opts.stem+1);
      BMC::BMCOptions bopts;
      bopts.useCOI = false;
      bopts.lo = opts.bmcsz ? 1 : clb;
      bopts.bound = &k;
      bopts.printCex = opts.printCex;
      bopts.constraints = opts.constraints;
      bopts.iictl = opts.iictl;
      bopts.iictl_clauses = opts.iictl_clauses;
      bopts.silent = opts.silent;
      bopts.proofProc = opts.proofProc;
      bopts.timeout = opts.timeout;
      int64_t stime = Util::get_user_cpu_time();
      rv = BMC::check(m, bopts, cexTrace, proofCNF, 
                      opts.stem > 0 ? &unrolling1 : NULL,
                      opts.stem > 0 ? &unrolling2 : NULL);
      int64_t bmcTime = (Util::get_user_cpu_time() - stime) / 1000000;
      if (opts.timeout > 0) {
        if (bmcTime >= opts.timeout && rv.returnType == MC::Unknown)
          return rv;
        opts.timeout -= bmcTime;
      }

    }
    if (rv.returnType != MC::Unknown) {
      if(opts.printCex) {
        Expr::Manager::View * ev = m.newView();
        for(vector<Transition>::iterator it = cexTrace->begin(); it != cexTrace->end(); ++it) {
          ev->sort(it->state.begin(), it->state.end());
          ev->sort(it->inputs.begin(), it->inputs.end());
        }
        delete ev;
      }
      return rv;
    }
    if(bmcProof)
      *bmcProof = false;
    if (m.verbosity() > Options::Silent && !opts.silent)
      cout << "IC3: starting" << (opts.reverse ? " (reverse)" : "") << endl;
    if (m.verbosity() > Options::Terse && !opts.silent)
      cout << "IC3: Using " << opts.backend << " as backend" << endl;
    int rseed = m.options()["rand"].as<int>();
    if(rseed != -1) {
      srand(rseed);
      Sim::RandomGenerator::generator.seed(static_cast<unsigned int>(rseed));
    }
    SharedState sstate(m, opts, cubes, propClauses);
    if (opts.stem > 0) {
      sstate.stem = &unrolling1;
      sstate.stem_plus = &unrolling2;
    }
    MC::ReturnValue rt;
    CubeSet _indCubes;
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
        //Concretize
        ExprAttachment const * eat = (ExprAttachment *) m.constAttachment(Key::EXPR);
        Expr::IDMap cur;
        const Transition & init = cexTrace->front();
        for (vector<ID>::const_iterator it = init.state.begin(); it != init.state.end(); ++it) {
          bool pos = ev->op(*it) == Expr::Not ? false : true;
          ID var = pos ? *it : ev->apply(Expr::Not, *it);
          cur.insert(Expr::IDMap::value_type(var, pos ? ev->btrue() : ev->bfalse()));
        }
        for (vector<ID>::const_iterator it = init.inputs.begin(); it != init.inputs.end(); ++it) {
          bool pos = ev->op(*it) == Expr::Not ? false : true;
          ID var = pos ? *it : ev->apply(Expr::Not, *it);
          cur.insert(Expr::IDMap::value_type(var, pos ? ev->btrue() : ev->bfalse()));
        }
        for (vector<Transition>::iterator trIt = cexTrace->begin()+1; trIt != cexTrace->end(); ++trIt) {
          vector<ID> next = eat->nextStateFns();
          varSub(*ev, cur, next);
          cur.clear();
          trIt->state.clear();
          for (unsigned i = 0; i < next.size(); ++i) {
            assert(next[i] == ev->btrue() || next[i] == ev->bfalse());
            ID stateVar = eat->stateVars()[i];
            trIt->state.push_back(next[i] == ev->btrue() ? stateVar : ev->apply(Expr::Not, stateVar));
            cur.insert(Expr::IDMap::value_type(stateVar, next[i]));
          }
          for (vector<ID>::const_iterator it = trIt->inputs.begin(); it != trIt->inputs.end(); ++it) {
            bool pos = ev->op(*it) == Expr::Not ? false : true;
            ID var = pos ? *it : ev->apply(Expr::Not, *it);
            cur.insert(Expr::IDMap::value_type(var, pos ? ev->btrue() : ev->bfalse()));
          }
        }
        //Error state
        cexTrace->push_back(Transition());
        vector<ID> next = eat->nextStateFns();
        varSub(*ev, cur, next);
        for (unsigned i = 0; i < next.size(); ++i) {
          assert(next[i] == ev->btrue() || next[i] == ev->bfalse());
          ID stateVar = eat->stateVars()[i];
          cexTrace->back().state.push_back(next[i] == ev->btrue() ? stateVar : ev->apply(Expr::Not, stateVar));
        }
        //Sanity check: make sure state is bad. Use a SAT query rather than
        //varSub to account for models for which the property is a function of
        //primary inputs
        SAT::Manager * sman = m.newSATManager();
        SAT::Manager::View * sview = sman->newView(*ev);
        SAT::Clauses npi;
        tseitin(*ev, eat->outputFns()[0], npi);
        try {
          sview->add(npi);
        }
        catch (SAT::Trivial tr) {
          assert(false); //Property is true?!
        }
        bool sat = sview->sat(&cexTrace->back().state);
        assert(sat);
        delete sview;
        delete sman;

        m.constRelease(eat);
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

      //if (!sstate.opts.reverse) {
        // do the incremental thing here, as well
        if (indCubes || sstate.opts.propNconstr) {
          if (m.verbosity() > Options::Informative)
            cout << "Number of F_inf cubes = " << sstate.infCubes.size() << endl;
          int timeout = sstate.opts.timeout;
          sstate.opts.timeout = -1;
          State st(sstate);
          if (sstate.opts.reverse)
            initReverseSAT(st);
          else
            initSAT(st);
          renewSAT(st);
          propagateClausesSpecial(st, st.cubes.size()-2, _indCubes);
          sstate.opts.timeout = timeout;
          if (indCubes) *indCubes = _indCubes;
          if (sstate.opts.propNconstr && !_indCubes.empty()) {
            if (m.verbosity() > Options::Informative)
              cout << "Total F_inf cubes = " << _indCubes.size() << endl;
            Expr::Manager::View * ev = m.newView();
            ExprAttachment * eat = (ExprAttachment*) m.attachment(Key::EXPR);
            for (CubeSet::const_iterator it = _indCubes.begin(); it != _indCubes.end();
                 ++it) {
              ostringstream oss;
              unsigned idx = eat->constraints().size();
              oss << "dc" << idx;
              assert(!ev->varExists(oss.str()));
              ID discConstr = ev->newVar(oss.str());
              vector<ID> cube = *it;
              eat->addConstraint(discConstr, ev->apply(Expr::Not, ev->apply(Expr::And, cube)));
              if (m.verbosity() > Options::Verbose) {
                vector<ID> cls;
                complement(*ev, *it, cls);
                for(vector<ID>::const_iterator it2 = cls.begin(); it2 != cls.end();
                    ++it2) {
                  cout << Expr::stringOf(*ev, *it2) << " ";
                }
                cout << endl;
              }
            }
            m.release(eat);
            delete ev;
          }
 
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
      //}

      if (useRAT) {
        RchAttachment * rat = (RchAttachment *) m.constAttachment(Key::RCH);
        Expr::Manager::View * ev = m.newView();
        for (unsigned int i = 1; i < sstate.cubes.size(); ++i) {
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

    if (sstate.ev) {
      sstate.ev->end_local();
      delete sstate.ev;
    }
    return rt;
  }

  void clean(vector< vector<ID> > & proof) {
    for (vector< vector<ID> >::iterator it = proof.begin(); it != proof.end(); ++it)
      sort(it->begin(), it->end());
    CubeSet cs(proof.begin(), proof.end());
    proof.clear();
    proof.insert(proof.end(), cs.begin(), cs.end());
  }

  void postProcessProof(Model & m, vector< vector<ID> > & proof, ProofProcType type,
      IC3Options & opts, vector<ID> * gprop) {
    if(proof.empty()) //Nothing to process
      return;

    //Disable CTG handling
    int ctgs = opts.ctgs;
    opts.ctgs = 0;

    //Disable abstraction (TODO: use final abstraction that obtained proof)
    int abstract = opts.abstract;
    opts.abstract = 0;

    ProofPostProcState st(m, opts);
    if(gprop && !opts.iictl)
      st.gprop = *gprop;
    initProofPostProcState(st);

    assert(verifyProof(m, proof, opts.constraints, opts, gprop));

    if (type == STRENGTHEN) {
      //Strengthen proof
      deriveStrongerProof(st, proof, opts);
      clean(proof);
    }
    else if (type == WEAKEN) {
      //Weaken proof
      deriveWeakerProof(st, proof);
      clean(proof);
    }
    else if (type == SHRINK) {
      deriveSmallerProof(st, proof, opts);
      clean(proof);
    }
    else
      assert(false);

    if (gprop && !opts.iictl)
      *gprop = st.gprop;

    assert(verifyProof(m, proof, opts.constraints, opts, gprop));

    opts.ctgs = ctgs;
    opts.abstract = abstract;
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
    vector<ID> gprop, concrete;
    bool bmcProof = true;
    MC::ReturnValue rv = check(m, opts, cex, rawProof, &gprop, cubes, 
                               propClauses, indCubes, false, &bmcProof);
    opts.cycle = old_cycle;
    int timeout = opts.timeout;
    opts.timeout = -1;

    if(rv.returnType == MC::Proof && rawProof && !bmcProof) {
      if(opts.proofProc != NONE) 
        postProcessProof(m, *rawProof, opts.proofProc, opts, &gprop);
      if(!opts.iictl)
        rawProof->push_back(gprop);
    }
    opts.timeout = timeout;

    return rv;
  }

  bool mic(Model & m, IC3Options & opts, vector<ID> & cube) {
    if (m.verbosity() > Options::Informative) {
      cout << "MIC: Starting" << endl;
    }
    int abs = opts.abstract;
    opts.abstract = 0;
    int ctgs = opts.ctgs;
    opts.ctgs = 0;

    SharedState sst(m, opts);
    State _st(sst);
    initSAT(_st);
    extend(_st, 0);

    opts.abstract = abs;

    set<ID> dummy;
    if(down(_st, 1, dummy, cube)) {
      mic(_st, 1, cube, true);
      opts.ctgs = ctgs;
      return true;
    }
    opts.ctgs = ctgs;
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
        delete ev;
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
