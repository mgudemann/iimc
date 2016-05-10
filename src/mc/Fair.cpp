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

#include "Fair.h"

#include "Error.h"
#include "Expr.h"
#include "ExprUtil.h"
#include "Model.h"
#include "SAT.h"
#include "SimplifyCNF.h"
#include "Util.h"

#include <sstream>
#include <stdlib.h>
#include <unordered_map>
#include <utility>
#include <vector>

#include <iostream>

using namespace std;

namespace {

  void primeVector(Expr::Manager::View & ev, const vector<ID> & in, vector<ID> & out) {
    for(vector<ID>::const_iterator it = in.begin(); it != in.end(); ++it) {
      if(*it != ev.btrue() && *it != ev.bfalse())
        out.push_back(ev.prime(*it));
      else
        out.push_back(*it);
    }
  }

  class Timeout {
  };

  enum ProofType { Stem, CycleP, CycleN };
  class Record {
  public:
    Record(SAT::Clauses & _p, ProofType _pt) : proof(_p), pt(_pt), dup(false) {}
    SAT::Clauses proof;
    ProofType pt;
    bool dup;
  };

  class State {
  public:
    State(Model & m, Fair::FairOptions & opts, Lasso * _lasso, 
          vector<SAT::Clauses> * _proofs,
          vector<Record> & _records) :
      m(m), opts(opts), lasso(_lasso), proofs(_proofs), _ev(m.newView()), 
      ev(*_ev), fairM(NULL), fairV(NULL), 
      full_fairM(NULL), full_fairV(NULL), 
      fairIndex(0), k(opts.k), c_k(opts.k),
      gd(1.0), lcnt(0), ld(2.0), consM(NULL), consV(NULL), trivial(false),
      records(_records)
    {
      for (vector<Record>::const_iterator it = records.begin();
           it != records.end(); ++it)
        switch (it->pt) {
        case Stem:
          rproofs.push_back(it->proof);
          break;
        case CycleP:
          pproofs.push_back(it->proof);
          break;
        case CycleN:
          nproofs.push_back(it->proof);
          break;
        }

      ExprAttachment const * eat = (ExprAttachment *) m.constAttachment(Key::EXPR);

      fairs = eat->outputFnOf(eat->outputs());
      for (vector<ID>::const_iterator it = fairs.begin(); it != fairs.end(); ++it) {
        if (m.verbosity() > Options::Terse) cout << Expr::stringOf(ev, *it) << endl;
        if(*it == ev.bfalse()) {
          trivial = true;
          return;
        }
        if(*it == ev.btrue()) {
          //Empty set of clauses
          fairSets.push_back(SAT::Clauses());
          continue;
        }
        vector<ID> cube;
        Expr::conjuncts(ev, *it, cube);
        bool iscube = true;
        SAT::Clauses cnf;
        for (vector<ID>::const_iterator lit = cube.begin(); lit != cube.end(); ++lit)
          if (ev.op(*lit) != Expr::Var && ev.op(ev.apply(Expr::Not, *lit)) != Expr::Var) {
            iscube = false;
            break;
          }
          else {
            vector<ID> cls;
            cls.push_back(*lit);
            cnf.push_back(cls);
          }
        if (!iscube) {
          cnf.clear();
          Expr::tseitin(ev, *it, cnf);
        }
        fairSets.push_back(cnf);
      }

      svars = eat->stateVars();
      sivars = svars;
      set<ID> inputs(eat->inputs().begin(), eat->inputs().end()), fvars, kvars;
      for (vector<ID>::const_iterator it = fairs.begin(); it != fairs.end(); ++it)
        Expr::variables(ev, *it, fvars);
      set_intersection(inputs.begin(), inputs.end(), fvars.begin(), fvars.end(), inserter(kvars, kvars.end()));
      sivars.insert(sivars.end(), kvars.begin(), kvars.end());
        
      m.constRelease(eat);

      CNFAttachment * cnfat = (CNFAttachment *) m.constAttachment(Key::CNF);
      trltn = cnfat->getPlainCNF();
      m.constRelease(cnfat);

      if(opts.constraints) {
        //Do not add constraints if they're trivial
        if(opts.constraints->size() == 1 && (*opts.constraints)[0].size() == 1 && (*opts.constraints)[0][0] == ev.bfalse()) {
          trivial = true;
          return;
        }
        if(!(opts.constraints->size() == 1 && (*opts.constraints)[0].size() == 1 && (*opts.constraints)[0][0] == ev.btrue())) {
          trltn.insert(trltn.end(), opts.constraints->begin(), opts.constraints->end());
          allConstraints.push_back(*opts.constraints);
          //SAT::Clauses clauses;
          //for(SAT::Clauses::const_iterator it = opts.constraints->begin(); it != opts.constraints->end(); ++it) {
          //  SAT::Clause cls;
          //  primeVector(ev, *it, cls);
          //  trltn.push_back(cls);
          //  clauses.push_back(cls);
          //}
          //allConstraints.push_back(clauses);
        }
      }

      consM = m.newSATManager();
      consV = consM->newView(ev);
      consV->add(trltn);
    }
    ~State() {
      if (fairV) delete fairV;
      if (fairM) delete fairM;
      if (full_fairV && full_fairV != fairV) delete full_fairV;
      if (full_fairM && full_fairM != fairM) delete full_fairM;
      if (consV) delete consV;
      if (consM) delete consM;
      delete _ev;
    }

    Model & m;
    Fair::FairOptions & opts;
    Lasso * lasso;
    vector<SAT::Clauses> * proofs;

    Expr::Manager::View * _ev;
    Expr::Manager::View & ev;

    vector<ID> svars;
    vector<ID> sivars;  // 111611
    SAT::Clauses trltn;

    SAT::Manager * fairM;
    SAT::Manager::View * fairV;

    // 072511
    SAT::Manager * full_fairM;
    SAT::Manager::View * full_fairV;

    vector<SAT::Clauses> fairSets;
    unsigned fairIndex;

    int k;
    int c_k;

    vector<SAT::Clauses> pproofs;
    vector<SAT::Clauses> nproofs;
    vector<SAT::Clauses> rproofs;
    vector<SAT::Clauses> rconstraints;
    vector<SAT::Clauses> allConstraints;

    float gd;
    unsigned long long lcnt;
    float ld;

    SAT::Manager * consM;
    SAT::Manager::View * consV;

    set<ID> slicedNDiced;
    vector<ID> fairs;

    bool trivial; //If a fairness constraint is false

    vector<Record> & records;
  };

  void printVector(State & st, const vector<ID> & c) {
    for (vector<ID>::const_iterator it = c.begin(); it != c.end(); it++)
      if (st.m.verbosity() > Options::Terse) cout << " " << Expr::stringOf(st.ev, *it);
    if (st.m.verbosity() > Options::Terse) cout << endl;
  }

  ID fairVar(State & st, ID var, unsigned fi) {
    ostringstream nm;
    nm << st.ev.varName(var) << ".f" << fi;
    return st.ev.primeTo(st.ev.newVar(nm.str()), st.ev.nprimes(var));
  }
  ID fairLit(State & st, ID lit, unsigned fi) {
    if (st.ev.op(lit) == Expr::Not)
      return st.ev.apply(Expr::Not, fairVar(st, st.ev.apply(Expr::Not, lit), fi));
    else
      return fairVar(st, lit, fi);
  }

  ID choiceVar(State & st, unsigned i) {
    ostringstream nm;
    nm << "cv@" << i;
    return st.ev.newVar(nm.str());
  }

  void ficnf(State & st, const SAT::Clauses & in, unsigned fi, SAT::Clauses & out) {
    for (SAT::Clauses::const_iterator it = in.begin(); it != in.end(); ++it) {
      vector<ID> cls;
      for (vector<ID>::const_iterator lit = it->begin(); lit != it->end(); ++lit)
        cls.push_back(fairLit(st, *lit, fi));
      out.push_back(cls);
    }
  }

  void timeStep(State & st, SAT::Clauses & cnf, int ts, ID except) {
    for (SAT::Clauses::iterator it = cnf.begin(); it != cnf.end(); ++it)
      for (vector<ID>::iterator lit = it->begin(); lit != it->end(); ++lit)
        if (*lit != except) *lit = primeFormula(st.ev, *lit, ts);
  }

  void fiproofs(State & st, 
                const SAT::Clauses & inp, const SAT::Clauses & innp, 
                unsigned fi, unsigned i,
                SAT::Clauses & outp, SAT::Clauses & outnp)
  {
    SAT::Clauses p, np;

    ID cvar = choiceVar(st, i);
    ID ncvar = st.ev.apply(Expr::Not, cvar);
    
    for (SAT::Clauses::const_iterator it = inp.begin(); it != inp.end(); ++it) {
      vector<ID> cls(*it);
      cls.push_back(ncvar);
      p.push_back(cls);
    }
    for (SAT::Clauses::const_iterator it = innp.begin(); it != innp.end(); ++it) {
      vector<ID> cls(*it);
      cls.push_back(cvar);
      np.push_back(cls);
    }

    for (SAT::Clauses::iterator it = p.begin(); it != p.end(); ++it)
      for (vector<ID>::iterator lit = it->begin(); lit != it->end(); ++lit)
        if (*lit != ncvar) *lit = fairLit(st, *lit, fi);
    for (SAT::Clauses::iterator it = np.begin(); it != np.end(); ++it)
      for (vector<ID>::iterator lit = it->begin(); lit != it->end(); ++lit)
        if (*lit != cvar) *lit = fairLit(st, *lit, fi);

    timeStep(st, p, -st.k, ncvar);
    timeStep(st, np, -st.k, cvar);
    for (int ts = -st.k; ts <= 1+st.k; ++ts) {
      outp.insert(outp.end(), p.begin(), p.end());
      outnp.insert(outnp.end(), np.begin(), np.end());
      if (ts <= st.k) {
        timeStep(st, p, 1, ncvar);
        timeStep(st, np, 1, cvar);
      }
    }
  }

  void compress(State & st, SAT::Clauses & cnf) {
    return;
    vector<ID> dummy;
    SAT::Clauses curr(cnf);
    int osz = cnf.size();
    cnf.clear();
    CNF::simplify(st.m, curr, cnf, dummy, st.svars, dummy, false);
    int fsz = cnf.size();
    if (st.m.verbosity() > Options::Terse)
      cout << "Fair: compress " << osz << " -> " << fsz << endl;
  }

  void addFair(State & st, const SAT::Clauses & fair, unsigned fi, 
               bool all, SAT::GID gid = SAT::NULL_GID) {
    SAT::Clauses fifair;
    ficnf(st, fair, fi, fifair);
    st.fairV->add(fifair, gid);

    if (all) {
      SAT::Clauses fitrln;
      ficnf(st, st.trltn, fi, fitrln);
      timeStep(st, fitrln, -st.k, st.ev.btrue());
      for (int ts = -st.k; ts < 1+st.k; ++ts) {
        st.fairV->add(fitrln, gid);        
        if (ts < st.k) timeStep(st, fitrln, 1, st.ev.btrue());
      }

      vector<ID> conj;
      for (int i = -st.k; st.k > 0 && i < 1+st.k; ++i) {
        if (i == -1 || i == 0) continue;
        vector<ID> disj;
        vector<ID> eq;
        for (vector<ID>::const_iterator it = st.svars.begin(); 
             it != st.svars.end(); ++it) {
          eq.push_back(st.ev.apply(Expr::Or, 
                                   primeFormula(st.ev, *it, i),
                                   st.ev.apply(Expr::Not, *it)));
          eq.push_back(st.ev.apply(Expr::Or, 
                                   primeFormula(st.ev, st.ev.apply(Expr::Not, *it), i),
                                   *it));
        }
        disj.push_back(st.ev.apply(Expr::And, eq));
        for (int j = i+1; j <= (i < 0 ? -1 : 1+st.k); ++j) {
          vector<ID> disjc(disj);
          for (vector<ID>::const_iterator it = st.svars.begin(); 
               it != st.svars.end(); ++it) {
            disjc.push_back(st.ev.apply(Expr::And, 
                                        primeFormula(st.ev, *it, i),
                                        primeFormula(st.ev, 
                                                     st.ev.apply(Expr::Not, *it), j)));
            disjc.push_back(st.ev.apply(Expr::And, 
                                        primeFormula(st.ev, *it, j),
                                        primeFormula(st.ev, 
                                                     st.ev.apply(Expr::Not, *it), i)));
          }
          conj.push_back(st.ev.apply(Expr::Or, disjc));
        }
      }
      SAT::Clauses eqc;
      Expr::tseitin(st.ev, st.ev.apply(Expr::And, conj), eqc);
      st.fairV->add(eqc, gid);

      for (vector<SAT::Clauses>::const_iterator it = st.rproofs.begin(); 
           it != st.rproofs.end(); ++it) {
        SAT::Clauses fir;
        ficnf(st, *it, fi, fir);
        timeStep(st, fir, -st.k, st.ev.btrue());
        for (int ts = -st.k; ts <= 1+st.k; ++ts) {
          st.fairV->add(fir, gid);        
          if (ts <= st.k) timeStep(st, fir, 1, st.ev.btrue());
        }
      }

      for (unsigned i = 0; i < st.pproofs.size(); ++i) {
        SAT::Clauses p, np;
        fiproofs(st, st.pproofs[i], st.nproofs[i], fi, i+1, p, np);
        st.fairV->add(p, gid);
        st.fairV->add(np, gid);
      }
    }
  }

  bool _weakenFair(State & st, unsigned i, unsigned fi, bool simple, int64_t stt) {
    if (i == st.fairSets.size()) {
      st.fairIndex = fi;
      if (fi == st.fairSets.size()) 
        return true;
      return st.fairV->sat();
    }
    if (!simple && i < 63) {
      if ((Util::get_user_cpu_time() - stt) / 1000000 > 5)
        throw Timeout();
      for (unsigned tfi = 1; tfi <= fi; ++tfi) {
        SAT::GID gid = st.fairV->newGID();
        addFair(st, st.fairSets[i], tfi, false, gid);
        if (st.fairV->sat() && _weakenFair(st, i+1, fi, simple, stt)) {
          st.fairV->remove(gid);
          addFair(st, st.fairSets[i], tfi, false);
          return true;
        }
        st.fairV->remove(gid);
      }
    }
    addFair(st, st.fairSets[i], fi+1, true);
    return _weakenFair(st, i+1, fi+1, simple, stt);
  }
  bool weakenFair(State & st, bool simple = false) {
    if (st.m.verbosity() > Options::Terse) cout << "Fair: weakenFair" << endl;

    if (st.fairV) delete st.fairV;
    if (st.fairM) delete st.fairM;
    st.fairM = st.m.newSATManager();
    st.fairV = st.fairM->newView(st.ev);

    bool rv;
    try {
      rv = _weakenFair(st, 0, 0, simple, Util::get_user_cpu_time());
      if (st.full_fairM && st.fairIndex == st.fairSets.size()) {
        delete st.fairV;
        delete st.fairM;
        st.fairM = st.full_fairM;
        st.fairV = st.full_fairV;
      }
    }
    catch (Timeout to) {
      if (st.m.verbosity() > Options::Terse) 
        cout << "Fair: weakenFair -> simple" << endl;
      delete st.fairV;
      delete st.fairM;
      if (st.k == st.c_k) {
        st.fairM = st.full_fairM;
        st.fairV = st.full_fairV;
        st.fairIndex = st.fairSets.size();
        rv = true;
      }
      else {
        st.fairM = st.m.newSATManager();
        st.fairV = st.fairM->newView(st.ev);
        rv = _weakenFair(st, 0, 0, true, Util::get_user_cpu_time());
      }
    }

    if (st.m.verbosity() > Options::Terse) 
      cout << "Fair: " << st.fairIndex << "/" << st.fairSets.size() << endl;

    return rv;
  }

  bool getSkeleton(State & st, vector< vector<ID> > & skel) {
    if (st.m.verbosity() > Options::Terse) cout << "Fair: getSkeleton" << endl;
    skel.clear();
    SAT::Assignment asgn;
    // 111611: svars -> sivars
    for (vector<ID>::const_iterator it = st.sivars.begin(); it != st.sivars.end(); ++it)
      for (unsigned i = 1; i <= st.fairIndex; ++i) {
        ID v = fairVar(st, *it, i);
        asgn.insert(SAT::Assignment::value_type(v, SAT::Unknown));
      }
    if (st.fairV->sat(NULL, &asgn)) {
      for (unsigned i = 1; i <= st.fairIndex; ++i) {
        vector<ID> cube;
        for (vector<ID>::const_iterator it = st.sivars.begin(); 
             it != st.sivars.end(); ++it) {
          ID var = fairVar(st, *it, i);
          SAT::Assignment::const_iterator vit = asgn.find(var);
          if (vit->second == SAT::True) cube.push_back(*it);
          else cube.push_back(st.ev.apply(Expr::Not, *it));
        }
        bool add = true;
        for (unsigned j = 0; j < skel.size(); ++j)
          if (skel[j] == cube) {
            add = false;
            break;
          }
        if (add) skel.push_back(cube);
      }
      return true;
    }
    return false;
  }

  void addGlobalProof(State & st, SAT::Clauses & proof, bool isproof = true) {
    if (isproof && st.m.verbosity() > Options::Terse) {
      cout << "Fair: addGlobalProof " << proof.size() << endl;
      for (SAT::Clauses::const_iterator it = proof.begin(); it != proof.end(); ++it)
        printVector(st, *it);
    }

    st.rconstraints.push_back(proof);
    st.consV->add(st.rconstraints.back());
    st.rproofs.push_back(proof);
    st.records.push_back(Record(proof, Stem));
    for (unsigned i = 1; i <= st.fairIndex; ++i) {
      SAT::Clauses iproof;
      ficnf(st, proof, i, iproof);
      timeStep(st, iproof, -st.k, st.ev.btrue());
      for (int ts = -st.k; ts <= 1+st.k; ++ts) {
        st.fairV->add(iproof);
        if (ts <= st.k) timeStep(st, iproof, 1, st.ev.btrue());
      }
    }
    // 072511
    if (st.full_fairV != st.fairV)
      for (unsigned i = 1; i <= st.fairSets.size(); ++i) {
        SAT::Clauses iproof;
        ficnf(st, proof, i, iproof);
        timeStep(st, iproof, -st.c_k, st.ev.btrue());
        for (int ts = -st.c_k; ts <= 1+st.c_k; ++ts) {
          st.full_fairV->add(iproof);
          if (ts <= st.c_k) timeStep(st, iproof, 1, st.ev.btrue());
        }
      }
  }

  void addCycleProof(State & st, SAT::Clauses & proof, vector<ID> * source, bool rec = true) {
    if (st.m.verbosity() > Options::Terse) {
      cout << "Fair: addCycleProof " << proof.size() << endl;
      for (SAT::Clauses::const_iterator it = proof.begin(); it != proof.end(); ++it)
        printVector(st, *it);
    }

#if 0
    unsigned lcnt = 0;
    for (SAT::Clauses::const_iterator it = proof.begin(); it != proof.end(); ++it)
      lcnt += it->size();
    st.lcnt += lcnt;
#endif
    bool crc = proof.size() == 1; 
    //true; // lcnt <= st.ld * ((float) st.lcnt) / ((float) (st.pproofs.size()+1));

    SAT::Clauses nproof, reach;
    if (proof.size() == 1) {
      for (unsigned i = 0; i < proof[0].size(); ++i) {
        vector<ID> cls;
        cls.push_back(st.ev.apply(Expr::Not, proof[0][i]));
        nproof.push_back(cls);
      }
      if (crc) {
        vector<ID> npp(proof[0]), _rc(proof[0]);
        for (vector<ID>::iterator lit = npp.begin(); lit != npp.end(); ++lit)
          *lit = primeFormula(st.ev, st.ev.apply(Expr::Not, *lit));
        ID root = Expr::tseitin(st.ev, st.ev.apply(Expr::And, npp), reach, NULL, false);
        _rc.push_back(root);
        reach.push_back(_rc);
      }
    }
    else {
      vector<ID> _nproof;
      for (SAT::Clauses::const_iterator it = proof.begin(); it != proof.end(); ++it) {
        vector<ID> cube;
        for (vector<ID>::const_iterator lit = it->begin(); lit != it->end(); ++lit)
          cube.push_back(st.ev.apply(Expr::Not, *lit));
        _nproof.push_back(st.ev.apply(Expr::And, cube));
      }
      ID np = st.ev.apply(Expr::Or, _nproof);
      Expr::tseitin(st.ev, np, nproof);
      compress(st, nproof);
      if (crc) {
        ID npp = Expr::primeFormula(st.ev, np);
        ID root = Expr::tseitin(st.ev, npp, reach, NULL, false);
        for (SAT::Clauses::const_iterator it = proof.begin(); it != proof.end(); ++it) {
          vector<ID> cls(*it);
          cls.push_back(root);
          reach.push_back(cls);
        }
      }
    }

    bool nempty = false;
#if 1
    if (source) {
      SAT::GID gid = st.consV->newGID();
      st.consV->add(nproof, gid);
      SAT::Clauses npproof(nproof);
      for (SAT::Clauses::iterator it = npproof.begin(); it != npproof.end(); ++it)
        Expr::primeFormulas(st.ev, *it);
      st.consV->add(npproof, gid);
      vector<ID> assumps(*source);
      if (!st.consV->sat(&assumps, NULL, &assumps, gid) 
          && assumps.size() < source->size()) {
        if (assumps.size() == 0) {
          if (st.m.verbosity() > Options::Terse)
            cout << "Fair: empty after source expansion" << endl;
          nempty = true;
        }
        else {
          if (st.m.verbosity() > Options::Terse)
            cout << "Fair: adding negation of source (" << source->size() 
                 << " -> " << assumps.size() << ")" << endl;
          for (vector<ID>::iterator it = assumps.begin(); it != assumps.end(); ++it)
            *it = st.ev.apply(Expr::Not, *it);
          nproof.push_back(assumps);
        }
      }
      st.consV->remove(gid);
    }
#endif

    if (!nempty) {
      SAT::GID gid = st.full_fairV->newGID();
      for (unsigned fi = 1; fi <= st.fairSets.size(); ++fi) {
        SAT::Clauses iproof, inproof;
        int kcp = st.k;
        st.k = st.c_k;
        fiproofs(st, proof, nproof, fi, st.pproofs.size()+1, iproof, inproof);
        st.k = kcp;
        st.full_fairV->add(iproof, gid);
        st.full_fairV->add(inproof, gid);
      }
      ID cvar = choiceVar(st, st.pproofs.size()+1);
      vector<ID> assumps(1, cvar);
      bool pside = st.full_fairV->sat(&assumps);
      assumps[0] = st.ev.apply(Expr::Not, cvar);
      bool nside = st.full_fairV->sat(&assumps);
      st.full_fairV->remove(gid);

      if (!pside) {
        if (st.m.verbosity() > Options::Terse) cout << "PSIDE" << endl;
        proof.clear();
        proof.push_back(vector<ID>());
        crc = true;
        reach = nproof;
        for (SAT::Clauses::iterator it = reach.begin(); it != reach.end(); ++it)
          primeFormulas(st.ev, *it);
      }
      if (!nside) {
        if (st.m.verbosity() > Options::Terse) cout << "NSIDE" << endl;
        nproof.clear();
        nproof.push_back(vector<ID>());
        crc = true;
        reach = proof;
      }
      if (!pside && !nside)
        // almost done but don't want to create a triviality
        crc = false;
    }

    if (crc) {
      st.ld *= 0.995;
      if (!nempty) compress(st, reach);
      st.rconstraints.push_back(nempty ? proof : reach);
      st.consV->add(st.rconstraints.back());
    }
    st.pproofs.push_back(proof);
    st.nproofs.push_back(nproof);
    if (rec) {
      st.records.push_back(Record(proof, CycleP));
      st.records.push_back(Record(nproof, CycleN));
    }

    for (unsigned fi = 1; fi <= st.fairIndex; ++fi) {
      SAT::Clauses iproof, inproof;
      fiproofs(st, proof, nproof, fi, st.pproofs.size(), iproof, inproof);
      st.fairV->add(iproof);
      st.fairV->add(inproof);
    }
    if (st.full_fairV != st.fairV)
      for (unsigned fi = 1; fi <= st.fairSets.size(); ++fi) {
        SAT::Clauses iproof, inproof;
        int kcp = st.k;
        st.k = st.c_k;
        fiproofs(st, proof, nproof, fi, st.pproofs.size(), iproof, inproof);
        st.k = kcp;
        st.full_fairV->add(iproof);
        st.full_fairV->add(inproof);
      }
  }

  bool cycleReach(State & st, vector<ID> & source, vector<ID> & target, 
                  vector<SAT::Clauses> & proofs, vector<Transition> * trace,
                  vector<IC3::CubeSet> & incr) {
    bool same = st.ev.apply(Expr::And, source) == st.ev.apply(Expr::And, target);

    if (st.m.verbosity() > Options::Terse) 
      cout << "Fair: cycle reach (" << same << ")" << endl;

    ExprAttachment * eat = (ExprAttachment *) st.m.attachment(Key::EXPR);
    ID o0 = eat->outputs()[0];
    ID ofn0 = eat->outputFnOf(o0);
    eat->setOutputFn(o0, st.ev.apply(Expr::And, target));
    vector<ID> init(eat->initialConditions());
    eat->clearInitialConditions();
    eat->addInitialConditions(source);
    st.m.release(eat);

    vector<SAT::Clauses> constraints;
    if(st.opts.constraints) {
      constraints = st.allConstraints;
      constraints.insert(constraints.end(), st.rconstraints.begin(),
                         st.rconstraints.end());
    }
    st.opts.ic3_opts.constraints = st.opts.constraints ? &constraints :
                                                         &st.rconstraints;
    st.opts.ic3_opts.bmcsz = same;
    st.opts.ic3_opts.proofProc = IC3::SHRINK;
    st.opts.ic3_opts.printCex = st.opts.printCex;

    //MC::ReturnValue rv = IC3::reach(st.m, st.opts.ic3_opts, proofs, trace);
    IC3::CubeSet indCubes;
    vector<IC3::LevClauses> dummy;
    st.opts.ic3_opts.incremental = true;
    st.opts.ic3_opts.propagate = true;
    MC::ReturnValue rv = IC3::reach2(st.m, st.opts.ic3_opts, trace, &proofs, &incr, 
                                     &dummy, &indCubes);
    st.opts.ic3_opts.incremental = false;
    st.opts.ic3_opts.propagate = false;
    incr.clear();
    if (indCubes.size() > 0) incr.push_back(indCubes);

    eat = (ExprAttachment *) st.m.attachment(Key::EXPR);
    eat->setOutputFn(o0, ofn0);
    eat->clearInitialConditions();
    eat->addInitialConditions(init);
    st.m.release(eat);

    if (rv.returnType == MC::Unknown) throw Timeout();
    return rv.returnType == MC::Proof;
  }

  bool globalReach(State & st, vector<ID> & target, SAT::Clauses & proof, 
                   vector<Transition> * trace, vector<IC3::CubeSet> & incr) {
    if (st.m.verbosity() > Options::Terse) 
      cout << "Fair: global reach" << endl;

    ExprAttachment * eat = (ExprAttachment *) st.m.attachment(Key::EXPR);
    ID o0 = eat->outputs()[0];
    ID ofn0 = eat->outputFnOf(o0);
    eat->setOutputFn(o0, st.ev.apply(Expr::And, target));
    st.m.release(eat);

    vector<SAT::Clauses> constraints;
    if(st.opts.constraints) {
      constraints = st.allConstraints;
      constraints.insert(constraints.end(), st.rproofs.begin(), 
                         st.rproofs.end());
    }
    st.opts.ic3_opts.constraints = st.opts.constraints ? &constraints :
                                                        &st.rproofs;
    st.opts.ic3_opts.bmcsz = false;
    if(st.opts.iictl)
      st.opts.ic3_opts.proofProc = st.opts.proofProc;
    else
      st.opts.ic3_opts.proofProc = IC3::STRENGTHEN;
    st.opts.ic3_opts.printCex = st.opts.printCex;

    vector<SAT::Clauses> proofs;
    //MC::ReturnValue rv = IC3::reach(st.m, st.opts.ic3_opts, proofs, trace);
    IC3::CubeSet indCubes;
    vector<IC3::LevClauses> dummy;
    st.opts.ic3_opts.incremental = true;
    st.opts.ic3_opts.propagate = true;
    MC::ReturnValue rv = IC3::reach2(st.m, st.opts.ic3_opts, trace, &proofs, &incr, 
                                     &dummy, &indCubes);
    st.opts.ic3_opts.incremental = false;
    st.opts.ic3_opts.propagate = false;
    incr.clear();

    if (rv.returnType == MC::Proof) 
      proof = proofs[0];
    else if (indCubes.size() > 0) {
      // use inductive clauses
      if (st.m.verbosity() > Options::Terse)
        cout << "Fair: obtained " << indCubes.size() << " inductive clauses" << endl;
      SAT::Clauses indClauses;
      for (IC3::CubeSet::const_iterator it = indCubes.begin(); 
           it != indCubes.end(); ++it) {
        SAT::Clause cls(*it);
        for (SAT::Clause::iterator lit = cls.begin(); lit != cls.end(); ++lit)
          *lit = st.ev.apply(Expr::Not, *lit);
        indClauses.push_back(cls);
      }
      addGlobalProof(st, indClauses, false);
    }

    eat = (ExprAttachment *) st.m.attachment(Key::EXPR);
    eat->setOutputFn(o0, ofn0);
    st.m.release(eat);

    if (rv.returnType == MC::Unknown) throw Timeout();
    return rv.returnType == MC::Proof;
  }

  void sliceNDice(State & st) {
    if (st.m.verbosity() > Options::Terse) 
      cout << "Fair: begin slice'n'dice" << endl;
    int cnt = 0;
    bool changed = true;
    vector<ID> checks(st.svars);
    //checks.insert(checks.end(), st.fairs.begin(), st.fairs.end());
    while (changed) {
      changed = false;
      for (vector<ID>::const_iterator it = checks.begin(); it != checks.end(); ++it) {
        for (int i = 0; i < 2; ++i) {
          ID lit = i == 0 ? *it : st.ev.apply(Expr::Not, *it);
          if (st.slicedNDiced.find(*it) != st.slicedNDiced.end()) continue;
          if (st.ev.op(*it) == Expr::Var || st.ev.op(st.ev.apply(Expr::Not, *it)) == Expr::Var) {
            vector<ID> assumps;
            assumps.push_back(lit);
            assumps.push_back(primeFormula(st.ev, st.ev.apply(Expr::Not, lit)));
            if (!st.consV->sat(&assumps)) {
              vector<ID> cls(1, lit);
              SAT::Clauses pf(1, cls);
              addCycleProof(st, pf, NULL, false);
              st.slicedNDiced.insert(*it);
              changed = true;
              ++cnt;
            }
          }
          else {
            SAT::GID tmp = st.consV->newGID();
            SAT::Clauses cnf, ncnf;
            tseitin(st.ev, lit, cnf);
            tseitin(st.ev, primeFormula(st.ev, st.ev.apply(Expr::Not, lit)), ncnf);
            st.consV->add(cnf, tmp);
            st.consV->add(ncnf, tmp);
            if (!st.consV->sat()) {
              addCycleProof(st, cnf, NULL, false);
              st.slicedNDiced.insert(*it);
              changed = true;
              ++cnt;
            }
            st.consV->remove(tmp);
          }
        }
      }
    }
    if (st.m.verbosity() > Options::Terse) {
      if (cnt) 
        cout << "Fair: end slice'n'dice (" << cnt << ")" << endl;
      else
        cout << "Fair: end slice'n'dice" << endl;
    }
  }

  bool check(State & st) {
    // 072511
    int kcp = st.k;
    st.k = st.c_k;
    weakenFair(st, true);
    st.fairIndex = 0;
    st.k = kcp;
    st.full_fairM = st.fairM;
    st.full_fairV = st.fairV;
    st.fairM = NULL;
    st.fairV = NULL;

    unsigned int rcsz = 0;
    bool first = true;

    while (st.fairIndex < st.fairSets.size() && weakenFair(st)) {
      if (first) {
        sliceNDice(st);
        first = false;
      }
      vector< vector<ID> > skel;
      while (getSkeleton(st, skel)) {
        if (st.m.verbosity() > Options::Terse) 
          cout << "Fair: skeleton size = " << skel.size() << endl;
        assert (skel.size() > 0);

        vector<bool> sched(1+skel.size(), false);
        st.opts.ic3_opts.timeout = 1;
        int todo = sched.size();

        bool gfirst;
        if(st.opts.global_last)
          gfirst = false;
        else
          gfirst = rand() < st.gd * INT_MAX;
        unsigned offset = rand() % skel.size(), i;
        vector< vector<Transition> > traces(sched.size());
        vector< vector<IC3::CubeSet> > incr(sched.size(), vector<IC3::CubeSet>());
        while (true) {
          if (st.m.options().count("fair_xincr"))
            for (uint x = 0; x < incr.size(); ++x)
              incr[x].clear();
          if (st.m.verbosity() > Options::Terse) {
            cout << "Fair: incremental levels are ";
            for (uint x = 0; x < incr.size(); ++x)
              cout << incr[x].size() << " ";
            cout << endl;
          }
          unsigned j = 0;
          for (i = gfirst ? 0 : 1+offset; 
               j < sched.size(); 
               ++j,
                 i = gfirst && i == 0 
                 ? 1+offset
                 : !gfirst && j == sched.size()-1
                 ? 0
                 : i == sched.size()-1
                 ? 1
                 : i+1) {
            if (sched[i]) continue;
            try {
              if (i == 0) {
                SAT::Clauses proof;
                vector<Transition> trace;
                if (globalReach(st, skel[rand() % skel.size()], 
                                proof, st.opts.printCex ? &trace : NULL,
                                incr[i])) {
                  addGlobalProof(st, proof);
                  st.gd /= .7;
                  if (st.gd > 1.0) st.gd = 1.0;
                  goto SAFE;
                }
                else {
                  st.gd *= .7;
                  traces[i] = trace;
                }
              }
              else {
                vector<SAT::Clauses> proofs;
                vector<Transition> trace;
                if (cycleReach(st, skel[i-1], skel[i % skel.size()],
                               proofs, st.opts.printCex ? &trace : NULL,
                               incr[i])) {
                  for (unsigned k = 0; k < proofs.size(); ++k)
                    addCycleProof(st, proofs[k], 
                                  skel.size() == 1 ? &skel[i-1] : NULL);
                  goto SAFE;
                }
                else {
                  traces[i] = trace;
                }
              }
              sched[i] = true;
              if (--todo == 1) st.opts.ic3_opts.timeout = -1;
            }
            catch (Timeout t) {
              if (st.m.verbosity() > Options::Terse) 
                cout << "timeout (" << st.opts.ic3_opts.timeout << ")" << endl;
              if (i == 0) {
                st.gd *= 0.7;
                if (st.gd <= 0.001) st.gd = 0.001;
              }
            }
          }
          if (todo == 0) {
            //Populate "lasso" with traces
            if(st.lasso) {
              traces[0].pop_back();
              st.lasso->stem = traces[0];
              for(unsigned i = 1; i < traces.size(); ++i) {
                assert(traces[i].size() > 1);
                traces[i].pop_back();
                st.lasso->loop.insert(st.lasso->loop.end(), traces[i].begin(), traces[i].end());
              }
            }
            return false;
          }
          st.opts.ic3_opts.timeout *= 2;
        }
      SAFE:
        if (rcsz < st.rconstraints.size())
          sliceNDice(st);
        rcsz = st.rconstraints.size();
      }
    }
    //Populate proofs
    //For now just add global reachability information (rproof?)
    if(st.proofs) {
      st.proofs->resize(1);
      for(vector<SAT::Clauses>::const_iterator it = st.rproofs.begin();
          it != st.rproofs.end(); ++it) {
        (*st.proofs)[0].insert((*st.proofs)[0].end(), it->begin(), it->end());
      }
    }
    return true;
  }

}

namespace Fair {

  MC::ReturnValue check(Model & m, FairOptions & opts, Lasso * lasso,
                        vector<SAT::Clauses> * proofs) {
    static vector< vector<Record> > records;
    ExprAttachment * eat = (ExprAttachment *) m.attachment(Key::EXPR);
    vector<ID> init(eat->initialConditions());
    m.release(eat);
    Expr::Manager::View * ev = m.newView();
    Expr::IDMap asgn;
    for (vector<ID>::const_iterator it = init.begin(); it != init.end(); ++it) {
      bool isvar = ev->op(*it) == Expr::Var;
      ID var = isvar ? *it : ev->apply(Expr::Not, *it);
      assert (ev->op(var) == Expr::Var);
      asgn.insert(Expr::IDMap::value_type(var, isvar ? ev->btrue() : ev->bfalse()));
    }
    vector<Record> crec;
    for (vector< vector<Record> >::iterator rit = records.begin(); 
         rit != records.end(); ++rit)
      for (vector<Record>::iterator it = rit->begin(); it != rit->end(); ++it) {
        if (it->pt == Stem) {
          vector<ID> clss;
          for (SAT::Clauses::iterator cit = it->proof.begin(); 
               cit != it->proof.end(); ++cit)
            clss.push_back(ev->apply(Expr::Or, *cit));
          ID val = Expr::varSub(*ev, asgn, ev->apply(Expr::And, clss));
          assert (val == ev->btrue() || val == ev->bfalse());
          if (val == ev->bfalse())
            break;
        }
        if (!it->dup) {
          crec.push_back(*it);
          crec.back().dup = true;
        }
      }
    delete ev;
    unsigned int sz = crec.size();

    State st(m, opts, lasso, proofs, crec);

    if (st.m.verbosity() > Options::Terse) 
      cout << "FAIR: using " << sz << " previous proofs" << endl;
    
    MC::ReturnValue rv;
    if (st.trivial || check(st))
      rv.returnType = MC::Proof;
    else
      rv.returnType = MC::CEX;

    if (crec.size() > sz) records.push_back(crec);

    return rv;
  }

  MC::ReturnValue fairPath(Model & m, FairOptions & opts, Lasso * lasso,
                           vector<SAT::Clauses> * proofs) {

    MC::ReturnValue rv = check(m, opts, lasso, proofs);
    //Post-process proof

    return rv;
  }
}
