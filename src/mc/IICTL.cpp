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

#include "BMC.h"
#include "IICTL.h"
#include "Error.h"
#include "FCBMC.h"
#include "Util.h"

#define CNFIZE tseitin
//#define CNFIZE wilson

using namespace std;

namespace {

using namespace IICTL;

class CEX {
};

class Safe {
};

inline bool _IDVectorComp(const vector<ID> & v1, const vector<ID> & v2) {
  vector<ID>::const_iterator it1 = v1.begin(), it2 = v2.begin();
  for (; it1 != v1.end() && it2 != v2.end(); ++it1, ++it2) {
    if (*it1 < *it2) return true;
    if (*it1 > *it2) return false;
  }
  return (it1 == v1.end() && it2 != v2.end());
}

class IDVectorComp {
public:
  bool operator()(const vector<ID> & v1, const vector<ID> & v2) {
    return _IDVectorComp(v1, v2);
  }
};

typedef set<vector<ID>, IDVectorComp> CubeSet;

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

void primeVector(Expr::Manager::View & ev, const vector<ID> & in, vector<ID> & out) {
  for(vector<ID>::const_iterator it = in.begin(); it != in.end(); ++it) {
    if(*it != ev.btrue() && *it != ev.bfalse())
      out.push_back(ev.prime(*it));
    else
      out.push_back(*it);
  }
}

void primeCNF(Expr::Manager::View & ev, const vector< vector<ID> > & in, vector< vector<ID> > & out) {
  for(vector< vector<ID> >::const_iterator it = in.begin(); it != in.end(); ++it) {
    vector<ID> primed;
    primeVector(ev, *it, primed);
    out.push_back(primed);
  }
}

void resetAssign(SAT::Assignment & asgn) {
  for(SAT::Assignment::iterator it = asgn.begin(); it != asgn.end(); ++it) {
    it->second = SAT::Unknown;
  }
}

void fullAssignOf(Expr::Manager::View & ev, Model & m, SAT::Assignment & asgn, vector<ID> & cube, vector<ID> & inputCube) {
  ExprAttachment const * eat = (ExprAttachment *) m.constAttachment(Key::EXPR);
  for (SAT::Assignment::const_iterator it = asgn.begin(); it != asgn.end(); ++it) {
    if (it->second != SAT::Unknown) {
      if(eat->isInput(it->first)) {
        inputCube.push_back(it->second == SAT::False ?
                            ev.apply(Expr::Not, it->first) :
                            it->first);
      }
      else {
        cube.push_back(it->second == SAT::False ? 
                       ev.apply(Expr::Not, it->first) : 
                       it->first);
      }
    }
  }
  m.constRelease(eat);
}


void assignOf(Expr::Manager::View & ev, SAT::Assignment & asgn, vector<ID> & cube) {
  for(SAT::Assignment::const_iterator it = asgn.begin(); it != asgn.end(); ++it)
    if (it->second != SAT::Unknown)
      cube.push_back(it->second == SAT::False ? 
                     ev.apply(Expr::Not, it->first) : 
                     it->first);
}

void complement(Expr::Manager::View & ev, const vector<ID> & in,
                vector<ID> & out) {
  for (vector<ID>::const_iterator it = in.begin(); it != in.end(); ++it) {
    out.push_back(ev.apply(Expr::Not, *it));
  }
}

ID rep(Expr::Manager::View & ev, ID id) {
  static int stamp = 0;
  ostringstream buf;
  buf << "r";
  buf << id;
  buf << "n";
  buf << stamp++;
  ID newId = ev.newVar(buf.str());
  return newId;
}

enum Fairness {
  Fair,       //States satisfying the subformula are guaranteed to be fair
  Complement, //States not satisfying the subformula are guaranteed to be fair
  Unknown,    //No guarantees can be made about fairness of states
};

class StdTranslationFolder : public Expr::Manager::View::Folder {
public:
  StdTranslationFolder(Expr::Manager::View & v) :
    Expr::Manager::View::Folder(v) {}

  virtual ID fold(ID id, int n, const ID * const args) {

    Fairness nodeFairness;
    id = Expr::Manager::View::Folder::fold(id, n, args);
    Expr::Op op = view().op(id);
    switch(op) {
      case Expr::True:
      case Expr::Var:
        nodeFairness = Unknown;
        break;
      case Expr::Not: {
        assert(fairness.find(args[0]) != fairness.end());
        Fairness childFairness = fairness[args[0]];
        if(childFairness == Fair)
          nodeFairness = Complement;
        else if(childFairness == Complement)
          nodeFairness = Fair;
        else
          nodeFairness = Unknown;
        break;
      }
      case Expr::And: {
        assert(fairness.find(args[0]) != fairness.end());
        assert(fairness.find(args[1]) != fairness.end());
        Fairness child0Fairness = fairness[args[0]];
        Fairness child1Fairness = fairness[args[1]];
        if(child0Fairness == Fair || child1Fairness == Fair)
          nodeFairness = Fair;
        else if(child0Fairness == Unknown || child1Fairness == Unknown)
          nodeFairness = Unknown;
        else
          nodeFairness = Complement;
        break;
      }
      case Expr::X:
      case Expr::F: {
        assert(fairness.find(args[0]) != fairness.end());
        Fairness childFairness = fairness[args[0]];
        if(childFairness != Fair) {
          //Must conjoin EG T
          id = view().apply(op, view().apply(Expr::And,
            args[0], view().apply(Expr::G, view().btrue())));
        }
        nodeFairness = Fair;
        break;
      }
      case Expr::U: {
        assert(fairness.find(args[1]) != fairness.end());
        Fairness childFairness = fairness[args[1]];
        if(childFairness != Fair) {
          //Must conjoin EG T
          id = view().apply(op, args[0], view().apply(Expr::And,
            args[1], view().apply(Expr::G, view().btrue())));
        }
        nodeFairness = Fair;
        break;
      }
      case Expr::G:
        nodeFairness = Fair;
        break;
      default:
        assert(false);
    }
    fairness.insert(IDFairnessMap::value_type(id, nodeFairness));
    return id;
  }
 
private:
  typedef unordered_map<ID, Fairness> IDFairnessMap;
  IDFairnessMap fairness;
};

}

namespace IICTL {

class LabelInitFolder : public Expr::Manager::View::Folder {
public:
  LabelInitFolder(IICTLAction & _iictl, ExprAttachment const * const _eat) :
    Expr::Manager::View::Folder(*_iictl.ev), iictl(_iictl), eat(_eat) {}

  virtual ID fold(ID id, int n, const ID * const args) {
 
    //During initialization QLB => UB, and so, LB = QLB & UB = QLB
    switch(view().op(id)) {

    case Expr::True: {
      iictl.UBId.insert(IDMap::value_type(id, view().btrue()));
      iictl.QLBId.insert(IDMap::value_type(id, view().btrue()));

      //Create CNF
      SAT::Clauses clauses;
      clauses.push_back(SAT::Clause(1, view().btrue()));
      iictl.UB.insert(IDClausesMap::value_type(id, clauses));
      iictl.QLB.insert(IDClausesMap::value_type(id, clauses));

      iictl.boundsEqual.insert(IDBoolMap::value_type(id, true));
      break;
    }

    case Expr::Var: {
      ID fn;
      if(eat->isOutput(id))
        fn = eat->outputFnOf(id);
      else if(eat->isStateVar(id))
        fn = id;
      else
        assert(false);

      iictl.UBId.insert(IDMap::value_type(id, fn));
      iictl.QLBId.insert(IDMap::value_type(id, fn));

      //Create CNF
      SAT::Clauses fnCnf;
      Expr::CNFIZE(view(), fn, fnCnf);
      iictl.UB.insert(IDClausesMap::value_type(id, fnCnf));
      iictl.QLB.insert(IDClausesMap::value_type(id, fnCnf));

      iictl.boundsEqual.insert(IDBoolMap::value_type(id, true));
      break;
    }

    case Expr::Not: {
      //UB = !LB(child) = !QLB(child)
      assert(iictl.QLBId.find(args[0]) != iictl.QLBId.end());
      ID ubID = view().apply(Expr::Not, iictl.QLBId[args[0]]);
      iictl.UBId.insert(IDMap::value_type(id, ubID));

      SAT::Clauses ubCnf;
      Expr::CNFIZE(view(), ubID, ubCnf);
      iictl.UB.insert(IDClausesMap::value_type(id, ubCnf));
 
      //LB = QLB = !UB(child)
      assert(iictl.UBId.find(args[0]) != iictl.UBId.end());
      ID qlbID = view().apply(Expr::Not, iictl.UBId[args[0]]);
      iictl.QLBId.insert(IDMap::value_type(id, qlbID));

      SAT::Clauses qlbCnf;
      Expr::CNFIZE(view(), qlbID, qlbCnf);
      iictl.QLB.insert(IDClausesMap::value_type(id, qlbCnf));

      //Inherits equality of bounds
      assert(iictl.boundsEqual.find(args[0]) != iictl.boundsEqual.end());
      iictl.boundsEqual.insert(IDBoolMap::value_type(id, 
          iictl.boundsEqual[args[0]]));
      break;
    }

    case Expr::And: {
      ID conj1 = args[0];
      ID conj2 = args[1];
      assert(iictl.UBId.find(conj1) != iictl.UBId.end());
      assert(iictl.UBId.find(conj2) != iictl.UBId.end());

      //UB = UB1 & UB2
      ID ubID = view().apply(Expr::And, iictl.UBId[conj1], iictl.UBId[conj2]);
      iictl.UBId.insert(IDMap::value_type(id, ubID));
 
      //Create CNF
      SAT::Clauses ubCnf;
      Expr::CNFIZE(view(), ubID, ubCnf);
      iictl.UB.insert(IDClausesMap::value_type(id, ubCnf));

      assert(iictl.QLBId.find(conj1) != iictl.QLBId.end());
      assert(iictl.QLBId.find(conj2) != iictl.QLBId.end());

      //QLB = QLB1 & QLB2
      ID qlbID = view().apply(Expr::And, iictl.QLBId[conj1], iictl.QLBId[conj2]);
      iictl.QLBId.insert(IDMap::value_type(id, qlbID));

      //Create CNF
      SAT::Clauses qlbCnf;
      Expr::CNFIZE(view(), qlbID, qlbCnf);
      iictl.QLB.insert(IDClausesMap::value_type(id, qlbCnf));

      assert(iictl.boundsEqual.find(conj1) != iictl.boundsEqual.end());
      assert(iictl.boundsEqual.find(conj2) != iictl.boundsEqual.end());
      iictl.boundsEqual.insert(IDBoolMap::value_type(id, 
                                iictl.boundsEqual[conj1] &&
                                iictl.boundsEqual[conj2]));
      break;
    }

    case Expr::X: { //EX
      //UB = true
      iictl.UBId.insert(IDMap::value_type(id, view().btrue()));
      SAT::Clauses ubCnf;
      ubCnf.push_back(SAT::Clause(1, view().btrue()));
      iictl.UB.insert(IDClausesMap::value_type(id, ubCnf));

      //LB = QLB = false
      iictl.QLBId.insert(IDMap::value_type(id, view().bfalse()));
      iictl.baseQLB.insert(IDMap::value_type(id, view().bfalse()));
      SAT::Clauses qlbCnf;
      qlbCnf.push_back(SAT::Clause(1, view().bfalse()));
      iictl.QLB.insert(IDClausesMap::value_type(id, qlbCnf));

      iictl.QLBcubes.insert(IDCubesMap::value_type(id, vector< vector<ID> >()));

      //Add a SAT manager and a SAT view for this node for lifting
      //Lifting formula (eq 13):
      //GR & UB & !QLB & T & (!UB'[child] | !QLB'[child])
      //GR is inductive, and so is omitted from next state
      SAT::Manager * sman = iictl.model().newSATManager();
      //Add transition relation
      sman->add(iictl.tr);
      //GR, UB, and QLB are initially trivial, and last conjunct is added right
      //before generalization
      SAT::Manager::View * sview = sman->newView(view());
      iictl.liftSatViews.insert(IDSatViewMap::value_type(id, sview));

      iictl.boundsEqual.insert(IDBoolMap::value_type(id, false));
      break;
    }

    case Expr::F: { //EF
      //UB = true
      iictl.UBId.insert(IDMap::value_type(id, view().btrue()));
      SAT::Clauses ubCnf;
      ubCnf.push_back(SAT::Clause(1, view().btrue()));
      iictl.UB.insert(IDClausesMap::value_type(id, ubCnf));

      //LB = QLB = LB[child] = QLB[child]
      ID child = args[0];
      assert(iictl.QLBId.find(child) != iictl.QLBId.end());
      ID qlbID = iictl.QLBId[child];
      iictl.QLBId.insert(IDMap::value_type(id, qlbID));
      iictl.baseQLB.insert(IDMap::value_type(id, qlbID));
      assert(iictl.QLB.find(child) != iictl.QLB.end());
      iictl.QLB.insert(IDClausesMap::value_type(id, iictl.QLB[child]));

      iictl.QLBcubes.insert(IDCubesMap::value_type(id, vector< vector<ID> >()));
      
      //Add a SAT manager and a SAT view for this node for lifting
      //Lifting formula (eq 18):
      //GR & UB & !QLB & T & (!UB' | !QLB')
      SAT::Manager * sman = iictl.model().newSATManager();
      //Add transition relation
      sman->add(iictl.tr);
      SAT::Manager::View * sview = sman->newView(view());
      //Add !QLB
      SAT::Clauses notQLBCnf;
      Expr::CNFIZE(view(), view().apply(Expr::Not, qlbID), notQLBCnf);
      sview->add(notQLBCnf);
      //GR and UB are initially trivial, and last conjunct is added right
      //before generalization

      iictl.liftSatViews.insert(IDSatViewMap::value_type(id, sview));

      iictl.boundsEqual.insert(IDBoolMap::value_type(id, false));

      iictl.ic3Fail.insert(IDIntMap::value_type(id, 0));
      iictl.bmcFail.insert(IDIntMap::value_type(id, 0));
      break;
    }

    case Expr::G: { //EG
      //UB = UB[child]
      ID child = args[0];
      assert(iictl.UBId.find(child) != iictl.UBId.end());
      iictl.UBId.insert(IDMap::value_type(id, iictl.UBId[child]));
      assert(iictl.UB.find(child) != iictl.UB.end());
      iictl.UB.insert(IDClausesMap::value_type(id, iictl.UB[child]));

      //LB = QLB = false
      iictl.QLBId.insert(IDMap::value_type(id, view().bfalse()));
      iictl.baseQLB.insert(IDMap::value_type(id, view().bfalse()));
      SAT::Clauses lbCnf;
      lbCnf.push_back(SAT::Clause(1, view().bfalse()));
      iictl.QLB.insert(IDClausesMap::value_type(id, lbCnf));

      iictl.QLBcubes.insert(IDCubesMap::value_type(id, vector< vector<ID> >()));

      //Add a SAT manager and a SAT view for this node for lifting
      //Lifting formula (eq 18): TODO: Check formula
      //GR & UB & !QLB & T & (!UB' | !QLB')
      SAT::Manager * sman = iictl.model().newSATManager();
      //Add transition relation
      sman->add(iictl.tr);
      SAT::Manager::View * sview = sman->newView(view());
      //Add UB
      try {
        sview->add(iictl.UB[id]);
      }
      catch(SAT::Trivial tr) {
        //Do nothing. Will be handled later
      }
      iictl.liftSatViews.insert(IDSatViewMap::value_type(id, sview));

      iictl.boundsEqual.insert(IDBoolMap::value_type(id, false));

      iictl.ic3Fail.insert(IDIntMap::value_type(id, 0));
      iictl.bmcFail.insert(IDIntMap::value_type(id, 0));
      break;
    }

    case Expr::U: { //EpUq
      ID p = args[0];
      ID q = args[1];
      assert(iictl.UBId.find(p) != iictl.UBId.end());
      assert(iictl.UBId.find(q) != iictl.UBId.end());

      //UB = pUB | qUB
      ID ubID = view().apply(Expr::Or, iictl.UBId[p], iictl.UBId[q]);
      iictl.UBId.insert(IDMap::value_type(id, ubID));

      //Create CNF
      SAT::Clauses ubCnf;
      Expr::CNFIZE(view(), ubID, ubCnf);
      iictl.UB.insert(IDClausesMap::value_type(id, ubCnf));

      //LB = QLB & UB = qLB = qQLB & qUB = qQLB
      //QLB = qQLB
      assert(iictl.QLBId.find(q) != iictl.QLBId.end());
      iictl.QLBId.insert(IDMap::value_type(id, iictl.QLBId[q]));
      iictl.baseQLB.insert(IDMap::value_type(id, iictl.QLBId[q]));
      assert(iictl.QLB.find(q) != iictl.QLB.end());
      iictl.QLB.insert(IDClausesMap::value_type(id, iictl.QLB[q]));

      iictl.QLBcubes.insert(IDCubesMap::value_type(id, vector< vector<ID> >()));

      //Add a SAT manager and a SAT view for this node for lifting
      //Lifting formula (eq 18):
      //GR & UB & !QLB & T & (!UB' | !QLB')
      SAT::Manager * sman = iictl.model().newSATManager();
      //Add transition relation
      sman->add(iictl.tr);
      SAT::Manager::View * sview = sman->newView(view());
      //Add UB
      sview->add(ubCnf);
      //Add !QLB
      SAT::Clauses notQLBCnf;
      Expr::CNFIZE(view(), view().apply(Expr::Not, iictl.QLBId[id]), notQLBCnf);
      sview->add(notQLBCnf);
      iictl.liftSatViews.insert(IDSatViewMap::value_type(id, sview));

      iictl.boundsEqual.insert(IDBoolMap::value_type(id, false));

      iictl.ic3Fail.insert(IDIntMap::value_type(id, 0));
      iictl.bmcFail.insert(IDIntMap::value_type(id, 0));
      break;
    }

    default:
      assert(false);

    } //switch

    return id;
  }

private:
  IICTLAction & iictl;
  ExprAttachment const * const eat;
};

IICTLAction::~IICTLAction() {
  for(IDSatViewMap::iterator it = liftSatViews.begin();
      it != liftSatViews.end(); ++it) {
    SAT::Manager * sman = &(it->second->manager());
    delete it->second;
    delete sman;
  }
  delete ev;
  SAT::Manager * sman = &(faeSatView->manager());
  delete faeSatView;
  delete sman;
}

void IICTLAction::grabProperty() {
  ExprAttachment const * eat = (ExprAttachment const *) 
                               model().constAttachment(Key::EXPR);

  assert(eat->ctlProperties().size() == 1);
  property = eat->ctlProperties()[0];
  if(verbosity)
    cout << Expr::stringOf(*ev, property) << endl << endl;
  if(model().options().count("parse_graph") > 0) {
    std::stringstream title;
    title << "\"property\"";
    cout << Expr::dotOf(*ev, property, title.str()) << endl << endl;
  }
  model().constRelease(eat);
}

void IICTLAction::initializeLabels() {

  ExprAttachment const * eat = (ExprAttachment *)
                               model().constAttachment(Key::EXPR);
  LabelInitFolder initLabels(*this, eat);
  ev->fold(initLabels, property);
  model().constRelease(eat);
}

bool IICTLAction::lbContainsStates(ID id, const vector<ID> & state, vector<ID> * witness) {

  //Query s & !LB[id] = s & !(QLB[id] & UB[id]) = s & (!QLB[id] | !UB[id])
  //s => GR, so no need to include GR
  assert(QLBId.find(id) != QLBId.end());
  assert(UBId.find(id) != UBId.end());
  ID negLB = ev->apply(Expr::Or, ev->apply(Expr::Not, QLBId[id]),
                                 ev->apply(Expr::Not, UBId[id]));

  SAT::Manager * sman = model().newSATManager();
  SAT::Manager::View * sview = sman->newView(*ev);

  SAT::Clauses negLBCnf;
  Expr::CNFIZE(*ev, negLB, negLBCnf);
  try {
    sview->add(negLBCnf);
  }
  catch(SAT::Trivial tr) {
    delete sview;
    delete sman;
    return true;
  }

  vector<ID> stateCopy = state;
  resetAssign(stateAsgn);
  bool sat = sview->sat(&stateCopy, &stateAsgn);

  delete sview;
  delete sman;

  if(sat && witness) {
    assignOf(*ev, stateAsgn, *witness);
  }
  return !sat;
}

bool IICTLAction::ubContainsStates(ID id, const vector<ID> & state) {

  //Query: I & !UB[id]
  assert(UBId.find(id) != UBId.end());

  SAT::Manager * sman = model().newSATManager();
  SAT::Manager::View * sview = sman->newView(*ev);

  SAT::Clauses negUB;
  Expr::CNFIZE(*ev, ev->apply(Expr::Not, UBId[id]), negUB);

  try {
    sview->add(negUB);
  }
  catch(SAT::Trivial tr) {
    delete sview;
    delete sman;
    return true;
  }

  vector<ID> stateCopy = state;
  bool sat = sview->sat(&stateCopy);
  delete sview;
  delete sman;

  return !sat;
}


bool IICTLAction::lbContainsInitStates(vector<ID> & state) {

  if(verbosity > Options::Informative)
    cout << "Checking LB initiation:" << endl;
  
  return lbContainsStates(property, initialConditions, &state);
}

bool IICTLAction::ubContainsInitStates() {

  if(verbosity > Options::Informative)
    cout << "Checking UB initiation:" << endl;
  return ubContainsStates(property, initialConditions);
}

bool IICTLAction::liftEF(Transition & tr1, ID id, ID qlbRep, SAT::GID gid, bool addUnprimed) {

  vector<ID> assumps = tr1.inputs;
  assumps.insert(assumps.end(), tr1.state.begin(), tr1.state.end());

  unsigned size = tr1.state.size();

  assert(liftSatViews.find(id) != liftSatViews.end());
  SAT::Manager::View * liftSatView = liftSatViews[id];

  bool sat = liftSatView->sat(&assumps, NULL, &assumps);
  assert(!sat);

  tr1.state.clear();
  ExprAttachment const * eat = (ExprAttachment *) model().constAttachment(Key::EXPR);
  for(vector<ID>::const_iterator it = assumps.begin(); it != assumps.end(); ++it) {
    if(eat->isStateVar(*it) || eat->isStateVar(ev->apply(Expr::Not, *it))) {
      tr1.state.push_back(*it);
    }
  }
  model().constRelease(eat);

  //Add negation of lifted cube to SAT database (in unprimed and primed forms)
  if(tr1.state.size() < size) {
    SAT::Clause cls;
    complement(*ev, tr1.state, cls);
    if(addUnprimed)
      liftSatView->add(cls);
    SAT::Clause primedCls;
    primeVector(*ev, cls, primedCls);
    //Add activation literal
    primedCls.push_back(ev->apply(Expr::Not, qlbRep));
    liftSatView->add(primedCls, gid);
    return true;
  }
  return false;
}

bool IICTLAction::liftEX(Transition & tr1, ID id) {

  SAT::Manager::View * liftSatView = liftSatViews[id];
  vector<ID> assumps = tr1.inputs;
  assumps.insert(assumps.end(), tr1.state.begin(), tr1.state.end());

  unsigned size = tr1.state.size();

  bool sat = liftSatView->sat(&assumps, NULL, &assumps);
  assert(!sat);

  tr1.state.clear();
  ExprAttachment const * eat = (ExprAttachment *) model().constAttachment(Key::EXPR);
  for(vector<ID>::const_iterator it = assumps.begin(); it != assumps.end(); ++it) {
    if(eat->isStateVar(*it) || eat->isStateVar(ev->apply(Expr::Not, *it))) {
      tr1.state.push_back(*it);
    }
  }
  model().constRelease(eat);

  if(tr1.state.size() < size)
    return true;
  return false;
}


bool IICTLAction::bruteForceLiftEF(Transition & tr1, ID id, ID qlbRep, SAT::GID gid, bool addUnprimed) {

  assert(liftSatViews.find(id) != liftSatViews.end());
  SAT::Manager::View * liftSatView = liftSatViews[id];

  ExprAttachment const * eat = (ExprAttachment *) model().constAttachment(Key::EXPR);
  vector<ID> cube = tr1.state;
  for(unsigned i = 0; i < cube.size(); ++i) {
    vector<ID> rcube;
    for(unsigned j = 0; j < cube.size(); ++j) {
      if(j != i) {
        rcube.push_back(cube[j]);
      }
    }
    //Check if is still UNSAT
    vector<ID> assumps = tr1.inputs;
    assumps.insert(assumps.end(), rcube.begin(), rcube.end());
    bool sat = liftSatView->sat(&assumps, NULL, &assumps);
    if(!sat) {
      cube.clear();
      for(vector<ID>::const_iterator it = assumps.begin(); it != assumps.end(); ++it) {
        if(eat->isStateVar(*it) || eat->isStateVar(ev->apply(Expr::Not, *it))) {
          cube.push_back(*it);
        }
      }
      --i;
      //Add negation of lifted cube to SAT database (in unprimed and primed
      //forms) and to QLBcubes
      SAT::Clause cls;
      complement(*ev, cube, cls);
      if(addUnprimed)
        liftSatView->add(cls);
      SAT::Clause primedCls;
      primeVector(*ev, cls, primedCls);
      //Add activation literal
      primedCls.push_back(ev->apply(Expr::Not, qlbRep));
      liftSatView->add(primedCls, gid);
    }
  }
  bool changed = false;
  if(cube.size() < tr1.state.size())
    changed = true;
  tr1.state = cube;
  model().constRelease(eat);
  return changed;
}

bool IICTLAction::bruteForceLiftEX(Transition & tr1, ID id) {

  SAT::Manager::View * liftSatView = liftSatViews[id];

  ExprAttachment const * eat = (ExprAttachment *) model().constAttachment(Key::EXPR);
  vector<ID> cube = tr1.state;
  for(unsigned i = 0; i < cube.size(); ++i) {
    vector<ID> rcube;
    for(unsigned j = 0; j < cube.size(); ++j) {
      if(j != i) {
        rcube.push_back(cube[j]);
      }
    }
    //Check if is still UNSAT
    vector<ID> assumps = tr1.inputs;
    assumps.insert(assumps.end(), rcube.begin(), rcube.end());
    bool sat = liftSatView->sat(&assumps, NULL, &assumps);
    if(!sat) {
      cube.clear();
      for(vector<ID>::const_iterator it = assumps.begin(); it != assumps.end(); ++it) {
        if(eat->isStateVar(*it) || eat->isStateVar(ev->apply(Expr::Not, *it))) {
          cube.push_back(*it);
        }
      }
      --i;
    }
  }
  bool changed = false;
  if(cube.size() < tr1.state.size())
    changed = true;
  tr1.state = cube;
  model().constRelease(eat);
  return changed;
}

bool IICTLAction::forAllExistsEF(Transition & tr1, SAT::Clauses & q2clauses, ID id, ID qlbRep, SAT::GID gid, ID tmpQLB, const SAT::Clauses & ubPrimed, bool reach, bool ic3) {

  int numCalls = 0;
  int numSuccess = 0;
  int numFailed = 0;
  int numTimeout = 0;
  int numPrevCTG = 0;

  bool changed = false;
  int verb = 0;
  if(model().options().count("iictl_verbosity"))
    verb = model().options()["iictl_verbosity"].as<int>();

  if(verb > Options::Verbose) {
    cout << "Starting forall-exists procedure with " << tr1.state.size()
         << " literals" << endl;
  }

  vector<ID> s_bar = tr1.state;
  /*
  cout << "Before shuffling" << endl;
  for(vector<ID>::const_iterator it = s_bar.begin(); it != s_bar.end(); ++it) {
    cout << *it << " ";
  }
  cout << endl;
  */
  random_shuffle(s_bar.begin(), s_bar.end());
  /*
  cout << "After shuffling" << endl;
  for(vector<ID>::const_iterator it = s_bar.begin(); it != s_bar.end(); ++it) {
    cout << *it << " ";
  }
  cout << endl;
  */
  int numDropped = 0;

  assert(liftSatViews.find(id) != liftSatViews.end());
  SAT::Manager::View * liftSatView = liftSatViews[id];
  for(unsigned i = 0; i < s_bar.size(); ++i) {
    if(verb > Options::Verbose)
      cout << "Attempting to drop literal from cube" << endl;
    int numQueries = 1;
    bool dropLit;
    bool bad = false;
    s_bar[i] = ev->apply(Expr::Not, s_bar[i]);

    //Look at the current CTGs that satisfy s_bar
    for(IC3::CubeSet::const_iterator it = ctgs.begin(); it != ctgs.end();) {
      set<ID> ctgLits;
      ctgLits.insert(it->begin(), it->end());
      bool isSbar = true;
      for(vector<ID>::const_iterator it2 = s_bar.begin(); it2 != s_bar.end(); ++it2) {
        if(ctgLits.find(ev->apply(Expr::Not, *it2)) != ctgLits.end()) {
          isSbar = false;
          break;
        }
      }
      if(isSbar) {
        if(verb > Options::Verbose)
          cout << "Cube has a previous CTG that ";
        //Check if CTG still lacks an L-successor
        SAT::GID faegid = faeSatView->newGID();
        faeSatView->add(q2clauses, faegid);
        vector<ID> assumps2 = *it;
        resetAssign(fullAsgn);
        bool sat = faeSatView->sat(&assumps2, &fullAsgn);
        faeSatView->remove(faegid);
        if(!sat) {
          //Still lacks an L-successor. Dropping literal is not going to work.
          if(verb > Options::Verbose)
            cout << "still lacks an L-successor. Cannot drop literal" << endl;
          ++numPrevCTG;
          bad = true;
          break;
        }
        else {
          if(verb > Options::Verbose)
            cout << "no longer lacks an L-successor! " << endl;
          //Remove from CTG list
          ctgs.erase(it++);
          //Lift and add
          Transition tr;
          fullAssignOf(*ev, model(), fullAsgn, tr.state, tr.inputs);
          liftEF(tr, id, qlbRep, gid, true);
          bruteForceLiftEF(tr, id, qlbRep, gid, true);
          QLBcubes[id].push_back(tr.state);
 
          //Add to q2clauses (in primed form)
          vector<ID> prcube;
          primeVector(*ev, tr.state, prcube);
          tmpQLB = disjoinCube(tmpQLB, prcube);
          q2clauses = ubPrimed;
          Expr::CNFIZE(*ev, tmpQLB, q2clauses);
        }
      }
      else {
        ++it;
      }
    }
    if(bad) {
      s_bar[i] = ev->apply(Expr::Not, s_bar[i]);
      continue;
    }

    vector<ID> assumps = s_bar;
    while(true) {
      resetAssign(fullAsgn);
      bool sat = liftSatView->sat(&assumps, &fullAsgn);
      if(!sat) {
        if(verb > Options::Verbose)
          cout << "Dropping literal was successful" << endl;
        dropLit = true;
        ++numDropped;
        break;
      }
      else {
        Transition tr;
        fullAssignOf(*ev, model(), fullAsgn, tr.state, tr.inputs);
        SAT::GID faegid = faeSatView->newGID();
        faeSatView->add(q2clauses, faegid);
        //T & L'
        vector<ID> assumps2 = tr.state;
        resetAssign(fullAsgn);
        bool sat = faeSatView->sat(&assumps2, &fullAsgn);
        faeSatView->remove(faegid);
        //T
        if(!sat) {
          if(!reach) {
            dropLit = false;
            break;
          }
          else if(haveExactRch) {
            //This is a true CTG
            ctgs.insert(tr.state);
            dropLit = false;
            break;
          }
          else {
            //As a last resort, check if the CTG state is reachable
            //Save model state
            ExprAttachment * eat = (ExprAttachment *) model().attachment(Key::EXPR);
            vector<ID> init(eat->initialConditions());
            eat->clearInitialConditions();
            eat->addInitialConditions(initialConditions);
            vector<ID> outputs = eat->outputs();
            vector<ID> outputFns = eat->outputFns();
            eat->clearOutputFns();
            ID o0 = ev->newVar("ooo");
            ID nfn0 = ev->apply(Expr::And, tr.state);
            eat->setOutputFn(o0, nfn0);
            model().release(eat);

            ++numCalls;
            if(ic3) {
              vector<SAT::Clauses> constraints(1, GR);
              _opts->ic3_opts.constraints = &constraints;
              _opts->ic3_opts.iictl = false;
              _opts->ic3_opts.printCex = true;
              _opts->ic3_opts.proofProc = IC3::STRENGTHEN;
              MC::ReturnValue rv;
              vector<SAT::Clauses> proofs;
              vector<Transition> cex;
              _opts->ic3_opts.timeout = model().options()["iictl_ic3timeout"].as<int>();
              _opts->ic3_opts.silent = true;
              if(verb > Options::Verbose) {
                cout << "IC3 Query " << numQueries++ << ": Checking if CTG is reachable: ";
                cout.flush();
              }
              _opts->ic3_opts.propagate = !model().options().count("iictl_xic3propagate");
              IC3::CubeSet indCubes;
              rv = IC3::reach2(model(), _opts->ic3_opts, &cex, &proofs, NULL, NULL, &indCubes);
              _opts->ic3_opts.constraints = NULL;
              _opts->ic3_opts.propagate = false;
              _opts->ic3_opts.timeout = -1;
              _opts->ic3_opts.silent = false;
              //Restore model state
              eat = (ExprAttachment *) model().attachment(Key::EXPR);
              eat->clearInitialConditions();
              eat->addInitialConditions(init);
              eat->clearOutputFns();
              eat->setOutputFns(outputs, outputFns);
              model().release(eat);

              if(rv.returnType != MC::Proof) {
                if(verb > Options::Verbose) {
                  cout << (rv.returnType == MC::CEX ? "Reachable!" : "Timeout") << endl;
                  cout << "Dropping literal failed" << endl;
                }
                if(rv.returnType == MC::CEX) {
                  ++numFailed;
                  //Add all states in counterexample trace to CTG list
                  for(vector<Transition>::const_iterator it = cex.begin();
                      it != cex.end(); ++it) {
                    ctgs.insert(it->state);
                  }
                  for(IC3::CubeSet::const_iterator it = indCubes.begin(); it != indCubes.end(); ++it) {
                    SAT::Clause cls;
                    complement(*ev, *it, cls);
                    GR.push_back(cls);
                    for(IDSatViewMap::iterator it = liftSatViews.begin();
                        it != liftSatViews.end(); ++it) {
                      it->second->add(cls);
                    }
                  }
                }
                else
                  ++numTimeout;
                dropLit = false;
                break;
              }
              else {
                ++numSuccess;
                if(verb > Options::Verbose)
                  cout << "Unreachable!" << endl;
                //Add proof to global reachability information
                GR.insert(GR.end(), proofs[0].begin(), proofs[0].end());

                //Add new global reachability info to all lift SAT databases
                for(IDSatViewMap::iterator it = liftSatViews.begin();
                    it != liftSatViews.end(); ++it) {
                  it->second->add(proofs[0]);
                }
              }
            }
            else {
              _opts->ic3_opts.iictl = false;
              _opts->ic3_opts.silent = true;
              if(verb > Options::Verbose) {
                cout << "MIC Query " << numQueries++ << ": Checking if a subclause of the cube negation is inductive: ";
                cout.flush();
              }
              bool success = mic(model(), _opts->ic3_opts, tr.state);
              //Restore model state
              _opts->ic3_opts.silent = false;
              eat = (ExprAttachment *) model().attachment(Key::EXPR);
              eat->clearInitialConditions();
              eat->addInitialConditions(init);
              eat->clearOutputFns();
              eat->setOutputFns(outputs, outputFns);
              model().release(eat);
              if(success) {
                ++numSuccess;
                if(verb > Options::Verbose)
                  cout << "Inductive subclause found!" << endl;
                SAT::Clause cls;
                complement(*ev, tr.state, cls);
                GR.push_back(cls);
                for(IDSatViewMap::iterator it = liftSatViews.begin();
                    it != liftSatViews.end(); ++it) {
                  it->second->add(cls);
                }

              }
              else {
                ++numFailed;
                if(verb > Options::Verbose) {
                  cout << "No inductive subclause found!" << endl;
                  cout << "Dropping literal failed" << endl;
                }
                dropLit = false;
                break;
              }
            }
            
          }
        }
        else {
          tr.state.clear();
          tr.inputs.clear();
          fullAssignOf(*ev, model(), fullAsgn, tr.state, tr.inputs);
          liftEF(tr, id, qlbRep, gid, true);
          bruteForceLiftEF(tr, id, qlbRep, gid, true);
          //Blocking clause has been added to lift SAT database inside the
          //lifting and brute-force lifting functions
          //Add to QLBcubes
          QLBcubes[id].push_back(tr.state);

          //Add to q2clauses (in primed form)
          vector<ID> prcube;
          primeVector(*ev, tr.state, prcube);
          tmpQLB = disjoinCube(tmpQLB, prcube);
          q2clauses = ubPrimed;
          Expr::CNFIZE(*ev, tmpQLB, q2clauses);
        }
      }
    }
    
    if(!dropLit) {
      s_bar[i] = ev->apply(Expr::Not, s_bar[i]);
    }
    else {
      changed = true;
      vector<ID> newCube;
      for(unsigned j = 0; j < s_bar.size(); ++j) {
        if(j != i)
          newCube.push_back(s_bar[j]);
      }
      //Extract the UNSAT core from a query on the resolvent
      //bool sat = liftSatView->sat(&newCube, NULL, &newCube);
      //assert(!sat);

      //Add new cube to q2clauses (in primed form)
      vector<ID> prnewcube;
      primeVector(*ev, newCube, prnewcube);
      tmpQLB = disjoinCube(tmpQLB, prnewcube);
      q2clauses = ubPrimed;
      Expr::CNFIZE(*ev, tmpQLB, q2clauses);

      //Add cube to the lifting SAT database (in unprimed and primed forms)
      SAT::Clause c;
      complement(*ev, newCube, c);
      liftSatView->add(c);
      SAT::Clause pc;
      primeVector(*ev, c, pc);
      pc.push_back(ev->apply(Expr::Not, qlbRep));
      liftSatView->add(pc, gid);
      s_bar = newCube;
      if(model().options().count("iictl_interlv_blift"))
        break;
      //Keep order
/*
      for(unsigned j = 0; j < s_bar.size(); ++j) {
        if(j != i && 
      }
*/
      --i;
    }
  }
  tr1.state = s_bar;
  sort(tr1.state.begin(), tr1.state.end());
  if(verb > Options::Verbose) {
    cout << "Forall-exists procedure: dropped " << numDropped
         << " literals" << endl;
  }
  if(verbosity > Options::Verbose) {
    cout << numCalls << (ic3 ? " IC3" : " MIC") << " queries, " << numSuccess << " inductive, " << numFailed << " not inductive, " << numTimeout << " timeouts, " << numPrevCTG << " prev CTGs. " << endl;
  }
  return changed;
}

bool IICTLAction::forAllExistsEG(Transition & tr1, SAT::Clauses & q3clauses, ID id, ID qlbRep, SAT::GID gid, SAT::Manager::View * q2, ID tmpQLB, const SAT::Clauses & ubPrimed, bool reach, bool ic3) {

  int numCalls = 0;
  int numSuccess = 0;
  int numFailed = 0;
  int numTimeout = 0;
  int numPrevCTG = 0;

  bool changed = false;
  int verb = 0;
  if(model().options().count("iictl_verbosity"))
    verb = model().options()["iictl_verbosity"].as<int>();

  if(verb > Options::Verbose) {
    cout << "Starting forall-exists procedure with " << tr1.state.size()
         << " literals" << endl;
  }

  vector<ID> s_bar = tr1.state;
  /*
  cout << "Before shuffling" << endl;
  for(vector<ID>::const_iterator it = s_bar.begin(); it != s_bar.end(); ++it) {
    cout << *it << " ";
  }
  cout << endl;
  */
  random_shuffle(s_bar.begin(), s_bar.end());
  /*
  cout << "After shuffling" << endl;
  for(vector<ID>::const_iterator it = s_bar.begin(); it != s_bar.end(); ++it) {
    cout << *it << " ";
  }
  cout << endl;
  */
  int numDropped = 0;

  assert(liftSatViews.find(id) != liftSatViews.end());
  SAT::Manager::View * liftSatView = liftSatViews[id];
  for(unsigned i = 0; i < s_bar.size(); ++i) {
    if(verb > Options::Verbose)
      cout << "Attempting to drop literal from cube" << endl;
    int numQueries = 1;
    bool dropLit;
    bool bad = false;
    s_bar[i] = ev->apply(Expr::Not, s_bar[i]);

    //Look at the current CTGs that satisfy s_bar
    for(IC3::CubeSet::const_iterator it = ctgs.begin(); it != ctgs.end();) {
      set<ID> ctgLits;
      ctgLits.insert(it->begin(), it->end());
      bool isSbar = true;
      for(vector<ID>::const_iterator it2 = s_bar.begin(); it2 != s_bar.end(); ++it2) {
        if(ctgLits.find(ev->apply(Expr::Not, *it2)) != ctgLits.end()) {
          isSbar = false;
          break;
        }
      }
      if(isSbar) {
        if(verb > Options::Verbose)
          cout << "Cube has a previous CTG that ";
        //Check if CTG is no longer a CTG which happens if:
        //1) q2 is UNSAT
        //2) q3 is SAT
        vector<ID> assumps2 = *it;
        bool sat;
        if(q2) {
          sat = q2->sat(&assumps2);
          if(sat) {
            if(verb > Options::Verbose)
              cout << "still lacks an L-successor. Cannot drop literal" << endl;
            ++numPrevCTG;
            bad = true;
            break;
          }
        }
        //q2 is UNSAT
        SAT::GID faegid = faeSatView->newGID();
        faeSatView->add(q3clauses, faegid);
        resetAssign(fullAsgn);
        sat = faeSatView->sat(&assumps2, &fullAsgn);
        faeSatView->remove(faegid);
        if(!sat) {
          //Still lacks an L-successor. Dropping literal is not going to work.
          if(verb > Options::Verbose)
            cout << "still lacks an L-successor. Cannot drop literal" << endl;
          ++numPrevCTG;
          bad = true;
          break;

        }
        else {
          if(verb > Options::Verbose)
            cout << "no longer lacks an L-successor! " << endl;
          //Remove from CTG list
          ctgs.erase(it++);
          //Lift and add
          Transition tr;
          fullAssignOf(*ev, model(), fullAsgn, tr.state, tr.inputs);
          liftEF(tr, id, qlbRep, gid, true);
          bruteForceLiftEF(tr, id, qlbRep, gid, true);
          QLBcubes[id].push_back(tr.state);
 
          //Add to q3clauses (in primed form)
          vector<ID> prcube;
          primeVector(*ev, tr.state, prcube);
          tmpQLB = disjoinCube(tmpQLB, prcube);
          q3clauses = ubPrimed;
          Expr::CNFIZE(*ev, tmpQLB, q3clauses);
        }
      }
      else {
        ++it;
      }
    }
    if(bad) {
      s_bar[i] = ev->apply(Expr::Not, s_bar[i]);
      continue;
    }

    vector<ID> assumps = s_bar;
    while(true) {
      resetAssign(fullAsgn);
      bool sat = liftSatView->sat(&assumps, &fullAsgn);
      if(!sat) {
        if(verb > Options::Verbose)
          cout << "Dropping literal was successful" << endl;
        dropLit = true;
        ++numDropped;
        break;
      }
      else {
        Transition tr;
        fullAssignOf(*ev, model(), fullAsgn, tr.state, tr.inputs);
        //Check q2 first
        vector<ID> assumps2 = tr.state;
        bool q2sat = false;
        if(q2)
          q2sat = q2->sat(&assumps2);
        bool q3sat;
        if(!q2sat) {
          SAT::GID faegid = faeSatView->newGID();
          faeSatView->add(q3clauses, faegid);
          //T & L'
          resetAssign(fullAsgn);
          q3sat = faeSatView->sat(&assumps2, &fullAsgn);
          faeSatView->remove(faegid);
          //T
        }
        if(q2sat || !q3sat) {
          if(!reach) {
            dropLit = false;
            break;
          }
          else if(haveExactRch) {
            //This is a true CTG
            ctgs.insert(tr.state);
            dropLit = false;
            break;
          }
          else {
            //As a last resort, check if the CTG state is reachable
            //Save model state
            ExprAttachment * eat = (ExprAttachment *) model().attachment(Key::EXPR);
            vector<ID> init(eat->initialConditions());
            eat->clearInitialConditions();
            eat->addInitialConditions(initialConditions);
            vector<ID> outputs = eat->outputs();
            vector<ID> outputFns = eat->outputFns();
            eat->clearOutputFns();
            ID o0 = ev->newVar("ooo");
            ID nfn0 = ev->apply(Expr::And, tr.state);
            eat->setOutputFn(o0, nfn0);
            model().release(eat);

            ++numCalls;
            if(ic3) {
              vector<SAT::Clauses> constraints(1, GR);
              _opts->ic3_opts.constraints = &constraints;
              _opts->ic3_opts.iictl = false;
              _opts->ic3_opts.printCex = true;
              _opts->ic3_opts.proofProc = IC3::STRENGTHEN;
              MC::ReturnValue rv;
              vector<SAT::Clauses> proofs;
              vector<Transition> cex;
              _opts->ic3_opts.timeout = model().options()["iictl_ic3timeout"].as<int>();
              _opts->ic3_opts.silent = true;
              if(verb > Options::Verbose) {
                cout << "IC3 Query " << numQueries++ << ": Checking if CTG is reachable: ";
                cout.flush();
              }
              _opts->ic3_opts.propagate = !model().options().count("iictl_xic3propagate");
              IC3::CubeSet indCubes;
              rv = IC3::reach2(model(), _opts->ic3_opts, &cex, &proofs, NULL, NULL, &indCubes);
              _opts->ic3_opts.constraints = NULL;
              _opts->ic3_opts.propagate = false;
              _opts->ic3_opts.timeout = -1;
              _opts->ic3_opts.silent = false;
              //Restore model state
              eat = (ExprAttachment *) model().attachment(Key::EXPR);
              eat->clearOutputFns();
              eat->setOutputFns(outputs, outputFns);
              eat->clearInitialConditions();
              eat->addInitialConditions(init);
              model().release(eat);

              if(rv.returnType != MC::Proof) {
                if(verb > Options::Verbose) {
                  cout << (rv.returnType == MC::CEX ? "Reachable!" : "Timeout") << endl;
                  cout << "Dropping literal failed" << endl;
                }
                if(rv.returnType == MC::CEX) {
                  ++numFailed;
                  //Add all states in counterexample trace to CTG list
                  for(vector<Transition>::const_iterator it = cex.begin();
                      it != cex.end(); ++it) {
                    ctgs.insert(it->state);
                  }
                  for(IC3::CubeSet::const_iterator it = indCubes.begin(); it != indCubes.end(); ++it) {
                    SAT::Clause cls;
                    complement(*ev, *it, cls);
                    GR.push_back(cls);
                    for(IDSatViewMap::iterator it = liftSatViews.begin();
                        it != liftSatViews.end(); ++it) {
                      it->second->add(cls);
                    }
                  }
                }
                else
                  ++numTimeout;
                dropLit = false;
                break;
              }
              else {
                ++numSuccess;
                if(verb > Options::Verbose)
                  cout << "Unreachable!" << endl;
                //Add proof to global reachability information
                GR.insert(GR.end(), proofs[0].begin(), proofs[0].end());

                //Add new global reachability info to all lift SAT databases
                for(IDSatViewMap::iterator it = liftSatViews.begin();
                    it != liftSatViews.end(); ++it) {
                  it->second->add(proofs[0]);
                }
              }
            }
            else {
              _opts->ic3_opts.iictl = false;
              _opts->ic3_opts.silent = true;
              if(verb > Options::Verbose) {
                cout << "MIC Query " << numQueries++ << ": Checking if a subclause of the cube negation is inductive: ";
                cout.flush();
              }
              bool success = mic(model(), _opts->ic3_opts, tr.state);
              //Restore model state
              _opts->ic3_opts.silent = false;
              eat = (ExprAttachment *) model().attachment(Key::EXPR);
              eat->clearInitialConditions();
              eat->addInitialConditions(init);
              eat->clearOutputFns();
              eat->setOutputFns(outputs, outputFns);
              model().release(eat);
              if(success) {
                ++numSuccess;
                if(verb > Options::Verbose)
                  cout << "Inductive subclause found!" << endl;
                SAT::Clause cls;
                complement(*ev, tr.state, cls);
                GR.push_back(cls);
                for(IDSatViewMap::iterator it = liftSatViews.begin();
                    it != liftSatViews.end(); ++it) {
                  it->second->add(cls);
                }

              }
              else {
                ++numFailed;
                if(verb > Options::Verbose) {
                  cout << "No inductive subclause found!" << endl;
                  cout << "Dropping literal failed" << endl;
                }
                dropLit = false;
                break;
              }
            }
            
          }
        }
        else {
          tr.state.clear();
          tr.inputs.clear();
          fullAssignOf(*ev, model(), fullAsgn, tr.state, tr.inputs);
          liftEF(tr, id, qlbRep, gid, true);
          bruteForceLiftEF(tr, id, qlbRep, gid, true);
          //Blocking clause has been added to lift SAT database inside the
          //lifting and brute-force lifting functions
          //Add to QLBcubes
          QLBcubes[id].push_back(tr.state);

          //Add to q3clauses (in primed form)
          vector<ID> prcube;
          primeVector(*ev, tr.state, prcube);
          tmpQLB = disjoinCube(tmpQLB, prcube);
          q3clauses = ubPrimed;
          Expr::CNFIZE(*ev, tmpQLB, q3clauses);
        }
      }
    }
    
    if(!dropLit) {
      s_bar[i] = ev->apply(Expr::Not, s_bar[i]);
    }
    else {
      changed = true;
      vector<ID> newCube;
      for(unsigned j = 0; j < s_bar.size(); ++j) {
        if(j != i)
          newCube.push_back(s_bar[j]);
      }
      //Extract the UNSAT core from a query on the resolvent
      //bool sat = liftSatView->sat(&newCube, NULL, &newCube);
      //assert(!sat);

      //Add new cube to q3clauses (in primed form)
      vector<ID> prnewcube;
      primeVector(*ev, newCube, prnewcube);
      tmpQLB = disjoinCube(tmpQLB, prnewcube);
      q3clauses = ubPrimed;
      Expr::CNFIZE(*ev, tmpQLB, q3clauses);
      //Add cube to the lifting SAT database (in unprimed and primed forms)
      SAT::Clause c;
      complement(*ev, newCube, c);
      liftSatView->add(c);
      SAT::Clause pc;
      primeVector(*ev, c, pc);
      pc.push_back(ev->apply(Expr::Not, qlbRep));
      liftSatView->add(pc, gid);
      s_bar = newCube;
      if(model().options().count("iictl_interlv_blift"))
        break;
      //Keep order
/*
      for(unsigned j = 0; j < s_bar.size(); ++j) {
        if(j != i && 
      }
*/
      --i;
    }
  }
  tr1.state = s_bar;
  sort(tr1.state.begin(), tr1.state.end());
  if(verb > Options::Verbose) {
    cout << "Forall-exists procedure: dropped " << numDropped
         << " literals" << endl;
  }
  if(verbosity > Options::Verbose) {
    cout << numCalls << (ic3 ? " IC3" : " MIC") << " queries, " << numSuccess << " inductive, " << numFailed << " not inductive, " << numTimeout << " timeouts, " << numPrevCTG << " prev CTGs. " << endl;
  }
  return changed;
}


bool IICTLAction::forAllExistsEX(Transition & tr1, ID id, bool reach, bool ic3) {

  int numCalls = 0;
  int numSuccess = 0;
  int numFailed = 0;
  int numTimeout = 0;
  int numPrevCTG = 0;
 
  assert(liftSatViews.find(id) != liftSatViews.end());
  SAT::Manager::View * liftSatView = liftSatViews[id];

  bool changed = false;
  int verb = 0;
  if(model().options().count("iictl_verbosity"))
    verb = model().options()["iictl_verbosity"].as<int>();

  if(verb > Options::Verbose) {
    cout << "Starting forall-exists procedure with " << tr1.state.size()
         << " literals" << endl;
  }

  vector<ID> s_bar = tr1.state;
  random_shuffle(s_bar.begin(), s_bar.end());
  int numDropped = 0;

  for(unsigned i = 0; i < s_bar.size(); ++i) {
    if(verb > Options::Verbose)
      cout << "Attempting to drop literal from cube" << endl;
    int numQueries = 1;
    bool dropLit;
    bool bad = false;
    s_bar[i] = ev->apply(Expr::Not, s_bar[i]);

    //Look at the current CTGs that satisfy s_bar
    for(IC3::CubeSet::const_iterator it = ctgs.begin(); it != ctgs.end();) {
      set<ID> ctgLits;
      ctgLits.insert(it->begin(), it->end());
      bool isSbar = true;
      for(vector<ID>::const_iterator it2 = s_bar.begin(); it2 != s_bar.end(); ++it2) {
        if(ctgLits.find(ev->apply(Expr::Not, *it2)) != ctgLits.end()) {
          isSbar = false;
          break;
        }
      }
      if(isSbar) {
        if(verb > Options::Verbose)
          cout << "Cube has a previous CTG that ";
        //Check if CTG still lacks an L-successor
        vector<ID> assumps2 = *it;
        resetAssign(fullAsgn);
        bool sat = faeSatView->sat(&assumps2, &fullAsgn);
        if(!sat) {
          //Still lacks an L-successor. Dropping literal is not going to work.
          if(verb > Options::Verbose)
            cout << "still lacks an L-successor. Cannot drop literal" << endl;
          ++numPrevCTG;
          bad = true;
          break;
        }
        else {
          if(verb > Options::Verbose)
            cout << "no longer lacks an L-successor! " << endl;
          //Remove from CTG list
          ctgs.erase(it++);
          //Lift and add as a blocking clause (unprimed)
          Transition tr;
          fullAssignOf(*ev, model(), fullAsgn, tr.state, tr.inputs);
          liftEX(tr, id);
          bruteForceLiftEX(tr, id);
          SAT::Clause cls;
          complement(*ev, tr.state, cls);
          liftSatView->add(cls);
          QLBcubes[id].push_back(tr.state);
        }
      }
      else {
        ++it;
      }
    }
    if(bad) {
      s_bar[i] = ev->apply(Expr::Not, s_bar[i]);
      continue;
    }

    vector<ID> assumps = s_bar;
    while(true) {
      resetAssign(fullAsgn);
      bool sat = liftSatView->sat(&assumps, &fullAsgn);
      if(!sat) {
        if(verb > Options::Verbose)
          cout << "Dropping literal was successful" << endl;
        dropLit = true;
        ++numDropped;
        break;
      }
      else {
        Transition tr;
        fullAssignOf(*ev, model(), fullAsgn, tr.state, tr.inputs);
        //T & L'
        vector<ID> assumps2 = tr.state;
        resetAssign(fullAsgn);
        bool sat = faeSatView->sat(&assumps2, &fullAsgn);
        //T
        if(!sat) {
          if(!reach) {
            dropLit = false;
            break;
          }
          else if(haveExactRch) {
            //This is a true CTG
            ctgs.insert(tr.state);
            dropLit = false;
            break;
          }
          else {
            //As a last resort, check if the CTG state is reachable
            //Save model state
            ExprAttachment * eat = (ExprAttachment *) model().attachment(Key::EXPR);
            vector<ID> init(eat->initialConditions());
            eat->clearInitialConditions();
            eat->addInitialConditions(initialConditions);
            vector<ID> outputs = eat->outputs();
            vector<ID> outputFns = eat->outputFns();
            eat->clearOutputFns();
            ID o0 = ev->newVar("ooo");
            ID nfn0 = ev->apply(Expr::And, tr.state);
            eat->setOutputFn(o0, nfn0);
            model().release(eat);

            ++numCalls;
            if(ic3) {
              vector<SAT::Clauses> constraints(1, GR);
              _opts->ic3_opts.constraints = &constraints;
              _opts->ic3_opts.iictl = false;
              _opts->ic3_opts.printCex = true;
              _opts->ic3_opts.proofProc = IC3::STRENGTHEN;
              MC::ReturnValue rv;
              vector<SAT::Clauses> proofs;
              vector<Transition> cex;
              _opts->ic3_opts.timeout = model().options()["iictl_ic3timeout"].as<int>();
              _opts->ic3_opts.silent = true;
              if(verb > Options::Verbose) {
                cout << "IC3 Query " << numQueries++ << ": Checking if CTG is reachable: ";
                cout.flush();
              }
              _opts->ic3_opts.propagate = !model().options().count("iictl_xic3propagate");
              IC3::CubeSet indCubes;
              rv = IC3::reach2(model(), _opts->ic3_opts, &cex, &proofs, NULL, NULL, &indCubes);
              _opts->ic3_opts.constraints = NULL;
              _opts->ic3_opts.propagate = false;
              _opts->ic3_opts.timeout = -1;
              _opts->ic3_opts.silent = false;
              //Restore model state
              eat = (ExprAttachment *) model().attachment(Key::EXPR);
              eat->clearOutputFns();
              eat->setOutputFns(outputs, outputFns);
              eat->clearInitialConditions();
              eat->addInitialConditions(init);
              model().release(eat);

              if(rv.returnType != MC::Proof) {
                if(verb > Options::Verbose) {
                  cout << (rv.returnType == MC::CEX ? "Reachable!" : "Timeout") << endl;
                  cout << "Dropping literal failed" << endl;
                }
                if(rv.returnType == MC::CEX) {
                  ++numFailed;
                  //Add all states in counterexample trace to CTG list
                  for(vector<Transition>::const_iterator it = cex.begin();
                      it != cex.end(); ++it) {
                    ctgs.insert(it->state);
                  }
                  for(IC3::CubeSet::const_iterator it = indCubes.begin(); it != indCubes.end(); ++it) {
                    SAT::Clause cls;
                    complement(*ev, *it, cls);
                    GR.push_back(cls);
                    for(IDSatViewMap::iterator it = liftSatViews.begin();
                        it != liftSatViews.end(); ++it) {
                      it->second->add(cls);
                    }
                  }
                }
                else
                  ++numTimeout;
                dropLit = false;
                break;
              }
              else {
                ++numSuccess;
                if(verb > Options::Verbose)
                  cout << "Unreachable!" << endl;
                //Add proof to global reachability information
                GR.insert(GR.end(), proofs[0].begin(), proofs[0].end());

                //Add new global reachability info to all lift SAT databases
                for(IDSatViewMap::iterator it = liftSatViews.begin();
                    it != liftSatViews.end(); ++it) {
                  it->second->add(proofs[0]);
                }
              }
            }
            else {
              _opts->ic3_opts.iictl = false;
              _opts->ic3_opts.silent = true;
              if(verb > Options::Verbose) {
                cout << "MIC Query " << numQueries++ << ": Checking if a subclause of the cube negation is inductive: ";
                cout.flush();
              }
              bool success = mic(model(), _opts->ic3_opts, tr.state);
              //Restore model state
              _opts->ic3_opts.silent = false;
              eat = (ExprAttachment *) model().attachment(Key::EXPR);
              eat->clearInitialConditions();
              eat->addInitialConditions(init);
              eat->clearOutputFns();
              eat->setOutputFns(outputs, outputFns);
              model().release(eat);
              if(success) {
                ++numSuccess;
                if(verb > Options::Verbose)
                  cout << "Inductive subclause found!" << endl;
                SAT::Clause cls;
                complement(*ev, tr.state, cls);
                GR.push_back(cls);
                for(IDSatViewMap::iterator it = liftSatViews.begin();
                    it != liftSatViews.end(); ++it) {
                  it->second->add(cls);
                }
              }
              else {
                ++numFailed;
                if(verb > Options::Verbose) {
                  cout << "No inductive subclause found!" << endl;
                  cout << "Dropping literal failed" << endl;
                }
                dropLit = false;
                break;
              }
            }
          }
        }
        else {
          tr.state.clear();
          tr.inputs.clear();
          fullAssignOf(*ev, model(), fullAsgn, tr.state, tr.inputs);
          liftEX(tr, id);
          bruteForceLiftEX(tr, id);
          SAT::Clause cls;
          complement(*ev, tr.state, cls);
          liftSatView->add(cls);
          //Add to QLBcubes
          QLBcubes[id].push_back(tr.state);
        }
      }
    }
    
    if(!dropLit) {
      s_bar[i] = ev->apply(Expr::Not, s_bar[i]);
    }
    else {
      changed = true;
      vector<ID> newCube;
      for(unsigned j = 0; j < s_bar.size(); ++j) {
        if(j != i)
          newCube.push_back(s_bar[j]);
      }
      s_bar = newCube;
      //Add cube to SAT database
      vector<ID> cls;
      complement(*ev, newCube, cls);
      liftSatView->add(cls);
      --i;
    }
  }
  tr1.state = s_bar;
  sort(tr1.state.begin(), tr1.state.end());
  if(verb > Options::Informative) {
    cout << "Forall-exists procedure: dropped " << numDropped
         << " literals" << endl;
  }
  if(verbosity > Options::Informative) {
    cout << tr1.state.size() << endl;
    cout << numCalls << (ic3 ? " IC3" : " MIC") << " queries, " << numSuccess
         << " inductive, " << numFailed << " not inductive, " << numTimeout
         << " timeouts, " << numPrevCTG << " prev CTGs. " << endl;
  }
  return changed;
}

void IICTLAction::subsumption(vector< vector<ID> > & cubes) {

  int size = cubes.size();
  CubeSet cs;
  for(vector< vector<ID> >::const_iterator it = cubes.begin(); it != cubes.end(); ++it) {
    cs.insert(*it);
  }
  SubsumptionUniverse su;
  su.add(cs, 1);
  su.reduce(cs, 1);

  cubes.clear();
  for(CubeSet::const_iterator it = cs.begin(); it != cs.end(); ++it) {
    cubes.push_back(*it);
  }
  if(verbosity > Options::Informative)
    cout << "Subsumption removed " << size - cubes.size() << " cubes" << endl;
}

void IICTLAction::renewQLB(ID id) {
  vector<ID> disjuncts;
  disjuncts.push_back(baseQLB[id]);
  for(vector< vector<ID> >::const_iterator it = QLBcubes[id].begin(); it != QLBcubes[id].end(); ++it) {
    vector<ID> tmp = *it;
    disjuncts.push_back(ev->apply(Expr::And, tmp));
  }
  QLBId[id] = ev->apply(Expr::Or, disjuncts);
  QLB[id].clear();
  Expr::CNFIZE(*ev, QLBId[id], QLB[id]);
}

ID IICTLAction::disjoinCube(ID id, const vector<ID> & cube) {
  vector<ID> disjuncts;
  disjuncts.push_back(id);
  vector<ID> tmp = cube;
  disjuncts.push_back(ev->apply(Expr::And, tmp));
  return ev->apply(Expr::Or, disjuncts);
}


ID IICTLAction::disjoinCubes(ID id, const vector< vector<ID> > & cubes) {
  vector<ID> disjuncts;
  disjuncts.push_back(id);
  for(vector< vector<ID> >::const_iterator it = cubes.begin(); it != cubes.end(); ++it) {
    vector<ID> tmp = *it;
    disjuncts.push_back(ev->apply(Expr::And, tmp));
  }
  return ev->apply(Expr::Or, disjuncts);
}


void IICTLAction::generalizeTwoStateTrace(vector<Transition> & cex, ID id, ID child) {

/*
  //Check if we're done
  QLBcubes[id].push_back(cex.front().state);
  renewQLB(id);
  updateAncestorsBounds(id, Lower);
*/

  assert(liftSatViews.find(id) != liftSatViews.end());
  SAT::Manager::View * liftSatView = liftSatViews[id];
  //Add (!UB'[child] | !QLB'[child]) with a GID
  ID disj = ev->apply(Expr::Or,
                      ev->apply(Expr::Not, Expr::primeFormula(*ev, UBId[child])),
                      ev->apply(Expr::Not, Expr::primeFormula(*ev, QLBId[child])));
  SAT::Clauses clauses;
  Expr::CNFIZE(*ev, disj, clauses);
  SAT::GID gid1 = liftSatView->newGID();
  SAT::GID gid2 = faeSatView->newGID();
  try {
    liftSatView->add(clauses, gid1);

    //Generalize cex
    //First do a pass of lifting and brute-force lifting
    bool changed = true;
    int pass = 0;
    while(changed) {
      changed = false;
      changed = liftEX(cex.front(), id) || changed;
      //Brute-force lifting
      changed = bruteForceLiftEX(cex.front(), id) || changed;
      ++pass;
      if(verbosity > Options::Informative) {
        cout << "After pass " << pass << " of basic lifting: " << endl;
        cout << cex.front().state.size() << endl;
      }
    }
/*
    //Check if we're done
    QLBcubes[id].push_back(cex.front().state);
    renewQLB(id);
    updateAncestorsBounds(id, Lower);
*/

    //Add reduced cube to lifting SAT database
    vector<ID> cls;
    complement(*ev, cex.front().state, cls);
    liftSatView->add(cls);

    int64_t totTime = 0;
    changed = true;
    pass = 0;
    //Second do a pass of forall-exists with MIC for CTGs
    //Prepare CNF for Query 2 (UB'[child] & QLB'[child])
    SAT::Clauses q2clauses = UB[child];
    q2clauses.insert(q2clauses.end(), QLB[child].begin(), QLB[child].end());
    for(SAT::Clauses::iterator it = q2clauses.begin(); it != q2clauses.end();
        ++it) {
      primeFormulas(*ev, *it);
    }
    faeSatView->add(q2clauses, gid2);
    if(model().options()["iictl_gen_aggr"].as<int>() > 0) {
      while(changed) {
        changed = false;
        if(verbosity > Options::Informative)
          cout << "Pass " << pass << " of forall-exists lifting with MIC: " << endl;
        int64_t startTime = Util::get_user_cpu_time(); 
        changed = forAllExistsEX(cex.front(), id, true, false) || changed;
        totTime += Util::get_user_cpu_time() - startTime;
        ++pass;
      }
      if(verbosity > Options::Informative)
        cout << "Forall-exists with no reachability " << totTime / 1000000.0 << " seconds" << endl;
/*
      //Check if we're done
      QLBcubes[id].push_back(cex.front().state);
      renewQLB(id);
      updateAncestorsBounds(id, Lower);
*/
    }

    totTime = 0;
    changed = true;
    pass = 0;
    if(model().options()["iictl_gen_aggr"].as<int>() > 1) {
      while(changed) {
        changed = false;
        //Do a final pass of forall-exists procedure with reachability checks
        //for CTGs
        if(verbosity > Options::Informative)
          cout << "Pass " << pass << " of forall-exists lifting with reachability: " << endl;
        int64_t startTime = Util::get_user_cpu_time(); 
        changed = forAllExistsEX(cex.front(), id, true, true) || changed;
        totTime += Util::get_user_cpu_time() - startTime;
        ++pass;
      }
      if(verbosity > Options::Informative)
        cout << "Forall-exists with reachability " << totTime / 1000000.0 << " seconds" << endl;
/*
      //Check if we're done
      QLBcubes[id].push_back(cex.front().state);
      renewQLB(id);
      updateAncestorsBounds(id, Lower);
*/
    }
    liftSatView->remove(gid1);
    faeSatView->remove(gid2);
  }
  catch(SAT::Trivial tr) {
    assert(!tr.value());
    liftSatView->remove(gid1);
    faeSatView->remove(gid2);
    QLBId[id] = ev->btrue();
    QLB[id].clear();
    QLB[id].push_back(SAT::Clause(1, ev->btrue()));
    //updateAncestorsBounds(id, Lower);
    return;
  }

  //Simplify GR
  SubsumptionUniverse su;
  CubeSet cs;
  for(vector< vector<ID> >::iterator it = GR.begin(); it != GR.end(); ++it) {
    vector<ID> cube;
    complement(*ev, *it, cube);
    cs.insert(cube);
  }
  int size = GR.size();
  su.add(cs, 1);
  su.reduce(cs, 1);
  GR.clear();
  for(CubeSet::iterator it = cs.begin(); it != cs.end(); ++it) {
    vector<ID> cls;
    complement(*ev, *it, cls);
    GR.push_back(cls);
  }
  if(verbosity > Options::Informative)
    cout << "Subsumption on GR removed " << size - GR.size() << endl;

  if(model().options().count("iictl_count_reach")) {
    BddAttachment const * bat = (BddAttachment *) model().constAttachment(Key::BDD);
    if(verbosity > Options::Informative)
      cout << "Number of potentially reachable states";
    bat->countStates(GR, *ev);
    model().constRelease(bat);
  }

  //Add state to QLB cubes
  assert(QLBcubes.find(id) != QLBcubes.end());
  QLBcubes[id].push_back(cex.front().state);
  if(verbosity > Options::Informative) {
    set<ID> ids;
    ids.insert(cex.front().state.begin(), cex.front().state.end());
    ExprAttachment const * const eat = (ExprAttachment const *)
                                       model().constAttachment(Key::EXPR);
    const vector<ID> & svs = eat->stateVars();
    for(vector<ID>::const_iterator it2 = svs.begin(); it2 != svs.end(); ++it2) {
      if(ids.find(*it2) != ids.end()) {
        cout << "1";
      }
      else if(ids.find(ev->apply(Expr::Not, *it2)) != ids.end()) {
        cout << "0";
      }
      else {
        cout << "-";
      }
    }
    cout << endl;
    model().constRelease(eat);
  }

  //Apply subsumption
  subsumption(QLBcubes[id]);
  renewQLB(id);
  //updateAncestorsBounds(id, Lower);

  if(!model().options().count("iictl_xsat_renew")) {
    //Renew lifting SAT database
    SAT::Manager * sman = model().newSATManager();
    sman->add(tr);
    //1) Add !baseQLB
    SAT::Clauses clauses;
    Expr::CNFIZE(*ev, ev->apply(Expr::Not, baseQLB[id]), clauses);
    sman->add(clauses);
    //2) Add !QLBcubes
    for(vector< vector<ID> >::const_iterator it = QLBcubes[id].begin(); it != QLBcubes[id].end(); ++it) {
      SAT::Clause cls;
      complement(*ev, *it, cls);
      sman->add(cls);
    }
    //3) Add UB
    sman->add(UB[id]);
    //4) Add GR
    sman->add(GR);
    SAT::Manager::View * sview = sman->newView(*ev);
    liftSatViews[id] = sview;
  }
}


void IICTLAction::generalizeEFTrace(vector<Transition> & cex, ID id) {
/*
  for(vector<Transition>::const_iterator it = cex.begin(); it != cex.end(); ++it) {
    QLBcubes[id].push_back(it->state);
  }
  renewQLB(id);
  updateAncestorsBounds(id, Lower);
*/


  assert(liftSatViews.find(id) != liftSatViews.end());
  SAT::Manager::View * liftSatView = liftSatViews[id];
  //Add (!UB' | !QLB')
  SAT::GID gid1 = liftSatView->newGID();
  //1) Create CNF for !UB'
  SAT::Clauses ubCNF;
  Expr::CNFIZE(*ev, ev->apply(Expr::Not, Expr::primeFormula(*ev, UBId[id])),
                ubCNF);
  //2) Add all clauses in !UB' with an activation literal
  ID ubRep = rep(*ev, id);
  for(SAT::Clauses::const_iterator it = ubCNF.begin(); it != ubCNF.end(); ++it) {
    //Add activation literal
    SAT::Clause cls = *it;
    cls.push_back(ev->apply(Expr::Not, ubRep));
    //Add to SAT database
    try {
      liftSatView->add(cls, gid1);
    }
    catch(SAT::Trivial tr) {
      assert(tr.value());
    }
  }
  //3) Add all clauses in !QLB' with an activation literal
  //a) Create an activation literal
  ID qlbRep = rep(*ev, id);
  //b) First add !baseQLB'
  SAT::Clauses baseQLBCNF;
  Expr::CNFIZE(*ev, ev->apply(Expr::Not, Expr::primeFormula(*ev, baseQLB[id])), baseQLBCNF);
  for(SAT::Clauses::const_iterator it = baseQLBCNF.begin(); it != baseQLBCNF.end(); ++it) {
    //Add activation literal
    SAT::Clause cls = *it;
    cls.push_back(ev->apply(Expr::Not, qlbRep));
    //Add to SAT database
    try {
      liftSatView->add(cls, gid1);
    }
    catch(SAT::Trivial tr) {
      assert(tr.value());
    }
  }
  //c) Second add !QLBcubes'
  for(vector< vector<ID> >::const_iterator it = QLBcubes[id].begin(); it != QLBcubes[id].end(); ++it) {
    SAT::Clause cls;
    complement(*ev, *it, cls);
    //Prime
    SAT::Clause prcls;
    primeVector(*ev, cls, prcls);
    //Add activation literal
    prcls.push_back(ev->apply(Expr::Not, qlbRep));
    //Add to database
    liftSatView->add(prcls, gid1);
  }
  //4) Add a clause representing the dijsunction of !UB' and !QLB'
  SAT::Clause disj;
  disj.push_back(ubRep);
  disj.push_back(qlbRep);
  liftSatView->add(disj, gid1);

  //Add current trace
  for(vector<Transition>::const_iterator it = cex.begin();
      it != cex.end(); ++it) {
    SAT::Clause cls;
    complement(*ev, it->state, cls);
    liftSatView->add(cls);
    SAT::Clause primedCls;
    primeVector(*ev, cls, primedCls);
    //Add activation literal
    primedCls.push_back(ev->apply(Expr::Not, qlbRep));
    liftSatView->add(primedCls, gid1);
  }
 
  //Generalize cex
  //First do a pass of lifting and brute-force lifting
  bool changed = true;
  int pass = 0;
  try {
    while(changed) {
      changed = false;
      for(vector<Transition>::reverse_iterator it = cex.rbegin() + 1;
          it != cex.rend(); ++it) {
        changed = liftEF(*it, id, qlbRep, gid1, true) || changed;
        //Brute-force lifting
        changed = bruteForceLiftEF(*it, id, qlbRep, gid1, true) || changed;
      }
      ++pass;
      if(verbosity > Options::Informative) {
        cout << "After pass " << pass << " of basic lifting: " << endl;
        for(vector<Transition>::iterator it = cex.begin(); 
            it != cex.end(); ++it) {
          cout << it->state.size() << " ";
        }
        cout << endl;
      }
    }

/*
    for(vector<Transition>::const_iterator it = cex.begin(); it != cex.end(); ++it) {
      QLBcubes[id].push_back(it->state);
    }
    renewQLB(id);
    updateAncestorsBounds(id, Lower);
*/


    int64_t totTime = 0;
    changed = true;
    pass = 0;
    //Second do a pass of forall-exists without reachability for CTGs
    //Prepare CNF for Query 2 (UB' & QLB')
    ID tmpQLB = primeFormula(*ev, QLBId[id]);
    vector< vector<ID> > newCubes;
    for(vector<Transition>::const_iterator it = cex.begin();
        it != cex.end(); ++it) {
      vector<ID> prcube;
      primeVector(*ev, it->state, prcube);
      newCubes.push_back(prcube);
    }
    tmpQLB = disjoinCubes(tmpQLB, newCubes);
    SAT::Clauses ubPrimed;
    primeCNF(*ev, UB[id], ubPrimed);
    SAT::Clauses q2clauses(ubPrimed);
    Expr::CNFIZE(*ev, tmpQLB, q2clauses);

    if(model().options()["iictl_gen_aggr"].as<int>() > 0) {
      while(changed) {
        changed = false;

        if(verbosity > Options::Informative)
          cout << "Pass " << pass << " of forall-exists lifting with MIC: " << endl;
        for(vector<Transition>::reverse_iterator it = cex.rbegin() + 1;
            it != cex.rend(); ++it) {
          bool restart = false;
          int64_t startTime = Util::get_user_cpu_time(); 
          changed = forAllExistsEF(*it, q2clauses, id, qlbRep, gid1, tmpQLB, ubPrimed, true, false) || changed;
          totTime += Util::get_user_cpu_time() - startTime;

          if(model().options().count("iictl_interlv_blift")) {
            if(changed)
              restart = true;

            while(changed) {
              changed = false;
              for(vector<Transition>::reverse_iterator it2 = cex.rbegin() + 1;
                  it2 != cex.rend(); ++it2) {
                changed = liftEF(*it2, id, qlbRep, gid1, true) || changed;
                //Brute-force lifting
                changed = bruteForceLiftEF(*it2, id, qlbRep, gid1, true) || changed;
              }
              if(verbosity > Options::Informative) {
                for(vector<Transition>::iterator it2 = cex.begin(); 
                    it2 != cex.end(); ++it2) {
                  cout << it2->state.size() << " ";
                }
                cout << endl;
              }
            }

            if(restart) {
              //Add to q2clauses the disjunction of all the cubes of the current
              //trace
              //Update tmpQLB
              vector< vector<ID> > newCubes;
              for(vector<Transition>::const_iterator it2 = cex.begin();
                  it2 != cex.end(); ++it2) {
                vector<ID> prcube;
                primeVector(*ev, it->state, prcube);
                newCubes.push_back(prcube);
              }
              tmpQLB = disjoinCubes(tmpQLB, newCubes);
              q2clauses = ubPrimed;
              Expr::CNFIZE(*ev, tmpQLB, q2clauses);

              changed = true;
              break;
            }
          }

        }
        ++pass;
        if(verbosity > Options::Informative) {
          for(vector<Transition>::iterator it = cex.begin(); it != cex.end();
              ++it) {
            cout << it->state.size() << " ";
          }
          cout << endl;
        }
      }
      if(verbosity > Options::Informative)
        cout << "Forall-exists with no reachability " << totTime / 1000000.0 << " seconds" << endl;
/*
      for(vector<Transition>::const_iterator it = cex.begin(); it != cex.end(); ++it) {
        QLBcubes[id].push_back(it->state);
      }
      renewQLB(id);
      updateAncestorsBounds(id, Lower);
*/
    }
    totTime = 0;
    changed = true;
    pass = 0;
    if(model().options()["iictl_gen_aggr"].as<int>() > 1) {
      while(changed) {
        changed = false;
        //Do a final pass of forall-exists procedure with reachability checks
        //for CTGs
        if(verbosity > Options::Informative)
          cout << "Pass " << pass << " of forall-exists lifting with reachability: " << endl;
        for(vector<Transition>::reverse_iterator it = cex.rbegin() + 1; it != cex.rend(); ++it) {
          bool restart = false;
          int64_t startTime = Util::get_user_cpu_time(); 
          changed = forAllExistsEF(*it, q2clauses, id, qlbRep, gid1, tmpQLB, ubPrimed, true, true) || changed;
          totTime += Util::get_user_cpu_time() - startTime;

          if(model().options().count("iictl_interlv_blift")) {
            if(changed)
              restart = true;

            while(changed) {
              changed = false;
              for(vector<Transition>::reverse_iterator it2 = cex.rbegin() + 1;
                  it2 != cex.rend(); ++it2) {
                changed = liftEF(*it2, id, qlbRep, gid1, true) || changed;
                //Brute-force lifting
                changed = bruteForceLiftEF(*it2, id, qlbRep, gid1, true) || changed;
              }
              if(verbosity > Options::Informative) {
                for(vector<Transition>::iterator it2 = cex.begin(); 
                    it2 != cex.end(); ++it2) {
                  cout << it2->state.size() << " ";
                }
                cout << endl;
              }
            }

            if(restart) {
              //Add to q2clauses the disjunction of all the cubes of the current
              //trace
              //Update tmpQLB
              vector< vector<ID> > newCubes;
              for(vector<Transition>::const_iterator it2 = cex.begin();
                  it2 != cex.end(); ++it2) {
                vector<ID> prcube;
                primeVector(*ev, it->state, prcube);
                newCubes.push_back(prcube);
              }
              tmpQLB = disjoinCubes(tmpQLB, newCubes);
              q2clauses = ubPrimed;
              Expr::CNFIZE(*ev, tmpQLB, q2clauses);

              changed = true;
              break;
            }
          }
        }
        ++pass;
        if(verbosity > Options::Informative) {
          for(vector<Transition>::iterator it = cex.begin(); 
              it != cex.end(); ++it) {
            cout << it->state.size() << " ";
          }
          cout << endl;
        }
      }
      if(verbosity > Options::Informative)
        cout << "Forall-exists with reachability " << totTime / 1000000.0 << " seconds" << endl;
/*
      for(vector<Transition>::const_iterator it = cex.begin(); it != cex.end(); ++it) {
        QLBcubes[id].push_back(it->state);
      }
      renewQLB(id);
      updateAncestorsBounds(id, Lower);
*/
    }
  }
  catch(SAT::Trivial tr) {
    liftSatView->remove(gid1);
    assert(!tr.value());
    QLBId[id] = ev->btrue();
    QLB[id].clear();
    QLB[id].push_back(SAT::Clause(1, ev->btrue()));
    //updateAncestorsBounds(id, Lower);
    return;
  }
  liftSatView->remove(gid1);

  //Simplify GR
  SubsumptionUniverse su;
  CubeSet cs;
  for(vector< vector<ID> >::iterator it = GR.begin(); it != GR.end(); ++it) {
    vector<ID> cube;
    complement(*ev, *it, cube);
    cs.insert(cube);
  }
  int size = GR.size();
  su.add(cs, 1);
  su.reduce(cs, 1);
  GR.clear();
  for(CubeSet::iterator it = cs.begin(); it != cs.end(); ++it) {
    vector<ID> cls;
    complement(*ev, *it, cls);
    GR.push_back(cls);
  }
  if(verbosity > Options::Informative)
    cout << "Subsumption on GR removed " << size - GR.size() << endl;

  if(model().options().count("iictl_count_reach")) {
    BddAttachment const * bat = (BddAttachment *) model().constAttachment(Key::BDD);
    cout << "Number of potentially reachable states";
    bat->countStates(GR, *ev);
    model().constRelease(bat);
  }

  //Add all states on cex trace to QLBcubes
  for(vector<Transition>::const_iterator it = cex.begin(); it != cex.end(); ++it) {
    assert(QLBcubes.find(id) != QLBcubes.end());
    QLBcubes[id].push_back(it->state);
    if(verbosity > Options::Informative) {
      if(it == cex.begin()) {
        set<ID> ids;
        ids.insert(it->state.begin(), it->state.end());
        ExprAttachment * eat = (ExprAttachment *) model().attachment(Key::EXPR);
        vector<ID> svs = eat->stateVars();
        for(vector<ID>::const_iterator it2 = svs.begin(); it2 != svs.end(); ++it2) {
          if(ids.find(*it2) != ids.end()) {
            cout << "1";
          }
          else if(ids.find(ev->apply(Expr::Not, *it2)) != ids.end()) {
            cout << "0";
          }
          else {
            cout << "-";
          }
        }
        cout << endl;
        model().release(eat);
      }
    }
  }

  //Apply subsumption
  subsumption(QLBcubes[id]);
  //Renew QLB
  renewQLB(id);
  //updateAncestorsBounds(id, Lower);

  if(!model().options().count("iictl_xsat_renew")) {
    //Renew lifting SAT database
    SAT::Manager * sman = model().newSATManager();
    sman->add(tr);
    //1) Add !baseQLB
    SAT::Clauses clauses;
    Expr::CNFIZE(*ev, ev->apply(Expr::Not, baseQLB[id]), clauses);
    sman->add(clauses);
    //2) Add !QLBcubes
    for(vector< vector<ID> >::const_iterator it = QLBcubes[id].begin(); it != QLBcubes[id].end(); ++it) {
      SAT::Clause cls;
      complement(*ev, *it, cls);
      sman->add(cls);
    }
    //3) Add UB
    sman->add(UB[id]);
    //4) Add GR
    sman->add(GR);
    SAT::Manager::View * sview = sman->newView(*ev);
    liftSatViews[id] = sview;
  }

}

void IICTLAction::generalizeLasso(Lasso & lasso, ID id, ID child) {
  //Linearize the lasso
  vector<Transition> cex = lasso.stem;
  cex.insert(cex.end(), lasso.loop.begin(), lasso.loop.end());

  generalizeEUTrace(cex, id, child);
}

void IICTLAction::generalizeEUTrace(vector<Transition> & cex, ID id, ID child) {
/*
  for(vector<Transition>::const_iterator it = cex.begin(); it != cex.end(); ++it) {
    QLBcubes[id].push_back(it->state);
  }
  renewQLB(id);
  updateAncestorsBounds(id, Lower);
*/

  assert(liftSatViews.find(id) != liftSatViews.end());
  SAT::Manager::View * liftSatView = liftSatViews[id];
  //Add (!UB' | !QLB' | !QLB(child))
  SAT::GID gid1 = liftSatView->newGID();
  //1) Create CNF for !UB'
  SAT::Clauses ubCNF;
  Expr::CNFIZE(*ev, ev->apply(Expr::Not, Expr::primeFormula(*ev, UBId[id])),
                ubCNF);
  //2) Add all clauses in !UB' with an activation literal
  ID ubRep = rep(*ev, id);
  for(SAT::Clauses::const_iterator it = ubCNF.begin(); it != ubCNF.end(); ++it) {
    //Add activation literal
    SAT::Clause cls = *it;
    cls.push_back(ev->apply(Expr::Not, ubRep));
    //Add to SAT database
    try {
      liftSatView->add(cls, gid1);
    }
    catch(SAT::Trivial tr) {
      assert(tr.value());
    }
  }
  //3) Add all clauses in !QLB' with an activation literal
  //a) Create an activation literal
  ID qlbRep = rep(*ev, id);
  //b) First add !baseQLB'
  SAT::Clauses baseQLBCNF;
  Expr::CNFIZE(*ev, ev->apply(Expr::Not, Expr::primeFormula(*ev, baseQLB[id])), baseQLBCNF);
  for(SAT::Clauses::const_iterator it = baseQLBCNF.begin(); it != baseQLBCNF.end(); ++it) {
    //Add activation literal
    SAT::Clause cls = *it;
    cls.push_back(ev->apply(Expr::Not, qlbRep));
    //Add to SAT database
    try {
      liftSatView->add(cls, gid1);
    }
    catch(SAT::Trivial tr) {
      assert(tr.value());
    }
  }
  //c) Second add !QLBcubes'
  for(vector< vector<ID> >::const_iterator it = QLBcubes[id].begin(); it != QLBcubes[id].end(); ++it) {
    SAT::Clause cls;
    complement(*ev, *it, cls);
    //Prime
    SAT::Clause prcls;
    primeVector(*ev, cls, prcls);
    //Add activation literal
    prcls.push_back(ev->apply(Expr::Not, qlbRep));
    //Add to database
    liftSatView->add(prcls, gid1);
  }
  //4) Add all clauses in !QLB(child) with an activation literal
  ID chqlbRep;
  SAT::Manager * q2man = model().newSATManager();
  SAT::Manager::View * q2view = q2man->newView(*ev);
  //a) Create an activation literal
  chqlbRep = rep(*ev, id);
  SAT::Clauses chQLBCNF;
  Expr::CNFIZE(*ev, ev->apply(Expr::Not, QLBId[child]), chQLBCNF);
  for(SAT::Clauses::iterator it = chQLBCNF.begin();
      q2view && it != chQLBCNF.end(); ++it) {
    SAT::Clause cls = *it;
    try {
      q2view->add(cls);
    }
    catch(SAT::Trivial tr) {
      if(!tr.value()) {
        delete q2view;
        q2view = NULL;
      }
    }
    //Add activation literal
    cls.push_back(ev->apply(Expr::Not, chqlbRep));
    //Add to SAT database
    liftSatView->add(cls, gid1);
  }
  //5) Add a clause representing the dijsunction of !UB', !QLB', and !QLB(child)
  SAT::Clause disj;
  disj.push_back(ubRep);
  disj.push_back(qlbRep);
  disj.push_back(chqlbRep);
  liftSatView->add(disj, gid1);
  
  //Add current trace
  for(vector<Transition>::const_iterator it = cex.begin();
      it != cex.end(); ++it) {
    SAT::Clause cls;
    complement(*ev, it->state, cls);
    liftSatView->add(cls);
    SAT::Clause primedCls;
    primeVector(*ev, cls, primedCls);
    //Add activation literal
    primedCls.push_back(ev->apply(Expr::Not, qlbRep));
    liftSatView->add(primedCls, gid1);
  }

  //Generalize cex
  //First do a pass of lifting and brute-force lifting
  bool changed = true;
  int pass = 0;
  try {
    while(changed) {
      changed = false;
      for(vector<Transition>::reverse_iterator it = cex.rbegin() + 1;
          it != cex.rend(); ++it) {
        changed = liftEF(*it, id, qlbRep, gid1, true) || changed;
        //Brute-force lifting
        changed = bruteForceLiftEF(*it, id, qlbRep, gid1, true) || changed;
      }
      ++pass;
      if(verbosity > Options::Informative) {
        cout << "After pass " << pass << " of basic lifting: " << endl;
        for(vector<Transition>::iterator it = cex.begin(); 
            it != cex.end(); ++it) {
          cout << it->state.size() << " ";
        }
        cout << endl;
      }
    }

/*
    for(vector<Transition>::const_iterator it = cex.begin(); it != cex.end(); ++it) {
      QLBcubes[id].push_back(it->state);
    }
    renewQLB(id);
    updateAncestorsBounds(id, Lower);
*/

    int64_t totTime = 0;
    changed = true;
    pass = 0;
    //Second do a pass of forall-exists without reachability for CTGs
    //Prepare CNF for Query 3 (UB' & QLB')
    ID tmpQLB = primeFormula(*ev, QLBId[id]);
    vector< vector<ID> > newCubes;
    for(vector<Transition>::const_iterator it = cex.begin();
        it != cex.end(); ++it) {
      vector<ID> prcube;
      primeVector(*ev, it->state, prcube);
      newCubes.push_back(prcube);
    }
    tmpQLB = disjoinCubes(tmpQLB, newCubes);
    SAT::Clauses ubPrimed;
    primeCNF(*ev, UB[id], ubPrimed);
    SAT::Clauses q3clauses(ubPrimed);
    Expr::CNFIZE(*ev, tmpQLB, q3clauses);

    if(model().options()["iictl_gen_aggr"].as<int>() > 0) {
      while(changed) {
        changed = false;
        if(verbosity > Options::Informative)
          cout << "Pass " << pass << " of forall-exists lifting with MIC: " << endl;
        for(vector<Transition>::reverse_iterator it = cex.rbegin() + 1;
            it != cex.rend(); ++it) {
          bool restart = false;
          int64_t startTime = Util::get_user_cpu_time(); 
          changed = forAllExistsEG(*it, q3clauses, id, qlbRep, gid1, q2view, tmpQLB, ubPrimed, true, false) || changed;
          totTime += Util::get_user_cpu_time() - startTime;

          if(model().options().count("iictl_interlv_blift")) {
            if(changed)
              restart = true;

            while(changed) {
              changed = false;
              for(vector<Transition>::reverse_iterator it2 = cex.rbegin() + 1;
                  it2 != cex.rend(); ++it2) {
                changed = liftEF(*it2, id, qlbRep, gid1, true) || changed;
                //Brute-force lifting
                changed = bruteForceLiftEF(*it2, id, qlbRep, gid1, true) || changed;
              }
              if(verbosity > Options::Informative) {
                for(vector<Transition>::iterator it2 = cex.begin(); 
                    it2 != cex.end(); ++it2) {
                  cout << it2->state.size() << " ";
                }
                cout << endl;
              }
            }

            if(restart) {
              //Add to q3clauses the disjunction of all the cubes of the current
              //trace
              //Update tmpQLB
              vector< vector<ID> > newCubes;
              for(vector<Transition>::const_iterator it2 = cex.begin(); it2 != cex.end(); ++it2) {
                vector<ID> prcube;
                primeVector(*ev, it2->state, prcube);
                newCubes.push_back(prcube);
              }
              tmpQLB = disjoinCubes(tmpQLB, newCubes);
              q3clauses = ubPrimed;
              Expr::CNFIZE(*ev, tmpQLB, q3clauses);
              changed = true;
              break;
            }
          }

        }
        ++pass;
        if(verbosity > Options::Informative) {
          for(vector<Transition>::iterator it = cex.begin(); 
              it != cex.end(); ++it) {
            cout << it->state.size() << " ";
          }
          cout << endl;
        }
      }
      if(verbosity > Options::Informative)
        cout << "Forall-exists with no reachability " << totTime / 1000000.0 << " seconds" << endl;
/*
      for(vector<Transition>::const_iterator it = cex.begin(); it != cex.end(); ++it) {
        QLBcubes[id].push_back(it->state);
      }
      renewQLB(id);
      updateAncestorsBounds(id, Lower);
*/
    }
    totTime = 0;
    changed = true;
    pass = 0;
    if(model().options()["iictl_gen_aggr"].as<int>() > 1) {
      while(changed) {
        changed = false;
        //Do a final pass of forall-exists procedure with reachability checks
        //for CTGs
        if(verbosity > Options::Informative)
          cout << "Pass " << pass << " of forall-exists lifting with reachability: " << endl;
        for(vector<Transition>::reverse_iterator it = cex.rbegin() + 1; it != cex.rend(); ++it) {
          bool restart = false;
          int64_t startTime = Util::get_user_cpu_time(); 
          changed = forAllExistsEG(*it, q3clauses, id, qlbRep, gid1, q2view, tmpQLB, ubPrimed, true, true) || changed;
          totTime += Util::get_user_cpu_time() - startTime;

          if(model().options().count("iictl_interlv_blift")) {
            if(changed)
              restart = true;

            while(changed) {
              changed = false;
              for(vector<Transition>::reverse_iterator it2 = cex.rbegin() + 1;
                  it2 != cex.rend(); ++it2) {
                changed = liftEF(*it2, id, qlbRep, gid1, true) || changed;
                //Brute-force lifting
                changed = bruteForceLiftEF(*it2, id, qlbRep, gid1, true) || changed;
              }
              if(verbosity > Options::Informative) {
                for(vector<Transition>::iterator it2 = cex.begin(); 
                    it2 != cex.end(); ++it2) {
                  cout << it2->state.size() << " ";
                }
                cout << endl;
              }
            }

            if(restart) {
              //Add to q3clauses the disjunction of all the cubes of the current
              //trace
              vector< vector<ID> > newCubes;
              for(vector<Transition>::const_iterator it2 = cex.begin(); it2 != cex.end(); ++it2) {
                vector<ID> prcube;
                primeVector(*ev, it2->state, prcube);
                newCubes.push_back(prcube);
              }
              tmpQLB = disjoinCubes(tmpQLB, newCubes);
              q3clauses = ubPrimed;
              Expr::CNFIZE(*ev, tmpQLB, q3clauses);
              changed = true;
              break;
            }
          }
        }
        ++pass;
        if(verbosity > Options::Informative) {
          for(vector<Transition>::iterator it = cex.begin(); 
              it != cex.end(); ++it) {
            cout << it->state.size() << " ";
          }
          cout << endl;
        }
      }
      if(verbosity > Options::Informative)
        cout << "Forall-exists with reachability " << totTime / 1000000.0 << " seconds" << endl;
/*
      for(vector<Transition>::const_iterator it = cex.begin(); it != cex.end(); ++it) {
        QLBcubes[id].push_back(it->state);
      }
      renewQLB(id);
      updateAncestorsBounds(id, Lower);
*/
    }
  }
  catch(SAT::Trivial tr) {
    liftSatView->remove(gid1);
    delete q2view;
    delete q2man;
    assert(!tr.value());
    QLBId[id] = ev->btrue();
    QLB[id].clear();
    QLB[id].push_back(SAT::Clause(1, ev->btrue()));
    //updateAncestorsBounds(id, Lower);
    return;
  }
  liftSatView->remove(gid1);
  delete q2view;
  delete q2man;

  //Simplify GR
  SubsumptionUniverse su;
  CubeSet cs;
  for(vector< vector<ID> >::iterator it = GR.begin(); it != GR.end(); ++it) {
    vector<ID> cube;
    complement(*ev, *it, cube);
    cs.insert(cube);
  }
  int size = GR.size();
  su.add(cs, 1);
  su.reduce(cs, 1);
  GR.clear();
  for(CubeSet::iterator it = cs.begin(); it != cs.end(); ++it) {
    vector<ID> cls;
    complement(*ev, *it, cls);
    GR.push_back(cls);
  }
  if(verbosity > Options::Informative)
    cout << "Subsumption on GR removed " << size - GR.size() << endl;

  if(model().options().count("iictl_count_reach")) {
    BddAttachment const * bat = (BddAttachment *) model().constAttachment(Key::BDD);
    cout << "Number of potentially reachable states";
    bat->countStates(GR, *ev);
    model().constRelease(bat);
  }

  //Add all states on cex trace to QLBcubes
  for(vector<Transition>::const_iterator it = cex.begin(); it != cex.end(); ++it) {
    assert(QLBcubes.find(id) != QLBcubes.end());
    QLBcubes[id].push_back(it->state);
    if(verbosity > Options::Informative) {
      if(it == cex.begin()) {
        set<ID> ids;
        ids.insert(it->state.begin(), it->state.end());
        ExprAttachment * eat = (ExprAttachment *) model().attachment(Key::EXPR);
        vector<ID> svs = eat->stateVars();
        for(vector<ID>::const_iterator it2 = svs.begin(); it2 != svs.end(); ++it2) {
          if(ids.find(*it2) != ids.end()) {
            cout << "1";
          }
          else if(ids.find(ev->apply(Expr::Not, *it2)) != ids.end()) {
            cout << "0";
          }
          else {
            cout << "-";
          }
        }
        cout << endl;
        model().release(eat);
      }
    }
  }

  //Apply subsumption
  subsumption(QLBcubes[id]);
  //Renew QLB
  renewQLB(id);
  //updateAncestorsBounds(id, Lower);

  if(!model().options().count("iictl_xsat_renew")) {
    //Renew lifting SAT database
    SAT::Manager * sman = model().newSATManager();
    SAT::Manager::View * sview = sman->newView(*ev);
    sview->add(tr);
    //1) Add !baseQLB
    SAT::Clauses clauses;
    Expr::CNFIZE(*ev, ev->apply(Expr::Not, baseQLB[id]), clauses);
    sview->add(clauses);
    //2) Add !QLBcubes
    for(vector< vector<ID> >::const_iterator it = QLBcubes[id].begin(); it != QLBcubes[id].end(); ++it) {
      SAT::Clause cls;
      complement(*ev, *it, cls);
      sview->add(cls);
    }
    //3) Add UB
    sview->add(UB[id]);
    //4) Add GR
    sview->add(GR);
    liftSatViews[id] = sview;
  }
}

MC::ReturnValue IICTLAction::runIC3(IC3::IC3Options & opts, ID targetID,
                                    vector<Transition> & cex,
                                    vector<SAT::Clauses> & proofs,
                                    bool incremental, bool propagate) {

  IC3::CubeSet indCubes;

  MC::ReturnValue rv = IC3::reach2(model(), opts, &cex, &proofs, 
                                   incremental ? &cubes : NULL, 
                                   incremental ? & propClauses : NULL,
                                   propagate ? &indCubes : NULL);

  if(rv.returnType == MC::CEX) {
    if(incremental) {
      //Add property to propClauses at last level reached in IC3 call
      if(cex.size() > 2) { //Call involved IC3 not just BMC
        SAT::Clauses property;
        Expr::CNFIZE(*ev, ev->apply(Expr::Not, targetID), property);
        propClauses.back().clauses = property;
      }
    }

    //Add inductive clauses to GR
    if(propagate) {
      if(verbosity > Options::Informative)
        cout << indCubes.size() << " inductive clauses derived" << endl;
      for(IC3::CubeSet::const_iterator it = indCubes.begin(); it != indCubes.end(); ++it) {
        SAT::Clause cls;
        complement(*ev, *it, cls);
        GR.push_back(cls);
        //Add to all lifting SAT databases
        for(IDSatViewMap::iterator it = liftSatViews.begin();
            it != liftSatViews.end(); ++it) {
          it->second->add(cls);
        }
      }
      if(model().options().count("iictl_count_reach")) {
        BddAttachment const * bat = (BddAttachment *) model().constAttachment(Key::BDD);
        cout << "Number of potentially reachable states";
        bat->countStates(GR, *ev);
        model().constRelease(bat);
      }
    }
  }

  return rv;
}


bool IICTLAction::fair(const vector<ID> & source, SAT::Clauses & constraints, SAT::Clauses & negConstraints,
                       IC3::ProofProcType grppt, bool globalLast,
                       vector<SAT::Clauses> & proofs, Lasso & cex, ID id) {
  ExprAttachment * eat = (ExprAttachment *) model().attachment(Key::EXPR);
  //Save the old output functions
  vector<ID> outputs = eat->outputs();
  vector<ID> outputFns = eat->outputFns();
  //Must remove all outputs so that they're not perceived by Fair as
  //fairness constraints
  eat->clearOutputFns();
  //Check for the existence of fairness constraints in the model
  const vector<ID> & fairness = eat->fairness();
  if(!fairness.empty()) {
    //Copy them to the outputs
    const vector<ID> & fairnessFns = eat->fairnessFns();
    eat->setOutputFns(fairness, fairnessFns);
  }
  else {
    //Add a single trivial fairness constraint 
    ID fc = ev->newVar("_fc0_");
    eat->setOutputFn(fc, ev->btrue());
  }
  //Change the initial conditions
  vector<ID> init(eat->initialConditions());
  eat->clearInitialConditions();
  eat->addInitialConditions(source);
  model().release(eat);

  //Prepare FCBMC
  FCBMC::FCBMCOptions fcbmcOpts(&constraints);
  fcbmcOpts.silent = (model().verbosity() == Options::Silent);
  FCBMC::FCBMC fcbmc(model(), fcbmcOpts);

  //Prepare Fair
  Fair::FairOptions & opts = _opts->fair_opts;
  //Fair::FairOptions opts(model().options());
  opts.constraints = &constraints;
  opts.negConstraints = &negConstraints;
  opts.printCex = true;
  opts.ic3_opts.silent = true;
  opts.proofProc = grppt;
  opts.global_last = globalLast;
  opts.iictl = true;
 
  MC::ReturnValue rv;
  opts.timeout = 2;
  rv = Fair::fairPath(model(), opts, &cex, &proofs);
  if(rv.returnType == MC::Unknown) {
    rv = fcbmc.check(5, 8191, &cex);

    if(rv.returnType != MC::CEX) {
      opts.timeout = -1;
      rv = Fair::fairPath(model(), opts, &cex, &proofs);
    }
  }
 
#if 0
  int timeout = 1;
  int iter = 0;
  while(true) {
    double prob = exp(-bmcFail[id] * iter / double(bmcFactor));
    if(rand() < prob * RAND_MAX) {
      if(verbosity > Options::Informative)
        cout << "FCBMC: (" << timeout << "s)" << endl;
      rv = fcbmc.check(timeout, 8191, &cex);

      if(rv.returnType == MC::CEX) {
        if(iter > 0) {
          bmcFail[id] = max(bmcFail[id] - 1, 0);
          ic3Fail[id]++;
        }
        break;
      }
    }

    opts.timeout = timeout;
    prob = exp(-ic3Fail[id] * iter / double(ic3Factor));
    if(rand() < prob * RAND_MAX) {
      if(verbosity > Options::Informative)
        cout << "Fair: (" << timeout << "s)" << endl;
      rv = Fair::fairPath(model(), opts, &cex, &proofs);

      if(rv.returnType != MC::Unknown) {
        if(iter > 0) {
          ic3Fail[id] = max(ic3Fail[id] - 1, 0);
          bmcFail[id]++;
        }
        break;
      }
    }

    timeout *= 2;
    ++iter;
  }
#endif

  eat = (ExprAttachment *) model().attachment(Key::EXPR);
  eat->clearOutputFns();
  eat->setOutputFns(outputs, outputFns);
  eat->clearInitialConditions();
  eat->addInitialConditions(init);
  model().release(eat);

  if(rv.returnType == MC::Proof)
    return false;
  return true;
}


bool IICTLAction::reach(const vector<ID> & source, ID targetID,
                        SAT::Clauses & targetCNF,
                        vector<SAT::Clauses> & constraints,
                        SAT::Clauses & negConstraints,
                        IC3::ProofProcType ppt, vector<SAT::Clauses> & proofs,
                        vector<Transition> & cex, ID id, bool isEU) {

  ExprAttachment * eat = (ExprAttachment *) model().attachment(Key::EXPR);
  //Change the output function
  vector<ID> outputs = eat->outputs();
  vector<ID> outputFns = eat->outputFns();
  eat->clearOutputFns();
  ID o0 = ev->newVar("_ooo_");
  eat->setOutputFn(o0, targetID);

  //Change the initial conditions
  vector<ID> init(eat->initialConditions());
  eat->clearInitialConditions();
  eat->addInitialConditions(source);
  model().release(eat);

  //Prepare BMC
  BMC::BMCOptions bopts;
  bopts.useCOI = false;
  bopts.lo = 0;
  size_t bound;
  bopts.bound = &bound;
  bopts.printCex = true;
  bopts.constraints = &constraints;
  bopts.iictl = true;
  bopts.iictl_clauses = &targetCNF;

  //Prepare IC3
  IC3::IC3Options & opts = _opts->reach_opts;
  //IC3::IC3Options opts(model().options());
  opts.iictl = true;
  opts.iictl_clauses = &targetCNF;
  opts.constraints = &constraints;
  opts.negConstraints = &negConstraints;
  opts.printCex = true;
  opts.proofProc = ppt;
  bool propagate = !model().options().count("iictl_xic3propagate");
  if(isEU)
    propagate = false;
  opts.propagate = propagate;
  opts.initCube = &initialConditions;
  bool incremental = model().options().count("iictl_ic3incremental");
  //If source is not initial, do not use incrementality
  vector<ID> st = source;
  sort(st.begin(), st.end());
  if(st != initialConditions || isEU) {
    incremental = false;
  }
  opts.incremental = incremental;
  IC3::CubeSet indCubes;

  MC::ReturnValue rv;
  opts.timeout = 2;
  rv = runIC3(opts, targetID, cex, proofs, incremental, propagate);
  if(rv.returnType == MC::Unknown) {

    bopts.timeout = 5;
    bound = 8191; //Maximum number of primes allowed by the expression package
    rv = BMC::check(model(), bopts, &cex);

    if(rv.returnType != MC::CEX) {
      opts.timeout = -1;

      rv = runIC3(opts, targetID, cex, proofs, incremental, propagate);
    }
  }

#if 0
  int timeout = 1;
  int iter = 0;
  while(true) {

    bopts.timeout = timeout;
    bound = 8191; //Maximum number of primes allowed by the expression package
    double prob = exp(-bmcFail[id] * iter / double(bmcFactor));
    if(rand() < prob * RAND_MAX) {
      if(verbosity > Options::Informative)
        cout << "BMC: (" << timeout << "s)" << endl;
      rv = BMC::check(model(), bopts, &cex);
      bopts.lo = bound; //Start where BMC stopped last time

      if(rv.returnType == MC::CEX) {
        if(iter > 0) {
          bmcFail[id] = max(bmcFail[id] - 1, 0);
          ic3Fail[id]++;
        }
        break;
      }
    }

    opts.timeout = timeout;

    prob = exp(-ic3Fail[id] * iter / double(ic3Factor));
    if(rand() < prob * RAND_MAX) {
      if(verbosity > Options::Informative)
        cout << "IC3: (" << timeout << "s)" << endl;
      rv = runIC3(opts, targetID, cex, proofs, incremental, propagate);

      if(rv.returnType != MC::Unknown) {
        if(iter > 0) {
          ic3Fail[id] = max(ic3Fail[id] - 1, 0);
          bmcFail[id]++;
        }
        break;
      }
    }

    ++iter;
    timeout *= 2;
  }
#endif

  //Restore the original model
  eat = (ExprAttachment *) model().attachment(Key::EXPR);
  eat->clearOutputFns();
  eat->setOutputFns(outputs, outputFns);
  eat->clearInitialConditions();
  eat->addInitialConditions(init);
  model().release(eat);
  
  if(rv.returnType == MC::CEX)
    return true;

  assert(rv.returnType == MC::Proof);
  return false;
}

bool IICTLAction::isUndecided(const vector<ID> & state, ID id) {
  //An undecided state is a potentially reachable state that is in the upper
  //bound and not in the lower bound, i.e. is in GR & UB & !LB = 
  //GR & UB & (!QLB | !UB) = (GR & UB & !QLB) | (GR & UB & !UB) = (GR & UB & !QLB)
  //Adding reachability is not really necessary because we always call this
  //function with reachable states
  assert(boundsEqual.find(id) != boundsEqual.end());
  if(boundsEqual[id] || UBId[id] == ev->bfalse() || QLBId[id] == ev->btrue())
    return false;

  SAT::Manager * sman = model().newSATManager();
  SAT::Manager::View * sview = sman->newView(*ev);
  sview->add(GR);
  sview->add(UB[id]);
  SAT::Clauses negQLB;
  Expr::CNFIZE(*ev, ev->apply(Expr::Not, QLBId[id]), negQLB);
  sview->add(negQLB);

  vector<ID> assumps = state;
  bool sat = sview->sat(&assumps);

  delete sview;
  delete sman;

  return sat;
}

bool IICTLAction::equivalent(ID id1, ID id2) {
  SAT::Manager * sman = model().newSATManager();
  SAT::Manager::View * sview = sman->newView(*ev);

  SAT::Clauses clauses;
  Expr::CNFIZE(*ev, ev->apply(Expr::Not, ev->apply(Expr::Equiv, id1, id2)), 
               clauses);

  try {
    sview->add(clauses);
  }
  catch(SAT::Trivial tr) {
    //Unsat (equivalent)
    delete sview;
    delete sman;
    return true;
  }

  bool sat = sview->sat();
  delete sview;
  delete sman;

  return !sat;
}

RefineType IICTLAction::update(ID id, RefineType childRefinement) {

  int nArgs;
  ID const * const child = ev->arguments(id, &nArgs);

  assert(childRefinement != None);

  RefineType possibleRefinement = None;

  ID currentUB = UBId[id];
  ID currentQLB = QLBId[id];

  switch(ev->op(id)) {

    case Expr::Not: {
      if(childRefinement == Upper || childRefinement == Both) {
        //Child's upper bound has been updated. Update this node's lower bound
        QLBId[id] = ev->apply(Expr::Not, UBId[child[0]]);
        //Rebuild CNF
        QLB[id].clear();
        Expr::CNFIZE(*ev, QLBId[id], QLB[id]);
      }
      if(childRefinement == Lower || childRefinement == Both) {
        //Child's lower bound has been updated. Update this node's upper bound
        //UB = !LB(child) = !(QLB(child) & UB(child))
        UBId[id] = ev->apply(Expr::Or, ev->apply(Expr::Not, QLBId[child[0]]),
                                       ev->apply(Expr::Not, UBId[child[0]]));
        //Rebuild CNF
        UB[id].clear();
        Expr::CNFIZE(*ev, UBId[id], UB[id]);
      }
      possibleRefinement = childRefinement == Both ? Both :
                               childRefinement == Upper ?  Lower : Upper;
      break;
    }
    case Expr::And: {
      if(childRefinement == Upper || childRefinement == Both) {
        UBId[id] = ev->apply(Expr::And, UBId[child[0]], UBId[child[1]]);
        UB[id].clear();
        Expr::CNFIZE(*ev, UBId[id], UB[id]);
      }
      if(childRefinement == Lower || childRefinement == Both) {
        QLBId[id] = ev->apply(Expr::And, QLBId[child[0]], QLBId[child[1]]);
        QLB[id].clear();
        Expr::CNFIZE(*ev, QLBId[id], QLB[id]);
      }
      possibleRefinement = childRefinement == Both ? Both :
                               childRefinement == Upper ?  Upper : Lower;
      break;
    }
    case Expr::X:
      //No updates possible
      break;
    case Expr::F: {
      if(childRefinement == Lower || childRefinement == Both) {
        baseQLB[id] = ev->apply(Expr::Or, baseQLB[id], QLBId[child[0]]);
        renewQLB(id);
        possibleRefinement = Lower;
      }
      break;
    }
    case Expr::U: {
      if(childRefinement == Lower || childRefinement == Both) {
        baseQLB[id] = ev->apply(Expr::Or, baseQLB[id], QLBId[child[1]]);
        renewQLB(id);
        possibleRefinement = Lower;
      }
      if(childRefinement == Upper || childRefinement == Both) {
        UBId[id] = ev->apply(Expr::And, UBId[id], 
                             ev->apply(Expr::Or, UBId[child[0]], UBId[child[1]]));
        UB[id].clear();
        Expr::CNFIZE(*ev, UBId[id], UB[id]);
        possibleRefinement = Upper;
      }
      break;
    }
    case Expr::G: {
      if(childRefinement == Upper || childRefinement == Both) {
        UBId[id] = ev->apply(Expr::And, UBId[id], UBId[child[0]]);
        UB[id].clear();
        Expr::CNFIZE(*ev, UBId[id], UB[id]);
        possibleRefinement = Upper;
      }
      break;
    }
    default:
      assert(false);
  }

  if(possibleRefinement == None)
    return None;

  bool ubChanged = false, lbChanged = false;
  if(possibleRefinement == Upper || possibleRefinement == Both) {
    //Check if a semantic change occurred to the upper bound
    ubChanged = !equivalent(currentUB, UBId[id]);
  }
  if(possibleRefinement == Lower || possibleRefinement == Both) {
    //Check if a semantic change occurred to the lower bound
    lbChanged = !equivalent(currentQLB, QLBId[id]);
  }
  
  if(ubChanged && lbChanged)
    return Both;
  if(ubChanged)
    return Upper;
  if(lbChanged)
    return Lower;
  return None;
}

bool IICTLAction::updateAncestorsBounds(ID id, RefineType refinement) {

  ToUpdate toUpdate(isDescendantOf);
  pair<Expr::IDMMap::iterator, Expr::IDMMap::iterator> ret = parents.equal_range(id);
  for(Expr::IDMMap::const_iterator it = ret.first; it != ret.second; ++it) {
    toUpdate.insert(ToUpdate::value_type(it->second, refinement));
  }

  while(!toUpdate.empty()) {
    ToUpdate::iterator tu = toUpdate.begin();
    RefineType nodeRefinement = update(tu->first, tu->second);
    if(nodeRefinement != None) {
      if(tu->first != property) {
        //Add its parents to the set of nodes to update
        pair<Expr::IDMMap::iterator, Expr::IDMMap::iterator> ret = parents.equal_range(tu->first);
        for(Expr::IDMMap::const_iterator it = ret.first; it != ret.second; ++it) {
          ToUpdate::iterator uit = toUpdate.find(it->second);
          if(uit == toUpdate.end())
            toUpdate.insert(ToUpdate::value_type(it->second, nodeRefinement));
          else {
            //Update refinement
            RefineType currentRefinement = uit->second;
            assert(currentRefinement != None);
            if(currentRefinement != nodeRefinement) {
              toUpdate.erase(uit);
              toUpdate.insert(ToUpdate::value_type(it->second, Both));
            }
          }
        }
      }
      else { //root
        //Check if all initial states are in LB (I => LB)
        vector<ID> dummy;
        if(lbContainsInitStates(dummy)) {
          throw Safe();
        }
        //Check if any of the initial states are not in UB (I =/> UB)
        if(!ubContainsInitStates()) {
          throw CEX();
        }
      }
    }
    toUpdate.erase(tu);
  }
  return false;
}

bool IICTLAction::decide(const vector<ID> & state, ID id, BoundChange skipGen) {

  _opts->reach_opts.abs_pattern = id;
  _opts->fair_opts.ic3_opts.abs_pattern = id;

  if(lbContainsStates(id, state))
    return true;
  if(!ubContainsStates(id, state))
    return false;

  int nArgs;
  ID const * const args = ev->arguments(id, &nArgs);

  vector<ID> child;
  for(int i = 0; i < nArgs; ++i) {
    child.push_back(args[i]);
  }

  switch(ev->op(id)) {
  
  case Expr::Not: {
    if(verbosity > Options::Informative)
      cout << "========== Not ==========" << endl;
    BoundChange chSkipGen;
    if(skipGen == NoSkip || skipGen == SkipForBoth)
      chSkipGen = skipGen;
    else if(skipGen == SkipForUpper)
      chSkipGen = SkipForLower;
    else
      chSkipGen = SkipForUpper;

    return !decide(state, child[0], chSkipGen);
  }

  case Expr::And: {
    if(verbosity > Options::Informative)
      cout << "========== And ==========" << endl;
    BoundChange chSkipGen;
    bool ch0Undec = isUndecided(state, child[0]);
    bool ch1Undec = isUndecided(state, child[1]);
    assert(ch0Undec || ch1Undec);
    bool bothUndec = ch0Undec && ch1Undec;
    if(bothUndec) {
      if(skipGen == NoSkip || skipGen == SkipForLower)
        chSkipGen = NoSkip;
      else //Upper or Both
        chSkipGen = SkipForUpper;

      if(!decide(state, child[0], chSkipGen)) {
        //No need to query the second child
        return false;
      }
      else {
        //Might not be enough to decide the mission state
        //First check if the state is still undecided
        if(lbContainsStates(id, state))
          return true;
        if(!ubContainsStates(id, state))
          return false;
        //The first is now decided, so pass skipGen as it is
        return decide(state, child[1], skipGen);
      }
    }
    else {
      //Only one child is undecided, so pass skipGen as it is
      return decide(state, ch0Undec ? child[0] : child[1], skipGen);
    }
  }

  case Expr::X: {
    if(verbosity > Options::Informative)
      cout << "========== EX ==========" << endl;
    bool decision;
    ID oldChildQLBId = ev->bfalse();
    bool first = true;
    while(true) {
      //We can only be here if this is the first iteration, or if a refinement
      //of the child resulted in an update to its upper bound, because if it
      //resulted in a refinement to its lower bound, we would have added the
      //mission state to our lower bound and exited the loop

      //Create a SAT manager and a view for the upper bound
      //Query state & T & UB'
      //TODO: Use incremental SAT instead of deleting and creating SAT managers
      //and views each time, and adding the transition relation
      SAT::Manager * satMan = model().newSATManager();
      SAT::Manager::View * satView = satMan->newView(*ev);
      vector<ID> ubInputs;
      vector<ID> ubNState;
      bool sat;
      vector<ID> assumps;
      SAT::Assignment asgn;
      assert(UBId.find(child[0]) != UBId.end());
      if(UBId[child[0]] == ev->bfalse()) {
        sat = false;
      }
      else {
        satView->add(tr);
        //Add UB'[child]
        assert(UB.find(child[0]) != UB.end());
        for(SAT::Clauses::const_iterator it = UB[child[0]].begin();
            it != UB[child[0]].end(); ++it) {
          vector<ID> cls;
          //Prime clause
          primeVector(*ev, *it, cls);
          try {
            satView->add(cls);
          }
          catch(SAT::Trivial tr) {
            assert(tr.value());
          }
        }

        assumps = state;
        resetAssign(primedStateAsgn);
        asgn = primedStateAsgn;
        //Add inputs
        ExprAttachment const * eat = (ExprAttachment const *)
                                     model().constAttachment(Key::EXPR);
        const vector<ID> & inputs = eat->inputs();
        for(vector<ID>::const_iterator it = inputs.begin(); it != inputs.end(); ++it) {
          asgn.insert(SAT::Assignment::value_type(*it, SAT::Unknown));
        }
        model().constRelease(eat); 
        bool ecore = true; //extract UNSAT core
        if(skipGen == SkipForUpper || skipGen == SkipForBoth)
          ecore = false;
        sat = satView->sat(&assumps, &asgn, ecore ? &assumps : NULL);
      }
      if(verbosity > Options::Informative)
        cout << "EX UB: " << (sat ? "SAT" : "UNSAT") << endl;
      if(!sat) {
        if(skipGen != SkipForUpper && skipGen != SkipForBoth) {
          //Apply brute-force to extract a minimum UNSAT core
          bool changed = true;
          sort(assumps.begin(), assumps.end());
          while(changed) {
            changed = false;
            for(unsigned i = 0; i < assumps.size(); ++i) {
              vector<ID> rassumps;
              for(unsigned j = 0; j < assumps.size(); ++j) {
                if(j != i)
                  rassumps.push_back(assumps[j]);
              }
              //Check if is still UNSAT
              bool sat2 = satView->sat(&rassumps, NULL, &rassumps);
              if(!sat2) {
                changed = true;
                --i;
                assumps = rassumps;
              }
            }
          }
        }
        delete satView;
        delete satMan;
        //Remove state(s) from UB by adding the negation of the UNSAT-core
        //reduced cube
        if(assumps.empty()) {
          //States in the upper bound are unreachable!
          UBId[id] = ev->bfalse();
          UB[id].clear();
          UB[id].push_back(SAT::Clause(1, ev->bfalse()));
        }
        else {
          vector<ID> cls;
          complement(*ev, assumps, cls);
          if(verbosity > Options::Verbose) {
            set<ID> ids(cls.begin(), cls.end());
            ExprAttachment const * const eat = (ExprAttachment const *)
                model().constAttachment(Key::EXPR);
            const vector<ID> & svs = eat->stateVars();
            for(vector<ID>::const_iterator it = svs.begin(); it != svs.end(); ++it) {
              if(ids.find(*it) != ids.end()) {
                cout << "1";
              }
              else if (ids.find(ev->apply(Expr::Not, *it)) != ids.end()) {
                cout << "0";
              }
              else {
                cout << "-";
              }
            }
            cout << endl;
            model().constRelease(eat);
          }
          UBId[id] = ev->apply(Expr::And, UBId[id], ev->apply(Expr::Or, cls));
          //Add clause to the upper bound
          UB[id].push_back(cls);
          //And to lifting SAT database
          assert(liftSatViews.find(id) != liftSatViews.end());
          liftSatViews[id]->add(cls);
        }
        decision = false;
        updateAncestorsBounds(id, Upper);
        break;
      }
      else { //sat
        fullAssignOf(*ev, model(), asgn, ubNState, ubInputs);
        //Remove primes from state
        for(vector<ID>::iterator it = ubNState.begin(); it != ubNState.end(); ++it) {
          *it = ev->unprime(*it);
        }

        //Query: state & T & LB' = state & T & QLB' & UB'
        vector<ID> lbInputs;
        vector<ID> lbNState;
        vector<ID> assumps;
        assert(boundsEqual.find(child[0]) != boundsEqual.end());
        if(!first && QLBId[child[0]] == oldChildQLBId) {
          //This is at least the second iteration, and the child's lower bound
          //hasn't changed from last iteration, so no need to repeat the query 
          sat = false;
        }
        else if(!boundsEqual[child[0]]) {

          oldChildQLBId = QLBId[child[0]];

          assert(QLBId.find(child[0]) != QLBId.end());
          if(QLBId[child[0]] == ev->bfalse()) {
            sat = false;
          }
          else {
            //Add QLB'[child] to SAT database
            for(SAT::Clauses::const_iterator it = QLB[child[0]].begin(); 
                it != QLB[child[0]].end(); ++it) {
              vector<ID> cls;
              primeVector(*ev, *it, cls);
              try {
                satView->add(cls);
              }
              catch(SAT::Trivial tr) {
                assert(tr.value());
              }
            }
            assumps = state;
            resetAssign(asgn);
            sat = satView->sat(&assumps, &asgn);
            delete satView;
            delete satMan;
            if(sat) {
              fullAssignOf(*ev, model(), asgn, lbNState, lbInputs);
              //Remove primes from state
              for(vector<ID>::iterator it = lbNState.begin(); it != lbNState.end(); ++it) {
                *it = ev->unprime(*it);
              }
            }
          }
          if(verbosity > Options::Informative)
            cout << "EX LB: " << (sat ? "SAT" : "UNSAT") << endl;
        }
        if(sat) {
          if(boundsEqual[child[0]]) {
            //Lower bound query wasn't performed
            lbInputs = ubInputs;
            lbNState = ubNState;
          }
          if(skipGen != SkipForLower && skipGen != SkipForBoth) {
            vector<Transition> twoStateTrace;
            twoStateTrace.push_back(Transition(state, lbInputs));
            twoStateTrace.push_back(Transition(lbNState, vector<ID>()));
            generalizeTwoStateTrace(twoStateTrace, id, child[0]);
          }
          else {
            QLBcubes[id].push_back(state);
            renewQLB(id);
          }
          decision = true;
          updateAncestorsBounds(id, Lower);
          break;
        }
        else {
          //We have a state that is undecided for our child
          //We can never get here if the bounds were equal
          assert(!boundsEqual[child[0]]);
          BoundChange chSkipGen;
          if(skipGen == NoSkip || skipGen == SkipForUpper)
            chSkipGen = NoSkip;
          else
            chSkipGen = SkipForLower;
          if(decide(ubNState, child[0], chSkipGen)) {
            //No need to perform another iteration
            if(skipGen != SkipForLower && skipGen != SkipForBoth) {
              vector<Transition> twoStateTrace;
              twoStateTrace.push_back(Transition(state, ubInputs));
              twoStateTrace.push_back(Transition(ubNState, vector<ID>()));
              generalizeTwoStateTrace(twoStateTrace, id, child[0]);
            }
            else {
              QLBcubes[id].push_back(state);
              renewQLB(id);
            }
            decision = true;
            updateAncestorsBounds(id, Lower);
            break;
          }
          //Check if the state is still undecided before looping again
          if(lbContainsStates(id, state))
            return true;
          if(!ubContainsStates(id, state))
            return false;
        }
      }
      first = false;
    }
    return decision;
  }

  case Expr::F: {
    if(verbosity > Options::Informative)
      cout << "========== EF ==========" << endl;
    bool decision;
    ID oldChildQLBId = ev->bfalse();
    bool first = true;
    while(true) {
      //We can only be here if this is the first iteration, or if the state
      //found from upper bound query in the previous iteration turned out not
      //to satisfy the child
      vector<Transition> ubCex;
      assert(boundsEqual.find(child[0]) != boundsEqual.end());
      if(!boundsEqual[child[0]]) {
        //Perform an IC3 query
        //    initial state: state
        //    property: AG !UB[child]
        //    ouptut: UB[child]
        assert(UBId.find(child[0]) != UBId.end());
        assert(UB.find(child[0]) != UB.end());
        //Add UB[id] & UB'[id] & GR as constraints
        vector<SAT::Clauses> constraints(1, GR);
        SAT::Clauses negConstraints(1, SAT::Clause()); //all constraints are optional, so set to false
        if(UBId[id] != ev->btrue()) {
          constraints[0].insert(constraints[0].end(), UB[id].begin(), UB[id].end());
          for(vector< vector<ID> >::const_iterator it = UB[id].begin();
              it != UB[id].end(); ++it) {
            vector<ID> cls;
            primeVector(*ev, *it, cls);
            constraints[0].push_back(cls);
          }
        }
        IC3::ProofProcType proofProc = (skipGen == SkipForUpper || 
                                        skipGen == SkipForBoth) ? 
                                        IC3::NONE : IC3::WEAKEN;

        vector<SAT::Clauses> proofs;
        int64_t startTime = Util::get_user_cpu_time(); 
        bool ubReachable = reach(state, UBId[child[0]], UB[child[0]], constraints, negConstraints,
                                 proofProc, proofs, ubCex, id);
        if(verbosity > Options::Informative) {
          cout << "EF UB: " << (ubReachable ? "SAT " : "UNSAT ")
               << (Util::get_user_cpu_time() - startTime) / 1000000.0
               << " seconds" << endl;
          if(ubReachable && verbosity > Options::Verbose) {
            //Print the last state in trace
            const vector<ID> & last = ubCex.back().state;
            for(vector<ID>::const_iterator it = last.begin(); it != last.end(); ++it)
              cout << Expr::stringOf(*ev, *it) << " "; 
            cout << endl;
            vector<ID> copy = ubCex.back().state;
            sort(copy.begin(), copy.end());
            for(vector<ID>::const_iterator it = copy.begin(); it != copy.end(); ++it)
              cout << (ev->op(*it) == Expr::Not ?  "0" : "1"); 
            cout << endl;
          }
        }
      
        if(!ubReachable) {
          //(P & F) is inductive
          //P = property = !UB[child]
          //F = proof from IC3 (doesn't include the property)
          //Remove state(s) from UB by removing (P & F) (or adding !(P & F))
          const vector< vector<ID> > & proof = proofs[0];
          //Create an expression for !(P & F) = !P | !F
          vector<ID> cubes;
          for(vector< vector<ID> >::const_iterator it = proof.begin();
              it != proof.end(); ++it) {
            vector<ID> cube;
            complement(*ev, *it, cube);
            cubes.push_back(ev->apply(Expr::And, cube));
          }
          cubes.push_back(UBId[child[0]]);
          ID toAdd = ev->apply(Expr::Or, cubes);
          //New UB = oldUB & !(P & F)
          UBId[id] = ev->apply(Expr::And, UBId[id], toAdd);
          //Update UB clauses
          //Create CNF for toAdd
          SAT::Clauses toAddCNF;
          Expr::CNFIZE(*ev, toAdd, toAddCNF);
          UB[id].insert(UB[id].end(), toAddCNF.begin(), toAddCNF.end());
          //Add new clauses of UB to lifting database
          if(UBId[id] != ev->bfalse()) {
            liftSatViews[id]->add(toAddCNF);
          }
          decision = false;
          updateAncestorsBounds(id, Upper);
          break;
        }
      }

      vector<Transition> lbCex;
      vector<SAT::Clauses> proofs;
      if(first || QLBId[child[0]] != oldChildQLBId) {
        oldChildQLBId = QLBId[child[0]];
        //Perform another IC3 query
        //    initial state: state
        //    property: AG !(QLB[id] & UB[id])
        //    ouptut: QLB[id] & UB[id]

        assert(QLBId.find(id) != QLBId.end());
        ID targetID = ev->apply(Expr::And, QLBId[id], UBId[id]);
        assert(QLB.find(id) != QLB.end());
        SAT::Clauses target;
        Expr::CNFIZE(*ev, targetID, target);
        vector<SAT::Clauses> constraints(1, GR);
        SAT::Clauses negConstraints(1, SAT::Clause()); //all constraints are optional, so set to false
        if(UBId[id] != ev->btrue()) {
          constraints[0].insert(constraints[0].end(), UB[id].begin(), UB[id].end());
          for(vector< vector<ID> >::const_iterator it = UB[id].begin();
              it != UB[id].end(); ++it) {
            vector<ID> cls;
            primeVector(*ev, *it, cls);
            constraints[0].push_back(cls);
          }
        }
        IC3::ProofProcType proofProc = (skipGen == SkipForUpper ||
                                       skipGen == SkipForBoth) ?
                                       IC3::NONE : IC3::WEAKEN;

        int64_t startTime = Util::get_user_cpu_time(); 
        bool lbReachable = reach(state, targetID, target, constraints, negConstraints, proofProc,
                                 proofs, lbCex, id);
        if(verbosity > Options::Informative)
          cout << "EF LB: " << (lbReachable ? "SAT " : "UNSAT ")
               << (Util::get_user_cpu_time() - startTime) / 1000000.0
               << " seconds" << endl;

        if(lbReachable) {
          if(skipGen != SkipForLower && skipGen != SkipForBoth)
            generalizeEFTrace(lbCex, id);
          else {
            //Add all the states on the trace directly
            for(vector<Transition>::const_iterator it = lbCex.begin(); it != lbCex.end();
                ++it) {
              QLBcubes[id].push_back(it->state);
            }
            //Renew QLB
            renewQLB(id);
          }
          decision = true;
          updateAncestorsBounds(id, Lower);
          break;
        }
        else if(boundsEqual[child[0]]) {
          //(P & F) is inductive
          //P = property = !(UB[id] & QLB[id])
          //F = proof from IC3 (doesn't include the property)
          //Remove state(s) from UB by removing (P & F) (or adding !(P & F))
          const vector< vector<ID> > & proof = proofs[0];
          //Create an expression for !(P & F)
          vector<ID> cubes;
          for(vector< vector<ID> >::const_iterator it = proof.begin();
              it != proof.end(); ++it) {
            vector<ID> cube;
            complement(*ev, *it, cube);
            cubes.push_back(ev->apply(Expr::And, cube));
          }
          cubes.push_back(ev->apply(Expr::And, UBId[id], QLBId[id]));
          ID toAdd = ev->apply(Expr::Or, cubes);
          //New UB = oldUB & !(P & F)
          UBId[id] = ev->apply(Expr::And, UBId[id], toAdd);
          //Update UB clauses
          //Create CNF for toAdd
          SAT::Clauses toAddCNF;
          Expr::CNFIZE(*ev, toAdd, toAddCNF);
          UB[id].insert(UB[id].end(), toAddCNF.begin(), toAddCNF.end());
          //Add new clauses of UB to lifting database
          if(UBId[id] != ev->bfalse()) {
            liftSatViews[id]->add(toAddCNF);
          }
          decision = false;
          updateAncestorsBounds(id, Upper);
          break;
        }
      }

      //state is undecided
      assert(!boundsEqual[child[0]]);

      //Decide last state in UB query cex trace
      BoundChange chSkipGen;
      if(skipGen == NoSkip || skipGen == SkipForUpper)
        chSkipGen = NoSkip;
      else
        chSkipGen = SkipForLower;

      if(decide(ubCex.back().state, child[0], chSkipGen)) {
        //No need to perform another iteration
        //Perform lifting on UB cex
        if(skipGen != SkipForLower && skipGen != SkipForBoth) {
          generalizeEFTrace(ubCex, id);
        }
        else {
          for(vector<Transition>::const_iterator it = ubCex.begin(); it != ubCex.end(); ++it) {
            QLBcubes[id].push_back(it->state);
          }
          renewQLB(id);
        }
        decision = true;
        updateAncestorsBounds(id, Lower);
        break;
      }
      //Check if the state is still undecided before looping again
      if(lbContainsStates(id, state))
        return true;
      if(!ubContainsStates(id, state))
        return false;
      
      first = false;
    }
    return decision;
  }

  case Expr::G: {
    if(verbosity > Options::Informative)
      cout << "========== EG ==========" << endl;

    bool decision;
    ID oldUBId, oldChildQLBId = ev->bfalse();
    bool first = true;
    Lasso ubLasso;
    while(true) {
      //Perform a Fair query
      //    initial state: state
      //    property: AF !UB[id]
      //    invariant constraints: UB[id]
      assert(boundsEqual.find(child[0]) != boundsEqual.end());
      if(first || UBId[id] != oldUBId) {
        ubLasso.stem.clear();
        ubLasso.loop.clear();
        oldUBId = UBId[id];
        assert(UB.find(id) != UB.end());
        SAT::Clauses constraints = GR;
        SAT::Clauses negConstraints; //UB[id] is necessary
        if(UBId[id] != ev->btrue()) {
          constraints.insert(constraints.end(), UB[id].begin(), UB[id].end());
          for(vector< vector<ID> >::const_iterator it = UB[id].begin(); it != UB[id].end(); ++it) {
            vector<ID> cls;
            primeVector(*ev, *it, cls);
            constraints.push_back(cls);
          }
          Expr::tseitin(*ev, ev->apply(Expr::Not,
                             ev->apply(Expr::And, UBId[id], primeFormula(*ev, UBId[id]))), negConstraints);
        }
        else {
          negConstraints.push_back(SAT::Clause());
        }

        IC3::ProofProcType proofProc = (IC3::ProofProcType) model().options()["iictl_fair_grppt"].as<int>();
        bool globalLast = !model().options().count("iictl_fair_global_first");
        if(skipGen == SkipForUpper || skipGen == SkipForBoth) {
          //Use Fair's defaults
          proofProc = IC3::STRENGTHEN;
          globalLast = false;
        }

        vector<SAT::Clauses> proofs;
        int64_t startTime = Util::get_user_cpu_time(); 
        bool ubFairCycle = fair(state, constraints, negConstraints, proofProc, globalLast,
                                proofs, ubLasso, id);
        if(verbosity > Options::Informative)
          cout << "EG UB: " << (ubFairCycle ? "SAT " : "UNSAT ")
               << (Util::get_user_cpu_time() - startTime) / 1000000.0
               << " seconds" << endl;

        if(!ubFairCycle) {
          //Remove state(s) from UB by adding the negation of the proof(s)
          //Proof = set of clauses
          //1) First create a CNF for the negation of the proof
          //a) Create a single ID for the negation of the proof to cnfize
          const vector< vector<ID> > & proof = proofs[0];
          vector<ID> cubes;
          for(vector< vector<ID> >::const_iterator it = proof.begin();
              it != proof.end(); ++it) {
            vector<ID> cube;
            complement(*ev, *it, cube);
            cubes.push_back(ev->apply(Expr::And, cube));
          }
          ID nproofID = ev->apply(Expr::Or, cubes);
          //Update UBId
          UBId[id] = ev->apply(Expr::And, UBId[id], nproofID);
          //b) Cnfize nproofID
          vector< vector<ID> > negProofCNF;
          Expr::CNFIZE(*ev, nproofID, negProofCNF);
          //2) Conjoin the old UB with the negation of the proof
          UB[id].insert(UB[id].end(), negProofCNF.begin(), negProofCNF.end());
          //Add new clauses of UB to lifting database
          if(UBId[id] != ev->bfalse()) {
            liftSatViews[id]->add(negProofCNF);
          }

          decision = false;
          updateAncestorsBounds(id, Upper);
          break;
        }
        else if(boundsEqual[child[0]]) {
          //Add all states in ubLasso to QLB after generalization
          if(skipGen != SkipForLower && skipGen != SkipForBoth) {
            generalizeLasso(ubLasso, id, child[0]);
          }
          else {
            for(vector<Transition>::const_iterator it = ubLasso.stem.begin();
                it != ubLasso.stem.end(); ++it) {
              QLBcubes[id].push_back(it->state);
            }
            for(vector<Transition>::const_iterator it = ubLasso.loop.begin();
                it != ubLasso.loop.end(); ++it) {
              QLBcubes[id].push_back(it->state);
            }
            renewQLB(id);
          }
          decision = true;
          updateAncestorsBounds(id, Lower);
          break;
        }
      }

      Lasso lbLasso;
      if(first || QLBId[child[0]] != oldChildQLBId) {
        oldChildQLBId = QLBId[child[0]];
        if(QLBId[child[0]] != ev->bfalse()) {
          //Perform another Fair query
          //  initial state: state
          //  property: AF !LB[child] = AF !(QLB[child] & UB[child])
          //  invariant constraints: QLB[child] & UB[child]
          //  No need to add UB[child] to constraints because we add UB[id]
          //  which is stronger
          assert(QLB.find(child[0]) != QLB.end());
          SAT::Clauses constraints = GR;
          SAT::Clauses negConstraints;
          //Add UB and UB'
          if(UBId[id] != ev->btrue()) {
            constraints.insert(constraints.end(), UB[id].begin(), UB[id].end());
            for(vector< vector<ID> >::const_iterator it = UB[id].begin(); it != UB[id].end(); ++it) {
              vector<ID> cls;
              primeVector(*ev, *it, cls);
              constraints.push_back(cls);
            }
          }
          //Add QLB[child] and QLB'[child]
          if(QLBId[child[0]] != ev->btrue()) {
            constraints.insert(constraints.end(), QLB[child[0]].begin(), QLB[child[0]].end());
            for(vector< vector<ID> >::const_iterator it = QLB[child[0]].begin(); it != QLB[child[0]].end(); ++it) {
              vector<ID> cls;
              primeVector(*ev, *it, cls);
              constraints.push_back(cls);
            }
          }
          vector<ID> conj;
          conj.push_back(UBId[id]);
          conj.push_back(primeFormula(*ev, UBId[id]));
          conj.push_back(QLBId[child[0]]);
          conj.push_back(primeFormula(*ev, QLBId[child[0]]));
          Expr::tseitin(*ev, ev->apply(Expr::Not, ev->apply(Expr::And, conj)), negConstraints);
          IC3::ProofProcType proofProc = (IC3::ProofProcType)
              model().options()["iictl_fair_grppt"].as<int>();
          bool globalLast = !model().options().count("iictl_fair_global_first");
          if(skipGen == SkipForUpper || skipGen == SkipForBoth) {
            //Use Fair's defaults
            proofProc = IC3::STRENGTHEN;
            globalLast = false;
          }

          vector<SAT::Clauses> proofs;
          int64_t startTime = Util::get_user_cpu_time();
          bool lbFairCycle = fair(state, constraints, negConstraints, proofProc, globalLast,
                                  proofs, lbLasso, id);
          if(verbosity > Options::Informative)
            cout << "EG LB: " << (lbFairCycle ? "SAT " : "UNSAT ")
                 << (Util::get_user_cpu_time() - startTime) / 1000000.0
                 << " seconds" << endl;
          if(lbFairCycle) {
            //Add all states in lbLasso to QLB after generalization
            if(skipGen != SkipForLower && skipGen != SkipForBoth) {
              generalizeLasso(lbLasso, id, child[0]);
            }
            else {
              for(vector<Transition>::const_iterator it = lbLasso.stem.begin();
                  it != lbLasso.stem.end(); ++it) {
                QLBcubes[id].push_back(it->state);
              }
              for(vector<Transition>::const_iterator it = lbLasso.loop.begin();
                  it != lbLasso.loop.end(); ++it) {
                QLBcubes[id].push_back(it->state);
              }
              renewQLB(id);
            }
            decision = true;
            updateAncestorsBounds(id, Lower);
            break;
          }
        }
      }  

      assert(!boundsEqual[child[0]]);
      //Decide an undecided state in ubLasso
      vector<Transition> allTransitions = ubLasso.stem;
      allTransitions.insert(allTransitions.end(), ubLasso.loop.begin(),
                            ubLasso.loop.end());
      bool oneUndecided = false;
      for(vector<Transition>::const_iterator it = allTransitions.begin();
          it != allTransitions.end(); ++it) {
        if(isUndecided(it->state, child[0])) {
          decide(it->state, child[0], NoSkip);
          oneUndecided = true;
          break;
        }
      }
      assert(oneUndecided);
      //Check if the state is still undecided before looping again
      if(lbContainsStates(id, state))
        return true;
      if(!ubContainsStates(id, state))
        return false;

      first = false;
    }
    return decision;
  }

  case Expr::U: {
    if(verbosity > Options::Informative)
      cout << "========== EU ==========" << endl;
    bool decision;
    ID oldChild0UBId = ev->bfalse();
    ID oldChild1UBId = ev->bfalse();
    ID oldChild0QLBId = ev->bfalse();
    ID oldChild1QLBId = ev->bfalse();
    bool first = true;
    vector<Transition> ubCex;
    while(true) {

      assert(boundsEqual.find(child[0]) != boundsEqual.end());
      assert(boundsEqual.find(child[1]) != boundsEqual.end());
      if(first || UBId[child[0]] != oldChild0UBId || UBId[child[1]] != oldChild1UBId) {
        ubCex.clear();
        oldChild0UBId = UBId[child[0]];
        oldChild1UBId = UBId[child[1]];

        vector<SAT::Clauses> proofs;
        //Perform an IC3 query
        //    initial state: state
        //    target: E UB[child[0]] U UB[child[1]]
        //    ouptut: UB[child[1]]
        assert(UBId.find(child[0]) != UBId.end());
        assert(UBId.find(child[1]) != UBId.end());
        assert(UB.find(child[0]) != UB.end());
        assert(UB.find(child[1]) != UB.end());
        //Add UB[id] & UB'[id] & GR & UB[child[0]] as constraints
        vector<SAT::Clauses> constraints(1, GR);
        SAT::Clauses negConstraints; //only UB[child[0]] is necessary
        if(UBId[id] != ev->btrue()) {
          constraints[0].insert(constraints[0].end(), UB[id].begin(), UB[id].end());
          for(vector< vector<ID> >::const_iterator it = UB[id].begin();
              it != UB[id].end(); ++it) {
            vector<ID> cls;
            primeVector(*ev, *it, cls);
            constraints[0].push_back(cls);
          }
        }
        if(UBId[child[0]] != ev->btrue()) {
          constraints[0].insert(constraints[0].end(), UB[child[0]].begin(),
                                UB[child[0]].end());
          Expr::CNFIZE(*ev, ev->apply(Expr::Not, UBId[child[0]]), negConstraints);
        }
        else
          negConstraints.push_back(SAT::Clause());
        IC3::ProofProcType proofProc = (skipGen == SkipForUpper ||
                                       skipGen == SkipForBoth) ?
                                       IC3::NONE : IC3::WEAKEN;
          
        int64_t startTime = Util::get_user_cpu_time(); 
        bool ubReachable = reach(state, UBId[child[1]], UB[child[1]], constraints, negConstraints,
                                 proofProc, proofs, ubCex, id, true);
        if(verbosity > Options::Informative) {
          cout << "EU UB: " << (ubReachable ? "SAT " : "UNSAT ")
               << (Util::get_user_cpu_time() - startTime) / 1000000.0
               << " seconds" << endl;
          if(ubReachable && verbosity > Options::Verbose) {
            //Print the last state in trace
            const vector<ID> & last = ubCex.back().state;
            for(vector<ID>::const_iterator it = last.begin(); it != last.end(); ++it)
              cout << Expr::stringOf(*ev, *it); 
            cout << endl;
            for(vector<ID>::const_iterator it = last.begin(); it != last.end(); ++it)
              cout << (ev->op(*it) == Expr::Not ?  "0" : "1"); 
            cout << endl;
          }
        }
        
        if(!ubReachable) {
          //(P & F) is inductive
          //P = property = !UB[child[1]]
          //F = proof from IC3 (doesn't include the property)
          //Remove state(s) from UB by removing (P & F) (or adding !(P & F))
          const vector< vector<ID> > & proof = proofs[0];
          //Create an expression for !(P & F) = !P | !F
          vector<ID> cubes;
          for(vector< vector<ID> >::const_iterator it = proof.begin();
              it != proof.end(); ++it) {
            vector<ID> cube;
            complement(*ev, *it, cube);
            cubes.push_back(ev->apply(Expr::And, cube));
          }
          cubes.push_back(UBId[child[1]]);
          ID toAdd = ev->apply(Expr::Or, cubes);
          //New UB = oldUB & !(P & F)
          UBId[id] = ev->apply(Expr::And, UBId[id], toAdd);
          //Update UB clauses
          //Create CNF for toAdd
          SAT::Clauses toAddCNF;
          Expr::CNFIZE(*ev, toAdd, toAddCNF);
          UB[id].insert(UB[id].end(), toAddCNF.begin(), toAddCNF.end());
          //Add new clauses of UB to lifting database
          if(UBId[id] != ev->bfalse()) {
            liftSatViews[id]->add(toAddCNF);
          }
          decision = false;
          updateAncestorsBounds(id, Upper);
          break;
        }
        else if(boundsEqual[child[0]] && boundsEqual[child[1]]) {
          if(skipGen != SkipForLower && skipGen != SkipForBoth)
            generalizeEUTrace(ubCex, id, child[0]);
          else {
            //Add all the states on the trace directly
            for(vector<Transition>::const_iterator it = ubCex.begin(); it != ubCex.end();
                ++it) {
              QLBcubes[id].push_back(it->state);
            }
            //Renew QLB
            renewQLB(id);
          }
          decision = true;
          updateAncestorsBounds(id, Lower);
          break;
        }
      }

      if((first || QLBId[child[0]] != oldChild0QLBId || QLBId[child[1]] != oldChild1QLBId)) {
        vector<Transition> lbCex;
        vector<SAT::Clauses> proofs;
        oldChild0QLBId = QLBId[child[0]];
        oldChild1QLBId = QLBId[child[1]];
        //Perform another IC3 query
        //    initial state: state
        //    target: E (QLB[child[0]] & UB[[child[0]]) U (QLB[child[0]] & UB[[child[0]])
        //    ouptut: QLB[child[1]] & UB[child[1]]

        assert(QLBId.find(id) != QLBId.end());
        ID targetID = ev->apply(Expr::And, QLBId[id], UBId[id]);
        assert(QLB.find(id) != QLB.end());
        SAT::Clauses target;
        Expr::CNFIZE(*ev, targetID, target);
        vector<SAT::Clauses> constraints(1, GR);
        SAT::Clauses negConstraints; //only QLB[child[0]] & UB[child[0]] are necessary
        if(UBId[id] != ev->btrue()) {
          constraints[0].insert(constraints[0].end(), UB[id].begin(), UB[id].end());
          for(vector< vector<ID> >::const_iterator it = UB[id].begin();
              it != UB[id].end(); ++it) {
            vector<ID> cls;
            primeVector(*ev, *it, cls);
            constraints[0].push_back(cls);
          }
        }
        constraints[0].insert(constraints[0].end(), QLB[child[0]].begin(), QLB[child[0]].end());
        if(UBId[child[0]] != ev->btrue()) {
          constraints[0].insert(constraints[0].end(), UB[child[0]].begin(), 
                                UB[child[0]].end());
        }
        Expr::CNFIZE(*ev, ev->apply(Expr::Or, ev->apply(Expr::Not, QLBId[child[0]]),
                                              ev->apply(Expr::Not, UBId[child[0]])),
                                              negConstraints);

        int64_t startTime = Util::get_user_cpu_time(); 
        bool lbReachable = reach(state, targetID, target, constraints, negConstraints, IC3::NONE,
                           proofs, lbCex, id, true);
        if(verbosity > Options::Informative)
          cout << "EU LB: " << (lbReachable ? "SAT " : "UNSAT ")
               << (Util::get_user_cpu_time() - startTime) / 1000000.0
               << " seconds" << endl;
        
        if(lbReachable) {
          if(skipGen != SkipForLower && skipGen != SkipForBoth)
            generalizeEUTrace(lbCex, id, child[0]);
          else {
            //Add all the states on the trace directly
            for(vector<Transition>::const_iterator it = lbCex.begin(); it != lbCex.end();
                ++it) {
              QLBcubes[id].push_back(it->state);
            }
            //Renew QLB
            renewQLB(id);
          }
          decision = true;
          updateAncestorsBounds(id, Lower);
          break;
        }
      }
      assert(!boundsEqual[child[0]] || !boundsEqual[child[1]]);

      BoundChange chSkipGen;
      if(skipGen == NoSkip || skipGen == SkipForUpper)
        chSkipGen = NoSkip;
      else
        chSkipGen = SkipForLower;

      bool oneUndecided = false;
      for(vector<Transition>::const_iterator it = ubCex.begin();
          it != ubCex.end() - 1; ++it) {
        if(isUndecided(it->state, child[0])) {
          decide(it->state, child[0], chSkipGen);
          oneUndecided = true;
          break;
        }
      }
      if(!oneUndecided) {
        assert(isUndecided(ubCex.back().state, child[1]));
        decide(ubCex.back().state, child[1], chSkipGen);
      }
      //Check if the state is still undecided before looping again
      if(lbContainsStates(id, state))
        return true;
      if(!ubContainsStates(id, state))
        return false;
      
      first = false;
    }

    return decision;
  }

  default: {
    assert(false);
  }

  } //switch
}

void IICTLAction::translateProperty() {
  StdTranslationFolder transFolder(*ev);
  property = ev->fold(transFolder, property);
  if(verbosity)
    cout << Expr::stringOf(*ev, property) << endl << endl;
  /*
  std::stringstream title;
  title << "\"property\"";
  cout << Expr::dotOf(*ev, property, title.str()) << endl << endl;
  */
}

MC::ReturnValue IICTLAction::check() {

  if(verbosity > Options::Silent)
    cout << "IICTL: starting" << endl;

  MC::ReturnValue rv;

  //Check for a trivial property
  if(property == ev->btrue()) {
    rv.returnType = MC::Proof;
    return rv;
  }
  if(property == ev->bfalse()) {
    rv.returnType = MC::CEX;
    return rv;
  }

  //Initialize upper and lower bounds for each node of the parse graph of the
  //CTL formula
  initializeLabels();

  if (model().options().count("iictl_use_bdd_reach")) {
    if (model().options().count("bdd_save_fw_reach")) {
      RchAttachment const *rat = (RchAttachment const *) model().constAttachment(Key::RCH);
      //this is actually the exact forward reachable states and not a lower
      //bound because with the bdd_save_fw_reach option, the lower bound is
      //only saved if forward reachability has completed
      BDD rch = rat->forwardBddLowerBound(); 
      if(rch) {
        rat->bddToCnf(rch, GR);
        haveExactRch = true;
      }
      model().constRelease(rat);
      //Add reachability info to all lifting SAT databases
      for(IDSatViewMap::iterator it = liftSatViews.begin();
          it != liftSatViews.end(); ++it) {
        it->second->add(GR);
      }
    }
  }


  while(true) {

    vector<ID> state;

    //Check if all initial states are in LB (I => LB)
    if(lbContainsInitStates(state)) {
      if(verbosity > Options::Informative)
        cout << "All initial states are in LB" << endl;
      rv.returnType = MC::Proof;
      return rv;
    }
    if(verbosity > Options::Informative)
      cout << "Some initial states are not in LB" << endl;

    //Check if any of the initial states are not in UB (I =/> UB)
    if(!ubContainsInitStates()) {
      if(verbosity > Options::Informative)
        cout << "Some initial states are not in UB" << endl;
      rv.returnType = MC::CEX;
      return rv;
    }
    if(verbosity > Options::Informative)
      cout << "All initial states are in UB" << endl;

    //Decide state s which is in UB but not in LB, and in the process refine
    //L/U bounds 
    //After return, s will either be added to LB or removed from UB
    try {
      decide(state, property, multiInit ? SkipForUpper : SkipForBoth); 
    }
    catch(Safe) {
      rv.returnType = MC::Proof;
      break;
    }
    catch(CEX) {
      rv.returnType = MC::CEX;
      break;
    }
  }

  return rv;
}

void IICTLAction::init() {
  ev = model().newView();
 
  //Grab the transition relation CNF
  CNFAttachment const * cat = (CNFAttachment const *)
                              model().constAttachment(Key::CNF);
  tr = cat->getPlainCNF();
  model().constRelease(cat);

  SAT::Manager * faeSatMan = model().newSATManager();
  faeSatView = faeSatMan->newView(*ev);
  faeSatView->add(tr);

  ExprAttachment const * eat = (ExprAttachment const *)
                               model().constAttachment(Key::EXPR);
  if(eat->initialConditions().size() != eat->stateVars().size()) {
    multiInit = true;
  }
  initialConditions = eat->initialConditions();
  if(!eat->fairness().empty())
    fairnessConstraints = true;

  const vector<ID> & stateVars = eat->stateVars();
  for(vector<ID>::const_iterator it = stateVars.begin(); it != stateVars.end();
      ++it) {
    stateAsgn.insert(SAT::Assignment::value_type(*it, SAT::Unknown));
    primedStateAsgn.insert(SAT::Assignment::value_type(ev->prime(*it), 
                           SAT::Unknown));
    fullAsgn.insert(SAT::Assignment::value_type(*it, SAT::Unknown));
  }
  const vector<ID> & inputs = eat->inputs();
  for(vector<ID>::const_iterator it = inputs.begin(); it != inputs.end();
      ++it) {
    fullAsgn.insert(SAT::Assignment::value_type(*it, SAT::Unknown));
  }
  model().constRelease(eat); 

  verbosity = model().verbosity();
  //Override the model's verbosity if iictl_verbosity option is specified
  if(model().options().count("iictl_verbosity")) {
    verbosity = (Options::Verbosity) model().options()["iictl_verbosity"].as<int>();
  }
 
  //Grab property from model
  grabProperty();

  if(fairnessConstraints) {
    translateProperty();
  }

  Expr::parents(*ev, property, parents);
  Expr::descendants(*ev, property, descendants);
}


void IICTLAction::exec() {
  IICTLOptions opts(options());
  _opts = &opts;

  init();

  MC::ReturnValue rv = check();
  if (rv.returnType != MC::Unknown) {
    ProofAttachment * pat = (ProofAttachment *) model().attachment(Key::PROOF);
    if (rv.returnType == MC::Proof)
      pat->setConclusion(0);
    else if (rv.returnType == MC::CEX)
      pat->setConclusion(1);
    model().release(pat);
  }
}

} //namespace IICTL
