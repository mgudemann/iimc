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

#include <iostream>
#include "Util.h"
#include "ExprUtil.h"
#include "Sim.h"
#include "Simplifier.h"
#include "AbsInt.h"

using namespace std;

namespace {
  typedef unordered_map<ID,ID> FunctionMap;
  typedef vector< pair< set<ID>, set<ID> > > Partition;

  class SimRefine : public Sim::StateFunctor64 {
  public:
    SimRefine(Model & m, Expr::Manager::View * _ev, Partition & _parts,
              FunctionMap & _fmap) : ev(_ev), parts(_parts), fmap(_fmap) {
      ExprAttachment const * const eat = (ExprAttachment const *) m.constAttachment(Key::EXPR);
      const vector<ID> & latches = eat->stateVars();
      for (unsigned int i = 0; i < latches.size(); ++i)
        latchOrder.insert(OMap::value_type(latches[i], i));
      m.constRelease(eat);
    }

    virtual bool operator()(vector<uint64_t>::const_iterator stateBegin,
                            vector<uint64_t>::const_iterator) {
      Partition newParts;
      for (Partition::iterator it = parts.begin(); it != parts.end(); ++it) {
        set<ID> const & fpart = it->first;
        set<ID> const & tpart = it->second;
        ID rep;
        uint64_t repVal;
        set<ID> eq_f, eq_t;
        if (fpart.find(ev->bfalse()) != fpart.end()) {
          rep = ev->bfalse();
          repVal = 0;
          eq_f.insert(rep);
        } else {
          if (fpart.size() == 0) {
            rep = *(tpart.begin());
            eq_t.insert(rep);
          } else {
            rep = *(fpart.begin());
            eq_f.insert(rep);
          }
          repVal = *(stateBegin + latchOrder[rep]);
        }
        unordered_map< ID, set<ID> > neq;
        // Identify members that are no longer identical to their representative.
        for (set<ID>::const_iterator pit = fpart.begin(); pit != fpart.end(); ++pit) {
          if (*pit == rep) continue;
          uint64_t pitVal = *(stateBegin + latchOrder[*pit]);
          if (repVal == pitVal)
            eq_f.insert(*pit);
          else {
            neq[pitVal].insert(*pit);
          }
        }
        // Identify members that are no longer complementary to their representative.
        for (set<ID>::const_iterator pit = tpart.begin(); pit != tpart.end(); ++pit) {
          if (*pit == rep) continue;
          uint64_t pitVal = *(stateBegin + latchOrder[*pit]);
          if (repVal == ~pitVal)
            eq_t.insert(*pit);
          else
            neq[~pitVal].insert(ev->apply(Expr::Not, *pit));
        }
        // If this class is still non-trivial, keep it.
        if (eq_f.size() + eq_t.size() > 1) {
          newParts.push_back(Partition::value_type(eq_f, eq_t));
        } else {
          if (eq_f.size() > 0)
            fmap.erase(*(eq_f.begin()));
          else
            fmap.erase(*(eq_t.begin()));
        }

        // Create new classes from the members who broke away.
        for (unordered_map< ID, set<ID> >::const_iterator classIt = neq.begin();
             classIt != neq.end(); ++classIt) {
          set<ID> const & members = classIt->second;
          if (members.size() > 1) {
            set<ID> new_fpart, new_tpart;
            for (set<ID>::const_iterator mit = members.begin(); mit != members.end(); ++mit) {
              if (ev->op(*mit) == Expr::Not) {
                new_tpart.insert(ev->apply(Expr::Not, *mit));
              } else {
                new_fpart.insert(*mit);
              }
            }
            newParts.push_back(Partition::value_type(new_fpart, new_tpart));
          } else {
            ID er = *(classIt->second.begin()); // the only one
            if (ev->op(er) == Expr::Not)
              er = ev->apply(Expr::Not, er);
            fmap.erase(er);
          }
        }
      }
      parts = newParts;
      return (parts.size() > 0);
    }

  private:
    Expr::Manager::View * ev;
    Partition & parts;
    FunctionMap & fmap;
    typedef unordered_map<ID, unsigned> OMap;
    OMap latchOrder;
  };

  void iterate(
    Expr::Manager::View * ev,
    ExprAttachment const *,
    Partition & parts,
    FunctionMap & fmap,
    Options::Verbosity verbosity)
  {
    // 1. map each latch to its EC's representative
    FunctionMap lmap;
    for (Partition::const_iterator it = parts.begin(); it != parts.end(); ++it) {
      set<ID> const & fpart = it->first;
      set<ID> const & tpart = it->second;
      assert(fpart.size() + tpart.size() > 1);
      set<ID>::const_iterator rep = fpart.begin();
      if (rep != fpart.end()) {
        ID repVal = *rep;
        set<ID>::const_iterator pit = rep;
        for (++pit; pit != fpart.end(); ++pit) {
          lmap.insert(FunctionMap::value_type(*pit, repVal));
          if (verbosity > Options::Verbose) {
            ostringstream oss;
            shortStringOfID(*ev, *pit, oss);
            oss << " -> ";
            shortStringOfID(*ev, repVal, oss);
            cout << oss.str() << endl;
          }
        }
        ID notRepVal = ev->apply(Expr::Not, repVal);
        for (pit = tpart.begin(); pit != tpart.end(); ++pit) {
          lmap.insert(FunctionMap::value_type(*pit, notRepVal));
          if (verbosity > Options::Verbose) {
            ostringstream oss;
            shortStringOfID(*ev, *pit, oss);
            oss << " -> ";
            shortStringOfID(*ev, notRepVal, oss);
            cout << oss.str() << endl;
          }
        }
      } else {
        // The true half of the EC must be non-empty.
        rep = tpart.begin();
        ID repVal = *rep;
        set<ID>::const_iterator pit = rep;
        for (++pit = tpart.begin(); pit != tpart.end(); ++pit) {
          lmap.insert(FunctionMap::value_type(*pit, repVal));
          if (verbosity > Options::Verbose) {
            ostringstream oss;
            shortStringOfID(*ev, *pit, oss);
            oss << " -> ";
            shortStringOfID(*ev, repVal, oss);
            cout << oss.str() << endl;
          }
        }
      }
    }
    if (verbosity > Options::Verbose) {
      cout << "Substitution map:\n";
      for (FunctionMap::const_iterator cit = lmap.begin();
           cit != lmap.end(); ++cit) {
        cout << ev->op(cit->second);
          cout << "CUBE@2: " << "~" << stringOf(*ev, cit->first)
               << " " << stringOf(*ev, cit->second) << endl;
          cout << "CUBE@2: " << stringOf(*ev, cit->first) << " "
               << "~" << stringOf(*ev, cit->second) << endl;
      }
    }

    // 2. varSub the latch map to form new roots
    if (lmap.size() > 0) {
      vector<ID> roots;
      for (FunctionMap::const_iterator it = fmap.begin(); it != fmap.end(); ++it) {
        roots.push_back(it->second);
      }
      implSet implications;
      Expr::Simplifier simp(*ev, implications, lmap, verbosity);
      //Expr::varSub(*ev, lmap, roots);
      simp.simplify(roots);
      vector<ID>::size_type i = 0;
      for (FunctionMap::iterator it = fmap.begin(); it != fmap.end(); ++it, ++i) {
        it->second = roots[i];
        if (verbosity > Options::Verbose) {
          ostringstream oss;
          shortStringOfID(*ev, it->first, oss);
          oss << "(1) = ";
          oss << stringOf(*ev, it->second);
          cout << oss.str() << endl;
        }
      }
    }
  }

  bool refine(
    Expr::Manager::View * ev,
    Partition & parts,
    FunctionMap const & roots,
    FunctionMap & fmap,
    Options::Verbosity verbosity)
  {
    bool changed = false;
    Partition newParts;
    for (Partition::iterator it = parts.begin(); it != parts.end(); ++it) {
      ID rep, rootRep;
      set<ID> const & fpart = it->first;
      set<ID> const & tpart = it->second;
      set<ID> eq_f, eq_t;
      // Get representative and its function.
      if (fpart.size() == 0) {
        rep = *(tpart.begin());
        rootRep = ev->apply(Expr::Not, roots.find(rep)->second);
        eq_t.insert(rep);
      } else {
        if (fpart.find(ev->bfalse()) != fpart.end()) {
          rep = ev->bfalse();
          rootRep = rep;
        } else {
          rep = *(fpart.begin());
          rootRep = roots.find(rep)->second;
        }
        eq_f.insert(rep);
      }
      if (verbosity > Options::Verbose) {
        ostringstream oss;
        oss << "Representative: ";
        shortStringOfID(*ev, rep, oss);
        oss << ". Root: ";
        shortStringOfID(*ev, rootRep, oss);
        cout << oss.str() << endl;
      }
      unordered_map< ID, set<ID> > neq;
      // Identify members that are no longer identical to their representative.
      for (set<ID>::const_iterator pit = fpart.begin(); pit != fpart.end(); ++pit) {
        if (*pit == rep) continue;
        FunctionMap::const_iterator rpit = roots.find(*pit);
        if (rootRep == rpit->second) {
          eq_f.insert(*pit);
        } else {
          neq[rpit->second].insert(*pit);
          changed = true;
        }
      }
      // Identify members that are no longer complementary to their representative.
      for (set<ID>::const_iterator pit = tpart.begin(); pit != tpart.end(); ++pit) {
        if (*pit == rep) continue;
        FunctionMap::const_iterator rpit = roots.find(*pit);
        if (rootRep == ev->apply(Expr::Not, rpit->second)) {
          eq_t.insert(*pit);
        } else {
          if (verbosity > Options::Verbose)
            cout << "Detaching " << stringOf(*ev, *pit) << endl;
          neq[ev->apply(Expr::Not, rpit->second)].insert(ev->apply(Expr::Not, *pit));
          changed = true;
        }
      }
      // If this class is still non-trivial, keep it.
      if (eq_f.size() + eq_t.size() > 1) {
        newParts.push_back(Partition::value_type(eq_f, eq_t));
      } else {
        if (eq_f.size() > 0)
          fmap.erase(*(eq_f.begin()));
        else
          fmap.erase(*(eq_t.begin()));
      }

      // Create new classes from the members that broke away.
      for (unordered_map< ID, set<ID> >::const_iterator classIt = neq.begin();
           classIt != neq.end(); ++classIt) {
        set<ID> const & members = classIt->second;
        if (members.size() > 1) {
          set<ID> new_fpart, new_tpart;
          for (set<ID>::const_iterator mit = members.begin(); mit != members.end(); ++mit) {
            if (verbosity > Options::Verbose)
              cout << "Reattaching " << stringOf(*ev, *mit) << endl;
            if (ev->op(*mit) == Expr::Not) {
              new_tpart.insert(ev->apply(Expr::Not, *mit));
            } else {
              new_fpart.insert(*mit);
            }
          }
          newParts.push_back(Partition::value_type(new_fpart, new_tpart));
        } else {
          ID er = *(classIt->second.begin()); // the only one
          if (ev->op(er) == Expr::Not)
            er = ev->apply(Expr::Not, er);
          if (verbosity > Options::Verbose)
            cout << "Erasing " << stringOf(*ev, er) << endl;
          fmap.erase(er);
        }
      }
    }
    parts = newParts;
    return changed;
  }
}


void AbsIntAction::exec()
{
  // Setup.  Get attachments and such stuff.
  int64_t startTime = Util::get_user_cpu_time();
  Options::Verbosity verbosity = _model.verbosity();
  if (verbosity > Options::Silent)
    cout << "Abstract interpretation of model " << _model.name() << endl;
  int timeout = _model.options()["absint_timeout"].as<int>();

  ExprAttachment const * const eat = (ExprAttachment const *) _model.constAttachment(Key::EXPR);

  Expr::Manager::View * ev = _model.newView();

  // Find initial partition.
  vector<ID> vars = eat->stateVars();
  FunctionMap fmap;
  for (vector<ID>::const_iterator it = vars.begin(); it != vars.end(); ++it)
    fmap.insert(FunctionMap::value_type(*it, eat->nextStateFnOf(*it)));

  // Uninitialized latches or those that get dropped out of ECs.
  FunctionMap singletonLatches = fmap;

  Partition parts;
  set<ID> fpart, tpart;
  fpart.insert(ev->bfalse());
  vector<ID> init = eat->initialConditions();
  for (vector<ID>::const_iterator it = init.begin(); it != init.end(); ++it) {
    if (ev->op(*it) == Expr::Var) {
      tpart.insert(*it);
      singletonLatches.erase(*it);
    } else {
      assert(ev->op(*it) == Expr::Not);
      ID var = ev->apply(Expr::Not, *it);
      assert(ev->op(var) == Expr::Var);
      fpart.insert(var);
      singletonLatches.erase(var);
    }
  }
  if (fpart.size() == 1 && tpart.size() == 0) {
    delete ev;
    return;
  }
  parts.push_back(Partition::value_type(fpart, tpart));

  // Refine classes by random simulation.
  if (model().verbosity() > Options::Informative)
    cout << "Abstract interpreter: Simulation refinement" << endl;
  SimRefine simRefine(model(), ev, parts, fmap);
  sequentialSimulateRandom64(model(), 100, simRefine);

  // Refinement cycle.
  unsigned iterations = 0;
  bool timedOut = false;
  ev->begin_local();
  while (true) {
    if (verbosity > Options::Informative) {
      cout << " " << parts.size();
      if (verbosity > Options::Verbose) {
        for (Partition::iterator it = parts.begin(); it != parts.end(); ++it)
          cout << " " << it->first.size() << "/" << it->second.size();
      }
      cout << endl;
    }
    FunctionMap curr(fmap);
    iterate(ev, eat, parts, curr, verbosity);
    ++iterations;
    if (!refine(ev, parts, curr, fmap, verbosity)) {
      // globalize roots
      vector<ID> roots;
      for (FunctionMap::const_iterator it = curr.begin(); it != curr.end(); ++it)
        roots.push_back(it->second);
      ev->global(roots);
      // make curr point to global roots
      unsigned int i = 0;
      for (FunctionMap::iterator it = curr.begin(); it != curr.end(); ++it, ++i)
        it->second = roots[i];
      // save as fmap
      fmap = curr;
      break;
    }
    if (timeout != -1) {
      int64_t currTime = Util::get_user_cpu_time();
      if (currTime - startTime > timeout * 1000000) {
        timedOut = true;
        if (verbosity > Options::Silent) {
          cout << "Abstract interpreter: timed out" << endl;
        }
        break;
      }
    }
  }
  ev->end_local();
  _model.constRelease(eat);

  bool changed = false;
  if (!timedOut) {
    if (verbosity > Options::Terse) {
      cout << "Abstract interpreter: " << parts.size() << " parts in "
           << iterations << " iterations" << endl;
    }

    // Add latches that were dropped from equivalence classes.
    for (vector<ID>::const_iterator it = vars.begin(); it != vars.end(); ++it) {
      if (fmap.find(*it) == fmap.end())
        singletonLatches.insert(FunctionMap::value_type(*it, eat->nextStateFnOf(*it)));
    }

    // Store simplified model in ExprAttachment.
    for (Partition::const_iterator it = parts.begin(); it != parts.end(); ++it) {
      set<ID> const & fpart = it->first;
      set<ID> const & tpart = it->second;
      if (fpart.size() + tpart.size() > 1) {
        changed = true;
        break;
      }
    }

    if (changed) {
      auto seat = model().attachment<SeqAttachment>(Key::SEQ);
      auto eat = model().attachment<ExprAttachment>(Key::EXPR);

      FunctionMap lmap;
      eat->clearNextStateFns();
      map<ID, ID> latchToNsf;
      for (Partition::const_iterator it = parts.begin(); it != parts.end(); ++it) {
        set<ID> const & fpart = it->first;
        set<ID> const & tpart = it->second;
        // Set next state function.
        set<ID>::const_iterator rep = fpart.begin();
        if (rep != fpart.end()) {
          if (*rep != ev->bfalse()) {
            FunctionMap::const_iterator rit = fmap.find(*rep);
            latchToNsf.insert(map<ID, ID>::value_type(*rep, rit->second));
          }
          // Build map of latch to representative latch.
          set<ID>::const_iterator pit = rep;
          for (++pit; pit != fpart.end(); ++pit) {
            lmap.insert(FunctionMap::value_type(*pit, *rep));
            seat->optimized.insert(unordered_map<ID, ID>::value_type(*pit, *rep));
          }
          for (pit = tpart.begin(); pit != tpart.end(); ++pit) {
            ID nrep = ev->apply(Expr::Not, *rep);
            lmap.insert(FunctionMap::value_type(*pit, nrep));
            seat->optimized.insert(unordered_map<ID, ID>::value_type(*pit, nrep));
          }
        } else {
          rep = tpart.begin();
          FunctionMap::const_iterator rit = fmap.find(*rep);
          latchToNsf.insert(map<ID, ID>::value_type(*rep, rit->second));
          for (set<ID>::const_iterator pit = tpart.begin(); pit != tpart.end(); ++pit) {
            lmap.insert(FunctionMap::value_type(*pit, *rep));
            seat->optimized.insert(unordered_map<ID, ID>::value_type(*pit, *rep));
          }
        }
      }
      if (verbosity > Options::Informative) {
        cout << "Substitution map:\n";
        for (FunctionMap::const_iterator cit = lmap.begin();
             cit != lmap.end(); ++cit) {
          cout << "// "
               << stringOf(*ev, cit->first) << " -> " << stringOf(*ev, cit->second) << endl;
          // output constant fixed latches
          if ("!true" == stringOf(*ev, cit->second))
            cout << "CUBE@2: " << stringOf(*ev, cit->first) << endl;
          else if ("true" == stringOf(*ev, cit->second))
            cout << "CUBE@2: ~" << stringOf(*ev, cit->first) << endl;
          // output latch equivalence
          else
            {
              cout << "CUBE@2: "
                << "~"
                << stringOf(*ev, cit->first)
                << " "
                << stringOf(*ev, cit->second) << endl;
              cout << "CUBE@2: "
                   << stringOf(*ev, cit->first)
                   << " ~"
                   << stringOf(*ev, cit->second) << endl;
            }
        }
      }
      for(FunctionMap::const_iterator it = singletonLatches.begin();
          it != singletonLatches.end(); ++it) {
        ID nsf = Expr::varSub(*ev, lmap, it->second);
        latchToNsf.insert(map<ID, ID>::value_type(it->first, nsf));
      }
      for (map<ID, ID>::const_iterator it = latchToNsf.begin();
           it != latchToNsf.end(); ++it) {
        eat->setNextStateFn(it->first, it->second);
      }
      ev->keep(eat->nextStateFnOf(eat->stateVars()));

      if (verbosity > Options::Silent)
        cout << "Abstract Interpreter: Final # latches = " << eat->stateVars().size() << endl;

      vector<ID> init(eat->initialConditions());
      eat->clearInitialConditions();
      for (vector<ID>::iterator it = init.begin(); it != init.end(); ++it)
        if (Expr::varSub(*ev, lmap, *it) == *it)
          eat->addInitialCondition(*it);

      vector<ID> constraints(eat->constraints());
      vector<ID> constraintFns(eat->constraintFns());
      eat->clearConstraints();
      Expr::varSub(*ev, lmap, constraintFns);
      eat->addConstraints(constraints, constraintFns);
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
      model().release(seat);
    }
  }
  if (timedOut || !changed) {
    if (verbosity > Options::Silent)
      cout << "Abstract Interpreter: Final # latches = " << vars.size() << endl;
  }

  // Endgame.

  delete ev;

  int64_t endTime = Util::get_user_cpu_time();
  if (verbosity > Options::Silent)
    cout << "Abstract interpreter completed in "
         << ((endTime - startTime) / 1000000.0) << " s" << endl;
}
