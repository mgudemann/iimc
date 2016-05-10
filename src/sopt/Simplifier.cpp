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
#include "PhaseAbstraction.h"
#include "Simplifier.h"

using namespace std;

namespace Expr {

void Simplifier::simplify(vector<ID> & roots)
{
  if (verbosity_ > Options::Informative)
    cout << "Starting simplifier" << endl;
  reduced_ = 0;
  rewritten_ = 0;
  view().fold(*this, roots);
  if (verbosity_ > Options::Informative)
    cout << "Simplification: " << reduced_ << " reduced " << rewritten_ << " rewritten" << endl;
}


ID Simplifier::fold(ID id, int n, const ID * const args)
{
  ID newId = id;
  Op op = view().op(id);
  if (op == Var)
    newId = simplifiedVar(id);
  else if (op == And && n == 2) {
    newId = simpleRewrite(id, args);
    if (newId != id) {
      ++rewritten_;
      if (verbosity_ > Options::Verbose)
        cout << "Rewritten " << stringOf(view(), id) << endl;
      int numArgs;
      ID const * newArgs = view().arguments(newId, &numArgs);
      if (numArgs == 2) {
        assert(view().op(newId) == And);
        newId = simplifiedAnd(newId, newArgs);
      }
    } else {
      newId = simplifiedAnd(id, args);
    }
  }
  if (newId != id) return newId;
  return Manager::View::Folder::fold(newId, n, args);
}


ID Simplifier::simplifiedVar(ID id)
{
  unordered_map<ID,ID>::const_iterator fit = equivalences_.find(id);
  if (fit != equivalences_.end()) {
    ID rep = fit->second;
    if (verbosity_ > Options::Verbose)
      cout << "Replacing " << stringOf(view(), id) << " with " << stringOf(view(), rep) << endl;
    return rep;
  }
  return id;
}

ID Simplifier::simpleRewrite(ID id, ID const * const args)
{
  ID id0 = args[0];
  ID id1 = args[1];
  ID n0 = view().apply(Not, id0);
  ID n1 = view().apply(Not, id1);
  if (view().op(id0) == And) {
    int numArgs;
    ID const * andArgs = view().arguments(id0, &numArgs);
    if (numArgs == 2) {
      if (id1 == andArgs[0] || id1 == andArgs[1])
        return id0;
      if (n1 == andArgs[0] || n1 == andArgs[1])
        return view().bfalse();
    }
  }
  if (view().op(n0) == And) {
    int numArgs;
    ID const * andArgs = view().arguments(n0, &numArgs);
    if (numArgs == 2) {
      if (n1 == andArgs[0] || n1 == andArgs[1])
        return id1;
      if (id1 == andArgs[0])
        return view().apply(And, id1, view().apply(Not, andArgs[1]));
      if (id1 == andArgs[1])
        return view().apply(And, id1, view().apply(Not, andArgs[0]));
    }
  }
  if (view().op(id1) == And) {
    int numArgs;
    ID const * andArgs = view().arguments(id1, &numArgs);
    if (numArgs == 2) {
      if (id0 == andArgs[0] || id0 == andArgs[1])
        return id1;
      if (n0 == andArgs[0] || n0 == andArgs[1])
        return view().bfalse();
    }
  }
  if (view().op(n1) == And) {
    int numArgs;
    ID const * andArgs = view().arguments(n1, &numArgs);
    if (numArgs == 2) {
      if (n0 == andArgs[0] || n0 == andArgs[1])
        return id0;
      if (id0 == andArgs[0])
        return view().apply(And, id0, view().apply(Not, andArgs[1]));
      if (id0 == andArgs[1])
        return view().apply(And, id0, view().apply(Not, andArgs[0]));
    }
  }
  return id;
}


ID Simplifier::simplifiedAnd(ID id, const ID * const args)
{
  ID id0 = args[0];
  ID id1 = args[1];
  ID n0 = view().apply(Not, id0);
  ID n1 = view().apply(Not, id1);
  if (implications_.find(implSet::value_type(n0,n1)) != implications_.end()) {
    if (verbosity_ > Options::Verbose)
      cout << "Simplifying " << stringOf(view(), id0) << " & "
           << stringOf(view(), id1) << " with " << stringOf(view(), n0)
           << " | " << stringOf(view(), n1) << " to "
           << stringOf(view(), view().bfalse()) << endl;
    ++reduced_;
    return view().bfalse();
  }
  if (implications_.find(implSet::value_type(id0,n1)) != implications_.end()) {
    if (verbosity_ > Options::Verbose)
      cout << "Simplifying " << stringOf(view(), id0) << " & "
           << stringOf(view(), id1) << " with " << stringOf(view(), id0)
           << " | " << stringOf(view(), n1) << " to "
           << stringOf(view(), id1) << endl;
    ++reduced_;
    return id1;
  }
  if (implications_.find(implSet::value_type(n0,id1)) != implications_.end()) {
    if (verbosity_ > Options::Verbose)
      cout << "Simplifying " << stringOf(view(), id0) << " & "
           << stringOf(view(), id1) << " with " << stringOf(view(), n0)
           << " | " << stringOf(view(), id1) << " to "
           << stringOf(view(), id0) << endl;
    ++reduced_;
    return id0;
  }
  return id;
}

} // namespace Expr

using namespace ThreeValued;

/** Collect information about a persistent signal. */
PersistentSignalCard::PersistentSignalCard(
  vecSeq const & lasso,
  ID var,
  vector<ID>::size_type li) : position(li)
{
  lastTransition = 0;
  firstTransition = 0;
  numberTransitions = 0;
  initialValue = lasso[0][li];
  finalValue = initialValue;
  wasX = initialValue == TVX;
  for (vecSeq::size_type it = 1; it < lasso.size(); ++it) {
    TV newval = lasso[it][li];
    if (newval != finalValue) {
      finalValue = newval;
      if (newval == TVX) wasX = true;
      lastTransition = it;
      if (numberTransitions == 0) {
        firstTransition = it;
      }
      numberTransitions++;
    }
  }
}


/** Collect information about a periodic signal. */
PeriodicSignalCard::PeriodicSignalCard(
  vecSeq const & lasso,
  ID var,
  vecSeq::size_type stem,
  vector<ID>::size_type li) :
  position(li)
{
  // Find minimum period.
  vecSeq::size_type maxperiod = lasso.size() - stem;
  period = 1;
  while (period < maxperiod) {
    ++period;
    if (maxperiod % period != 0) continue;
    bool success = true;
    vecSeq::size_type mit = stem;
    for (vecSeq::size_type cit = stem + period; cit < lasso.size(); ++ cit) {
      if (lasso[cit][li] != lasso[mit][li]) {
        success = false;
        break;
      }
      if (mit == stem + period - 1) mit = stem; else ++mit;
    }
    if (success) break;
  }
  // Find where periodic behavior starts by walking back the stem.
  start = stem;
  vecSeq::size_type cit = lasso.size();
  while (start != 0) {
    if (cit == stem) cit = lasso.size() - 1; else --cit;
    if (lasso[cit][li] == lasso[start-1][li])
      --start;
    else
      break;
  }
  // Check whether signal is ever X.
  wasX = false;
  vecSeq::size_type sit = start;
  while (sit > 0) {
    --sit;
    if (lasso[sit][li] == TVX) {
      wasX = true;
      break;
    }
  }
  wave.reserve(period);
  for (vecSeq::size_type it = start; it < start + period; ++it)
    wave.push_back(lasso[it][li]);
}


/** Comparison function to sort persistent signals. */
bool comparePersistent(pair<ID, PersistentSignalCard> const & a,
                       pair<ID, PersistentSignalCard> const & b)
{
  return (a.second.firstTransition <  b.second.firstTransition) ||
    ((a.second.firstTransition ==  b.second.firstTransition) &&
     ((a.second.lastTransition <  b.second.lastTransition) ||
      ((a.second.lastTransition ==  b.second.lastTransition) &&
       (a.second.numberTransitions <  b.second.numberTransitions))));
}


/** Comparison function to sort periodic signals. */
bool comparePeriodic(pair<ID, PeriodicSignalCard> const & a,
                     pair<ID, PeriodicSignalCard> const & b)
{
  return (a.second.period < b.second.period) ||
    ((a.second.period == b.second.period) &&
     (a.second.start < b.second.start));
}


/** Extract periodic and persistent signals from the results
 *  of ternary simulation. */
void findInterestingSignals(
  vecSeq const & lasso,
  vector<ID> const & sv,
  vecSeq::size_type stem,
  PersistentCardMap & persistentMap,
  PeriodicCardMap & periodicMap)
{
  for (vector<ID>::size_type li = 0; li < sv.size(); ++li) {
    // A persistent signal has the same known value throughout the cycle.
    // A periodic signal is never unknown throughout the cycle.  According
    // to these definitions, persistence is a special case of periodicity.
    TV val = lasso[stem][li];
    if (val == TVX) continue;
    bool persists = true;
    for (vecSeq::size_type it = stem + 1; it < lasso.size(); ++it) {
      TV newval = lasso[it][li];
      if (newval == TVX) {
        val = TVX;
        break;
      } else if (newval != val) {
        persists = false;
      }
    }
    // The following check (val != TVX) misses periodic signals whose
    // periods contain an X, but contain other values as well.  This is
    // acceptable, because we wouldn't do much with such signals anyway.
    if (val != TVX) {
      // Write signal "card," gathering its useful traits.
      if (persists) {
        persistentMap.insert(
          PersistentCardMap::value_type(
            sv[li], PersistentSignalCard(lasso, sv[li], li)));
      } else { // signal is (eventually) periodic
        periodicMap.insert(
          PeriodicCardMap::value_type(
            sv[li], PeriodicSignalCard(lasso, sv[li], stem, li)));
      }
    }
  }
}


/** Print the results of ternary simulation in tabular form.
 *  With "full" set to false (default) only print periodic
 *  and persistent signals.  Otherwise, print all latches.
 *  Note that the full version of the table may be both wider
 *  and longer than the abridged one, because signals that
 *  eventually go to X may take a long time to do so. */
void printSimulationWaves(
  Expr::Manager::View & v,
  vecSeq const & lasso,
  vector<ID> const & sv,
  PersistentCardMap const & pmap,
  PeriodicCardMap const & cmap,
  bool full)
{
  // Study the cards to find number of rows and columns.
  unordered_map<ID, string> names;
  string::size_type maxlen = 0;
  vecSeq::size_type stable = 0;
  vecSeq::size_type period = 1;
  for (vector<ID>::size_type i = 0; i < sv.size(); ++i) {
    ID var = sv[i];
    PersistentCardMap::const_iterator pit = pmap.find(var);
    if (pit != pmap.end()) {
      if (pit->second.lastTransition > stable)
        stable = pit->second.lastTransition;
    }
    PeriodicCardMap::const_iterator cit = cmap.find(var);
    if (cit != cmap.end()) {
      if (cit->second.period > period)
        period = cit->second.period;
      if (cit->second.start > stable)
        stable = cit->second.start;
    }
    if (full || pit != pmap.end() || cit != cmap.end()) {
      ostringstream oss;
      shortStringOfID(v, var, oss);
      names[var] = oss.str();
      if (oss.str().length() > maxlen)
        maxlen = oss.str().length();
    }
  }
  if (!full && names.size() * (stable + period) > 100000) return;
  // Print the header.
  for (string::size_type j = 0; j < maxlen; ++j) {
    cout << " ";
    for (vector<ID>::size_type i = 0; i < sv.size(); ++i) {
      ID var = sv[i];
      unordered_map<ID, string>::const_iterator it = names.find(var);
      if (it != names.end()) {
        if (j < it->second.length())
          cout << it->second[j];
        else
          cout << " ";
      }
    }
    cout << endl;
  }
  cout << endl;
  // Print the body.
  vecSeq::size_type num = full ? lasso.size() : (stable + period);
  for (vecSeq::size_type j = 0; j < num; ++j) {
    cout << " ";
    for (vector<ID>::size_type i = 0; i < sv.size(); ++i) {
      if (names.find(sv[i]) != names.end()) {
        cout << lasso[j][i];
      }
    }
    cout << endl;
  }
}


/** Print finding from ternary simulation. */
void printReport(
  Options::Verbosity verbosity,
  vecSeq const & lasso,
  Expr::Manager::View & ev,
  vector<ID> const & sv,
  PersistentCardMap const & persistentMap,
  PeriodicCardMap const & periodicMap)
{
  if (verbosity > Options::Informative) {
    printSimulationWaves(ev, lasso, sv, persistentMap, periodicMap, verbosity > Options::Verbose);
    PersistentCardMap::size_type nStuck=0;
    for (PersistentCardMap::const_iterator card = persistentMap.begin();
         card != persistentMap.end(); ++card) {
      ostringstream oss;
      shortStringOfID(ev, card->first, oss);
      if (card->second.numberTransitions == 0) {
        oss << " stuck at " << card->second.finalValue;
        nStuck++;
      } else {
        oss << " " << card->second.numberTransitions;
        if (card->second.numberTransitions == 1) {
          oss << " transition at " << card->second.firstTransition;
        } else {
          oss << " transitions between " << card->second.firstTransition
              << " and " << card->second.lastTransition;
        }
        oss << ", initially " << card->second.initialValue
            << ", eventually " << card->second.finalValue
            << (card->second.wasX ? ", was X" : ", never X");
      }
      if (verbosity > Options::Informative)
        cout << oss.str() << endl;
    }
    if (verbosity > Options::Informative) {
      for (PeriodicCardMap::const_iterator card = periodicMap.begin();
           card != periodicMap.end(); ++card) {
        ostringstream oss;
        shortStringOfID(ev, card->first, oss);
        oss << " (starts at time " << card->second.start << ") wave: ";
        for (TVvec::const_iterator val = card->second.wave.begin();
             val != card->second.wave.end(); ++val)
          oss << *val;
        cout << oss.str() << endl;
      }
    }
    cout << "Found " << persistentMap.size() << " persistent latches ("
         << nStuck << " stuck) and "
         << periodicMap.size() << " periodic latches" << endl;
  }
}


/** Build a set of constraint clauses from the lasso. */
void findImplications(
  Expr::Manager::View & ev,
  vector<ID> const & sv,
  unordered_set<ID> const & ignore,
  vecSeq const & lasso,
  implSet & implications,
  unordered_map<ID,ID> & equivalences,
  Options::Verbosity verbosity)
{
  TVvec::size_type classes = 0;

  for (vector<ID>::size_type i = 0; i < sv.size(); ++i) {
    ID var = sv[i];
    if (ignore.find(var) != ignore.end()) continue;
    for (vector<ID>::size_type j = i+1; j < sv.size(); ++j) {
      ID scndVar = sv[j];
      if (ignore.find(scndVar) != ignore.end()) continue;
      // mask is encoded thus: 8 -> 11, 4 -> 10, 2 -> 01, 1 -> 00
      unsigned mask = 0;
      for (vecSeq::const_iterator it = lasso.begin();
           it != lasso.end(); ++it) {
        if ((*it)[i] == TVTrue) {
          if ((*it)[j] == TVTrue) mask |= 8;
          else if ((*it)[j] == TVFalse) mask |= 4;
          else mask |= 12;
        } else if ((*it)[i] == TVFalse) {
          if ((*it)[j] == TVTrue) mask |= 2;
          else if ((*it)[j] == TVFalse) mask |= 1;
          else mask |= 3;
        } else { // TVX
          if ((*it)[j] == TVTrue) mask |= 10;
          else if ((*it)[j] == TVFalse) mask |= 5;
          else mask |= 15;
        }
        if (mask == 15) break;
      }
      if (mask != 15) {
        // Implications found.
        if ((mask & 12) == 0) {
          // First latch stuck at 0.
          equivalences[var] = ev.bfalse();
          classes = 1;
          break;
        }
        if ((mask & 3) == 0) {
          // First latch stuck at 1.
          equivalences[var] = ev.btrue();
          classes = 1;
          break;
        }
        if ((mask & 10) == 0 || (mask & 5) == 0) {
          // Second latch is stuck.  We'll deal with it later.
          continue;
        }
        bool reverse = var > scndVar;
        if ((mask & 6) == 0) {
          // The two latches are equivalent.
          if (verbosity > Options::Verbose)
            cout << stringOf(ev, scndVar) << " equivalent to " << stringOf(ev, var);
          unordered_map<ID,ID>::const_iterator it1 = equivalences.find(var);
          if (it1 == equivalences.end()) {
            assert(equivalences.find(scndVar) == equivalences.end());
            equivalences[var] = var;
            equivalences[scndVar] = var;
            if (verbosity > Options::Verbose)
              cout << ": representative is " << stringOf(ev, var) << endl;
          } else {
            equivalences[scndVar] = it1->second;
            if (verbosity > Options::Verbose)
              cout << ": representative is " << stringOf(ev, it1->second) << endl;
          }
        }
        if ((mask & 9) == 0) {
          // The two latches are complementary.
          if (verbosity > Options::Verbose)
            cout << stringOf(ev, scndVar) << " complementary to " << stringOf(ev, var);
          unordered_map<ID,ID>::const_iterator it1 = equivalences.find(var);
          if (it1 == equivalences.end()) {
            assert(equivalences.find(scndVar) == equivalences.end());
            equivalences[var] = var;
            equivalences[scndVar] = ev.apply(Expr::Not, var);
            if (verbosity > Options::Verbose)
              cout << ": representative is " << stringOf(ev, var) << endl;
          } else {
            equivalences[scndVar] = ev.apply(Expr::Not, it1->second);
            if (verbosity > Options::Verbose)
              cout << ": representative is " << stringOf(ev, it1->second) << endl;
          }
        }
        // At this point, exactly one bit of the mask is 0.
        ID l1, l2;
        if (~mask & 1) { // (false, false) never occurs
          l1 = reverse ? scndVar : var;
          l2 = reverse ? var : scndVar;
        } else if (~mask & 2) { // (false, true) never occurs 
          l1 = reverse ? ev.apply(Expr::Not, scndVar) : var;
          l2 = reverse ? var : ev.apply(Expr::Not, scndVar);
        } else if (~mask & 4) { // (true, false) never occurs 
          l1 = reverse ? scndVar : ev.apply(Expr::Not, var);
          l2 = reverse ? ev.apply(Expr::Not, var) : scndVar;
        } else { // (true, true) never occurs 
          l1 = ev.apply(Expr::Not, (reverse ? scndVar : var));
          l2 = ev.apply(Expr::Not, (reverse ? var : scndVar));
        }
        implications.insert(implSet::value_type(l1, l2));
      }
    }
  }

  // Report.
  if (verbosity > Options::Silent) {
    for (unordered_map<ID,ID>::const_iterator it = equivalences.begin();
         it != equivalences.end(); ++it) {
      if (it->first == it->second)
        ++classes;
    }
    cout << "Found " << equivalences.size() << " equivalent signals in " << classes
         << " classes and " << implications.size() << " implications among latches"
         << endl;
    if (verbosity > Options::Verbose) {
      for (unordered_map<ID,ID>::const_iterator it = equivalences.begin();
           it != equivalences.end(); ++it) {
        cout << stringOf(ev, it->first) << " -> " << stringOf(ev, it->second) << endl;
      }
      for (implSet::const_iterator it = implications.begin();
           it != implications.end(); ++it) {
        cout << stringOf(ev, it->first) << " | " << stringOf(ev, it->second) << endl;
      }
    }
  }
}


/** A lighter-weight implication finder. */
void findImplicationsLight(
  Expr::Manager::View & ev,
  unordered_set<ID> const & ignore,
  PersistentCardMap const & persistentMap,
  PeriodicCardMap const & periodicMap,
  vecSeq const & lasso,
  implSet & implications,
  unordered_map<ID,ID> & equivalences,
  Options::Verbosity verbosity)
{
  TVvec::size_type classes = 0;

  typedef vector<pair<ID, PersistentSignalCard>> cardVec;
  cardVec nonStuck;

  // Check equivalence to true and false.  Accumulate non-stuck,
  // not-to-be-ignored persistent signals in a vector for more
  // efficient later processing.
  for (PersistentCardMap::const_iterator fit = persistentMap.begin();
       fit != persistentMap.end(); ++fit) {
    pair<ID, PersistentSignalCard> card = *fit;
    ID var = card.first;
    if (ignore.find(var) != ignore.end()) continue;
    if (card.second.numberTransitions == 0 && card.second.initialValue != TVX) {
      equivalences[var] = (card.second.finalValue == TVTrue) ? ev.btrue() : ev.bfalse();
    } else {
      nonStuck.push_back(card);
    }
  }
  if (equivalences.size() > 0)
    classes = 1;

  // Sort vector so that we can quickly terminate searches for equivalent
  // and complementary signals.  Such signals must have the same numbers
  // of transitions, first transition time, and last transition time.
  // If we sort on these keys, we can skip the rest of the list as soon
  // as one signals strictly precedes the other in the order.
  sort(nonStuck.begin(), nonStuck.end(), comparePersistent);

  // Look for equivalent and complementary persistent signals.
  for (cardVec::const_iterator fit = nonStuck.begin();
       fit != nonStuck.end(); ++fit) {
    pair<ID, PersistentSignalCard> card = *fit;
    ID var = card.first;
    if (card.second.wasX) continue;
    // Only consider the representative of each equivalence class.
    unordered_map<ID,ID>::const_iterator it1 = equivalences.find(var);
    if (it1 != equivalences.end() && it1->second != var) continue;
    TVvec::size_type p1 = card.second.position;
    cardVec::const_iterator sit = fit;
    for (++sit; sit != nonStuck.end(); ++sit) {
      pair<ID, PersistentSignalCard> scard = *sit;
      ID scndVar = scard.first;
      if (equivalences.find(scndVar) != equivalences.end()) continue;
      if (scard.second.firstTransition > card.second.firstTransition ||
          scard.second.lastTransition > card.second.lastTransition ||
          scard.second.numberTransitions > card.second.numberTransitions) break;
      if (!scard.second.wasX) {
        // They could be either equivalent or complementary.
        TVvec::size_type p2 = scard.second.position;
        if (scard.second.initialValue == card.second.initialValue &&
            scard.second.finalValue == card.second.finalValue) {
          // Check for equivalence.
          bool equivalent = true;
          // If the two signals have just one transition, they are equivalent.
          if (card.second.numberTransitions > 1) {
            for (vecSeq::const_iterator lit = lasso.begin() + card.second.firstTransition + 1;
                 lit != lasso.begin() + card.second.lastTransition; ++lit) {
              PackedTvVector const & vec = *lit;
              if (vec[p1] != vec[p2] || vec[p1] == TVX) {
                equivalent = false;
                break;
              }
            }
          }
          if (equivalent) {
            // Put the two latches in the same class.  We know that the second
            // is not in a class yet.
            if (verbosity > Options::Verbose)
              cout << stringOf(ev, scndVar) << " equivalent to " << stringOf(ev, var);
            it1 = equivalences.find(var);
            if (it1 == equivalences.end()) {
              equivalences[var] = var;
              equivalences[scndVar] = var;
              if (verbosity > Options::Verbose)
                cout << ": representative is " << stringOf(ev, var) << endl;
            } else {
              ID rep = it1->second;
              equivalences[scndVar] = rep;
              if (verbosity > Options::Verbose)
                cout << ": representative is " << stringOf(ev, rep) << endl;
            }
          }
        } else if (scard.second.initialValue != card.second.initialValue &&
                   scard.second.finalValue != card.second.finalValue) {
          // Check for complementarity.
          bool complementary = true;
          if (card.second.numberTransitions > 1) {
            for (vecSeq::const_iterator lit = lasso.begin() + card.second.firstTransition + 1;
                 lit != lasso.begin() + card.second.lastTransition; ++lit) {
              PackedTvVector const & vec = *lit;
              if (vec[p1] == vec[p2] || vec[p1] == TVX || vec[p2] == TVX) {
                complementary = false;
                break;
              }
            }
          }
          if (complementary) {
            if (verbosity > Options::Verbose)
              cout << stringOf(ev, scndVar) << " complementary to " << stringOf(ev, var);
            it1 = equivalences.find(var);
            if (it1 == equivalences.end()) {
              equivalences[var] = var;
              equivalences[scndVar] = ev.apply(Expr::Not, var);
              if (verbosity > Options::Verbose)
                cout << ": representative is " << stringOf(ev, var) << endl;
            } else {
              ID rep = it1->second;
              equivalences[scndVar] = ev.apply(Expr::Not, rep);
              if (verbosity > Options::Verbose)
                cout << ": representative is " << stringOf(ev, rep) << endl;
            }
          }
        }
      }
    }
  }
  //cout << equivalences.size() << " equivalences so far" << endl;

  // Look for implications between persistent signals.
  for (cardVec::const_iterator fit = nonStuck.begin();
       fit != nonStuck.end(); ++fit) {
    pair<ID, PersistentSignalCard> card = *fit;
    ID var = card.first;
    // Only consider implications between representatives (including singletons).
    unordered_map<ID,ID>::const_iterator it1 = equivalences.find(var);
    if (it1 != equivalences.end() && it1->second != var) continue;
    // Heuristic: only consider signals with one or two transitions.
    if (card.second.numberTransitions > 2) continue;
    //cout << fit - nonStuck.begin() << endl;
    TVvec::size_type p1 = card.second.position;
    cardVec::const_iterator sit = fit;
    for (++sit; sit != nonStuck.end(); ++sit) {
      pair<ID, PersistentSignalCard> scard = *sit;
      ID scndVar = scard.first;
      // Skip if not a representative or a singleton.
      unordered_map<ID,ID>::const_iterator it2 = equivalences.find(scndVar);
      if (it2 != equivalences.end() && it2->second != scndVar) continue;
      // Heuristic: only consider signals with one or two transitions.
      if (scard.second.numberTransitions > 2) continue;
      TVvec::size_type p2 = scard.second.position;
      // mask is encoded thus: 8 -> 11, 4 -> 10, 2 -> 01, 1 -> 00
      unsigned mask = 0;
      // Only compare signals from one step before their first
      // transition to one step after their last transition.  Because
      // of how they are sorted, the earliest transition time is
      // always from the first signal, but the latest could be from
      // either.  The earliest transition is at least 1: subtracting 1
      // is fine.  The cycle is at least 1.  If the last transition is
      // still in the stem, adding 2 gives at most the size of the
      // lasso, which is fine.  Otherwise, we take the size of the lasso.
      vecSeq::size_type first = card.second.firstTransition - 1;
      vecSeq::size_type last = min(max(card.second.lastTransition,
                                       scard.second.lastTransition) + 2,
                                   lasso.size());
      for (vecSeq::size_type it = first; it < last; ++it) {
        TV const t1 = lasso[it][p1];
        TV const t2 = lasso[it][p2];
        if (t1 == TVTrue) {
          if (t2 == TVTrue) mask |= 8;
          else if (t2 == TVFalse) mask |= 4;
          else mask |= 12;
        } else if (t1 == TVFalse) {
          if (t2 == TVTrue) mask |= 2;
          else if (t2 == TVFalse) mask |= 1;
          else mask |= 3;
        } else { // TVX
          if (t2 == TVTrue) mask |= 10;
          else if (t2 == TVFalse) mask |= 5;
          else mask |= 15;
        }
        if (mask == 15) break;
      }
      if (mask != 15) {
        // Implications found.  Since the signals are not constant
        // and they are neither equivalent nor complementary, at most one
        // implication is possible.
        bool reverse = var > scndVar;
        ID l1, l2;
        if (~mask & 1) { // (false, false) never occurs
          l1 = reverse ? scndVar : var;
          l2 = reverse ? var : scndVar;
        } else if (~mask & 2) { // (false, true) never occurs 
          l1 = reverse ? ev.apply(Expr::Not, scndVar) : var;
          l2 = reverse ? var : ev.apply(Expr::Not, scndVar);
        } else if (~mask & 4) { // (true, false) never occurs 
          l1 = reverse ? scndVar : ev.apply(Expr::Not, var);
          l2 = reverse ? ev.apply(Expr::Not, var) : scndVar;
        } else { // (true, true) never occurs 
          l1 = ev.apply(Expr::Not, (reverse ? scndVar : var));
          l2 = ev.apply(Expr::Not, (reverse ? var : scndVar));
        }
        implications.insert(implSet::value_type(l1, l2));
      }
    }
  }

  // Look for equivalent and complementary periodic signals.
  for (PeriodicCardMap::const_iterator fit = periodicMap.begin();
       fit != periodicMap.end(); ++fit) {
    pair<ID, PeriodicSignalCard> card = *fit;
    ID var = card.first;
    if (ignore.find(var) != ignore.end()) continue;
    if (card.second.wasX) continue;
    unordered_map<ID,ID>::const_iterator it1 = equivalences.find(var);
    if (it1 != equivalences.end() && it1->second != var) continue;
    TVvec::size_type p1 = card.second.position;
    PeriodicCardMap::const_iterator sit = fit;
    for (++sit; sit != periodicMap.end(); ++sit) {
      pair<ID, PeriodicSignalCard> scard = *sit;
      ID scndVar = scard.first;
      unordered_map<ID,ID>::const_iterator it2 = equivalences.find(scndVar);
      if (it2 != equivalences.end()) continue;
      if (scard.second.period == card.second.period &&
          scard.second.start == card.second.start &&
          !scard.second.wasX) {
        bool equivalent = true;
        // Check periodic part of signal.
        for (TVvec::size_type w = 0; w < card.second.period; ++w) {
          if (scard.second.wave[w] != card.second.wave[w]) {
            equivalent = false;
            break;
          }
        }
        // If periodic part is the same, check stem.
        if (equivalent) {
          TVvec::size_type p2 = scard.second.position;
          for (vecSeq::const_iterator lit = lasso.begin();
               lit != lasso.begin() + card.second.start; ++lit) {
            if ((*lit)[p1] != (*lit)[p2]) {
              equivalent = false;
              break;
            }
          }
        }
        if (equivalent) {
          if (verbosity > Options::Verbose)
            cout << stringOf(ev, scndVar) << " equivalent to " << stringOf(ev, var);
          it1 = equivalences.find(var);
          if (it1 == equivalences.end()) {
            equivalences[var] = var;
            equivalences[scndVar] = var;
            if (verbosity > Options::Verbose)
              cout << ": representative is " << stringOf(ev, var) << endl;
          } else {
            ID rep = it1->second;
            equivalences[scndVar] = rep;
            if (verbosity > Options::Verbose)
              cout << ": representative is " << stringOf(ev, rep) << endl;
          }
        }
      }
    }
  }

  // Look for implications between periodic signals.
  for (PeriodicCardMap::const_iterator fit = periodicMap.begin();
       fit != periodicMap.end(); ++fit) {
    pair<ID, PeriodicSignalCard> card = *fit;
    ID var = card.first;
    if (ignore.find(var) != ignore.end()) continue;
    if (card.second.wasX) continue;
    unordered_map<ID,ID>::const_iterator it1 = equivalences.find(var);
    if (it1 != equivalences.end() && it1->second != var) continue;
    TVvec::size_type p1 = card.second.position;
    PeriodicCardMap::const_iterator sit = fit;
    for (++sit; sit != periodicMap.end(); ++sit) {
      pair<ID, PeriodicSignalCard> scard = *sit;
      ID scndVar = scard.first;
      unordered_map<ID,ID>::const_iterator it2 = equivalences.find(scndVar);
      if (it2 != equivalences.end() && it2->second != scndVar) continue;
      // Heuristic: Only consider pairs of signals with the same period.
      if (scard.second.period != card.second.period) continue;
      TVvec::size_type p2 = scard.second.position;
      // mask is encoded thus: 8 -> 11, 4 -> 10, 2 -> 01, 1 -> 00
      unsigned mask = 0;
      for (vecSeq::const_iterator it = lasso.begin();
           it != lasso.end(); ++it) {
        TV const t1 = (*it)[p1];
        TV const t2 = (*it)[p2];
        if (t1 == TVTrue) {
          if (t2 == TVTrue) mask |= 8;
          else if (t2 == TVFalse) mask |= 4;
          else mask |= 12;
        } else if (t1 == TVFalse) {
          if (t2 == TVTrue) mask |= 2;
          else if (t2 == TVFalse) mask |= 1;
          else mask |= 3;
        } else { // TVX
          if (t2 == TVTrue) mask |= 10;
          else if (t2 == TVFalse) mask |= 5;
          else mask |= 15;
        }
        if (mask == 15) break;
      }
      if (mask != 15) {
        // Implications found.  Since the signals are not constant
        // and they are neither equivalent nor complementary, at most one
        // implication is possible.
        bool reverse = var > scndVar;
        ID l1, l2;
        if (~mask & 1) { // (false, false) never occurs
          l1 = reverse ? scndVar : var;
          l2 = reverse ? var : scndVar;
        } else if (~mask & 2) { // (false, true) never occurs 
          l1 = reverse ? ev.apply(Expr::Not, scndVar) : var;
          l2 = reverse ? var : ev.apply(Expr::Not, scndVar);
        } else if (~mask & 4) { // (true, false) never occurs 
          l1 = reverse ? scndVar : ev.apply(Expr::Not, var);
          l2 = reverse ? ev.apply(Expr::Not, var) : scndVar;
        } else { // (true, true) never occurs 
          l1 = ev.apply(Expr::Not, (reverse ? scndVar : var));
          l2 = ev.apply(Expr::Not, (reverse ? var : scndVar));
        }
        implications.insert(implSet::value_type(l1, l2));
      }
    }
  }

  // Report.
  if (verbosity > Options::Silent) {
    for (unordered_map<ID,ID>::const_iterator it = equivalences.begin();
         it != equivalences.end(); ++it) {
      if (it->first == it->second)
        ++classes;
    }
    cout << "Found " << equivalences.size() << " equivalent signals in " << classes
         << " classes and " << implications.size() << " implications among latches"
         << endl;
    if (verbosity > Options::Verbose) {
      for (unordered_map<ID,ID>::const_iterator it = equivalences.begin();
           it != equivalences.end(); ++it) {
        cout << stringOf(ev, it->first) << " -> " << stringOf(ev, it->second) << endl;
      }
      for (implSet::const_iterator it = implications.begin();
           it != implications.end(); ++it) {
        cout << stringOf(ev, it->first) << " | " << stringOf(ev, it->second) << endl;
      }
    }
  }
}


/** Simplify the model based on the constraints extracted from the ternary
 *  simulation results. */
void simplifyModel(
  Model & model,
  Expr::Manager::View & ev,
  unordered_set<ID> const & ignore,
  vecSeq const & lasso,
  PersistentCardMap const & persistentMap,
  PeriodicCardMap const & periodicMap)
{
  Options::Verbosity verbosity = model.verbosity();
  implSet implications;
  unordered_map<ID,ID> equivalences;
  ExprAttachment * eat = (ExprAttachment *) model.attachment(Key::EXPR);
  if (eat->stateVars().size() > 600)
    findImplicationsLight(ev, ignore, persistentMap, periodicMap, lasso,
                          implications, equivalences, verbosity);
  else
    findImplications(ev, eat->stateVars(), ignore, lasso, implications, equivalences, verbosity);
  Expr::Simplifier simp(ev, implications, equivalences, verbosity);

  vector<ID> sv(eat->stateVars());
  vector<ID> nsf(eat->nextStateFns());
  eat->clearNextStateFns();
  simp.simplify(nsf);
  eat->setNextStateFns(sv, nsf);

  vector<ID> outputs(eat->outputs());
  vector<ID> of(eat->outputFns());
  eat->clearOutputFns();
  simp.simplify(of);
  eat->setOutputFns(outputs, of);

  vector<ID> constraints(eat->constraints());
  vector<ID> constraintFns(eat->constraintFns());
  eat->clearConstraints();
  simp.simplify(constraintFns);
  for (vector<ID>::size_type i = 0; i != constraintFns.size(); ++i) {
    if (constraintFns[i] != ev.btrue())
      eat->addConstraint(constraints[i], constraintFns[i]);
  }
  unordered_set<ID> lset(sv.begin(), sv.end());
  vector<ID> constrVec;
  for (implSet::const_iterator it = implications.begin(); it != implications.end(); ++it) {
    ID lit0 = it->first;
    ID lit1 = it->second;
    ID n0 = ev.apply(Expr::Not, lit0);
    ID n1 = ev.apply(Expr::Not, lit1);
    ID var0 = (ev.op(lit0) == Expr::Not) ? n0 : lit0;
    ID var1 = (ev.op(lit1) == Expr::Not) ? n1 : lit1;
    if (lset.find(var0) == lset.end() || lset.find(var1) == lset.end())
      continue;
    ID cid = ev.apply(Expr::Or, lit0, lit1);
    constrVec.push_back(cid);
  }
  Expr::varSub(ev, equivalences, constrVec);
  sort(constrVec.begin(), constrVec.end());
  vector<ID>::iterator newEnd = unique(constrVec.begin(), constrVec.end());
  vector<ID>::size_type i = constraints.size();
  for (vector<ID>::const_iterator it = constrVec.begin(); it != newEnd; ++it) {
    if (*it == ev.btrue())
      continue;
    ostringstream oss;
    oss << 'c' << i;
    string nm = oss.str();
    ID vid = ev.newVar(nm);
    ++i;
    eat->addConstraint(vid, *it);
  }

  // Should we simplify the rest?

  model.release(eat);
}

/** Simplify constrained TR expressions. 
 *  Use ternary simulation to produce constraints. */
void simplifyTV(
  Expr::Manager::View & ev,
  AIGAttachment const * aat,
  vector<ID> const & stateVars,
  vector<ID> & nextStateFns,
  vector<ID> & outputFns,
  vector<ID> const & init,
  unordered_map<ID,ID> const & assignments,
  Options::Verbosity verbosity,
  bool allowWidening,
  int * pconclusion,
  unsigned int * pstemLength,
  unsigned int * ploopLength,
  unsigned int * pstabilized,
  unsigned int * pfirstNonzero,
  bool * pwidened)
{
  // Ternary simulation to find periodic and persistent signals.
  vecSeq lasso;
  vecSeq::size_type stem = ThreeValued::computeLasso(ev, init, outputFns, aat, lasso,
                                                     verbosity, allowWidening, pconclusion,
                                                     pfirstNonzero, pwidened);

  if (pconclusion != 0 && *pconclusion != 2) return;

   // Find (eventually) periodic and persistent signals.
  PersistentCardMap persistentMap;
  PeriodicCardMap periodicMap;
  findInterestingSignals(lasso, stateVars, stem, persistentMap, periodicMap);

  printReport(verbosity, lasso, ev, stateVars, persistentMap, periodicMap);

  implSet implications;
  unordered_map<ID,ID> equivalences(assignments);
  if (stateVars.size() > 600)
    findImplicationsLight(ev, unordered_set<ID>(), persistentMap, periodicMap,
                          lasso, implications, equivalences, verbosity);
  else
    findImplications(ev, stateVars, unordered_set<ID>(), lasso, implications, equivalences, verbosity);
  if (verbosity > Options::Silent) {
    vector<ID> roots(nextStateFns);
    roots.insert(roots.end(), outputFns.begin(), outputFns.end());
    cout << "Node count before tvsim = " << sizeOf(ev, roots) << endl;
  }
  Expr::Simplifier simp(ev, implications, equivalences, verbosity);
  simp.simplify(nextStateFns);
  simp.simplify(outputFns);
  if (verbosity > Options::Silent) {
    vector<ID> roots(nextStateFns);
    roots.insert(roots.end(), outputFns.begin(), outputFns.end());
    cout << "Node count after tvsim = " << sizeOf(ev, roots) << endl;
  }
  unsigned int maxstable = 0;
  for (PersistentCardMap::const_iterator it = persistentMap.begin();
       it != persistentMap.end(); ++it) {
    pair<ID, PersistentSignalCard> card = *it;
    if (card.second.lastTransition > maxstable)
      maxstable = card.second.lastTransition;
  }
  if (verbosity > Options::Silent) {
    cout << "All persistent signal stable at cycle " << maxstable << endl;
  }
  if (pstabilized != 0) {
    *pstabilized = maxstable;
  }
  if (pstemLength != 0)
    *pstemLength = stem;
  if (ploopLength != 0)
    *ploopLength = lasso.size() - stem;
}

namespace {

void rewriteModel(
  Model & model,
  ExprAttachment * eat,
  vector<ID> const & nsf,
  vector<ID> const & of)
{
  //Options::Verbosity verbosity = model.verbosity();
  vector<ID> sv(eat->stateVars());
  eat->clearNextStateFns();
  eat->setNextStateFns(sv, nsf);

  vector<ID> outputs(eat->outputs());
  eat->clearOutputFns();
  eat->setOutputFns(outputs, of);

  // We could do more.
  // We should fix the sequential attachment.
}


} // anonymous

void TvSimplifierAction::exec()
{
  // Setup.  Get attachments and such stuff.
  int64_t startTime = Util::get_user_cpu_time();
  Options::Verbosity verbosity = _model.verbosity();
  if (verbosity > Options::Silent)
    cout << "TV simplification of model " << _model.name() << endl;

  ExprAttachment * eat = (ExprAttachment *) _model.attachment(Key::EXPR);
  AIGAttachment const * aat = (AIGAttachment const *) _model.constAttachment(Key::AIG);

  Expr::Manager::View * ev = _model.newView();

  vector<ID> nsfv(eat->nextStateFns());
  vector<ID> ofv(eat->outputFns());
  unordered_map<ID,ID> assignments;
  bool allowWidening = _model.options().count("tv_narrow") == 0;
  bool noOutputCheck = _model.options().count("tv_nocheck") != 0;
  Model::Mode mode = _model.defaultMode();
  if (verbosity > Options::Verbose)
    cout << "mode = " << mode << endl;
  if (mode == Model::mFAIR || mode == Model::mIICTL)
    noOutputCheck = true;
  int conclusion = 2;
  unsigned int stemLength;
  unsigned int loopLength;
  unsigned int stabilized;
  unsigned int firstNonzero;
  bool widened;
  if (noOutputCheck) {
    simplifyTV(*ev, aat, eat->stateVars(), nsfv, ofv, eat->initialConditions(),
               assignments, verbosity, allowWidening, 0,  &stemLength,
               &loopLength, &stabilized, &firstNonzero, &widened);
  } else {
    simplifyTV(*ev, aat, eat->stateVars(), nsfv, ofv, eat->initialConditions(),
               assignments, verbosity, allowWidening, &conclusion, &stemLength,
               &loopLength, &stabilized, &firstNonzero, &widened);
  }
  if (conclusion == 2) {
    rewriteModel(_model, eat, nsfv, ofv);
    if (verbosity > Options::Terse) {
      cout << "RAT: stem: " << stemLength << " loop: " << loopLength
           << " stable at: " << stabilized << " nonzero: "
           << firstNonzero << " widened: " << widened << endl;
    }
    RchAttachment * rat = (RchAttachment *) _model.attachment(Key::RCH);
    rat->setTvInfo(stemLength, loopLength, stabilized, widened);
    rat->updateCexLowerBound(firstNonzero);
    _model.release(rat);
  } else {
    ProofAttachment * pat = (ProofAttachment *) _model.attachment(Key::PROOF);
    assert(pat != 0);
    pat->setConclusion(conclusion);
    _model.release(pat);
  }
  delete ev;
  _model.constRelease(aat);
  _model.release(eat);

  int64_t endTime = Util::get_user_cpu_time(); 
  if (verbosity > Options::Silent)
    cout << "Expression simplifier completed in "
         << ((endTime - startTime) / 1000000.0) << " s" << endl;
}
