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

#include "Util.h"
#include "ThreeValuedSimulation.h"

using namespace std;

namespace ThreeValued {
  AIGTVSim::AIGTVSim(const AIGAttachment * _aat) :
    aat(_aat), aig(aat->aig), tvs(aig.size(), TVX), isMux(aig.size(), 1),
    _inputBegin(tvs.begin() + 1), _inputEnd(_inputBegin + aig.numInputs()),
    _latchBegin(_inputEnd), _latchEnd(_latchBegin + aig.numStateVars()),
    nsValues(aig.numStateVars()), outputValues(aig.outputFnRefs().size()) {
      tvs[0] = TVFalse; //the false node
  }

  void AIGTVSim::reset(Expr::Manager::View & view, const vector<ID> & init) {
    // Set all latch values to TVX
    for (vector<TV>::iterator it = _latchBegin; it != _latchEnd; ++it) {
      *it = TVX;
    }

    //Overwrite them with values from init
    // assumes AIGER 1.9
    for (size_t i = 0; i < init.size(); ++i) {
      if (view.op(init[i]) == Expr::Not) {
        ID latch = view.apply(Expr::Not, init[i]);
        Opt::IDRefMap::const_iterator it = aat->id2ref.find(latch);
        assert(it != aat->id2ref.end());
        tvs[UIGET(Opt::indexOf(it->second))] = TVFalse;
      }
      else {
        assert(view.op(init[i]) == Expr::Var);
        Opt::IDRefMap::const_iterator it = aat->id2ref.find(init[i]);
        assert(it != aat->id2ref.end());
        tvs[UIGET(Opt::indexOf(it->second))] = TVTrue;
      }
    }
  }

  void AIGTVSim::step() {
    simulate();

    //Extract next-state values and set latch values accordingly
    for (unsigned int i = 0; i < aig.nextStateFnRefs().size(); ++i) {
      TV val = tvs[UIGET(Opt::indexOf(aig.nextStateFnRefs()[i]))];
      TV nsfVal = Opt::isNot(aig.nextStateFnRefs()[i]) ?  tv_not(val) : val; 
      nsValues[i] = nsfVal;
    }
    //Extract output values
    for (unsigned int i = 0; i < aig.outputFnRefs().size(); ++i) {
      TV val = tvs[UIGET(Opt::indexOf(aig.outputFnRefs()[i]))];
      TV outputVal = Opt::isNot(aig.outputFnRefs()[i]) ?  tv_not(val) : val; 
      outputValues[i] = outputVal;
    }
    copy(nsValues.begin(), nsValues.end(), _latchBegin);
  }

  vector<TV>::iterator AIGTVSim::inputBegin() {
    return _inputBegin;
  }

  vector<TV>::iterator AIGTVSim::inputEnd() {
    return _inputEnd;
  }

  vector<TV>::iterator AIGTVSim::latchBegin() {
    return _latchBegin;
  }

  vector<TV>::iterator AIGTVSim::latchEnd() {
    return _latchEnd;
  }

  const vector<TV> & AIGTVSim::getNSValues() const {
    return nsValues;
  }

  const vector<TV> & AIGTVSim::getOutputValues() const {
    return outputValues;
  }

  void AIGTVSim::simulate() {
    for (unsigned i = aig.numInputs() + aig.numStateVars() + 1; i < aig.size(); ++i) {
      Opt::NodeRef fanin1 = aig[i][0];
      Opt::NodeRef fanin2 = aig[i][1];
      TV fanin1Val = Opt::isNot(fanin1) ? tv_not(tvs[UIGET(Opt::indexOf(fanin1))]) : 
                                          tvs[UIGET(Opt::indexOf(fanin1))];
      TV fanin2Val = Opt::isNot(fanin2) ? tv_not(tvs[UIGET(Opt::indexOf(fanin2))]) : 
                                          tvs[UIGET(Opt::indexOf(fanin2))];

      tvs[i] = tv_and(fanin1Val, fanin2Val);
      if (tvs[i] == TVX && isMux[i]) {
        bool ismux = mux(aig, i, tvs);
        if (!ismux)
          isMux[i] = 0;
      }
    }
  }

  void BrieTV::insert(PackedTvVector const & key)
  {
    TVvec::size_type index = lasso.size();
    lasso.push_back(key);
    m.insert(mapval(key.hash(), index));
  }

  vecSeq::const_iterator BrieTV::find(PackedTvVector const & key) const
  {
    hval h = key.hash();
    std::pair<map::const_iterator,map::const_iterator> range = m.equal_range(h);
    for (map::const_iterator it = range.first; it != range.second; ++it) {
      vecSeq::size_type i = it->second;
      if (lasso[i] == key) return lasso.cbegin() + i;
    }
    return lasso.cend();
  }

}

namespace {

  using namespace ThreeValued;

  /** Perform widening (setting latches to X) if
   *  simulation does not converge rapidly. */
  class WidenIfSlow {
  public:
    WidenIfSlow(vecSeq const & ls, Options::Verbosity verb,
                bool wide = true, int finalTime = -1):
      lasso(ls), tCounts(ls.front().size(), 0), i(1), mask(255),
      verbosity(verb), widen(wide), finalTime(finalTime) {}

    bool operator()(TVvec & vec) {
      bool widened = false;
      // Check is done periodically.
      if ((lasso.size() & mask) == mask) {
        // Update transition counts.
        for (; i < lasso.size(); ++i) {
          for (TVvec::size_type j = 0; j < vec.size(); ++j) {
            if (lasso[i][j] != lasso[i-1][j])
              ++tCounts[j];
          }
        }
        // Report.
        if (verbosity > Options::Terse) {
          cout << "@" << lasso.size() << ": ";
          TVvec::size_type xCount = 0;
          vecSeq::size_type stable = 0;
          for (TVvec::size_type j = 0; j < vec.size(); ++j) {
            if (vec[j] == TVX) ++xCount;
            else if (tCounts[j] < 2) ++stable;
          }
          cout << xCount << "/" << vec.size() << " X " << stable << " stable";
          vecSeq::size_type min = lasso.size(), max = 0, tot = 0;
          for (vector< vecSeq::size_type >::const_iterator it = tCounts.begin();
               it != tCounts.end(); ++it) {
            vecSeq::size_type count = *it;
            if (count < min) min = count;
            if (count > max) max = count;
            tot += count;
          }
          cout << " m=" << min << " M=" << max << " tot=" << tot;
        }
        // Allow grace period to let things settle a bit.
        if (lasso.size() < 32767 && (finalTime == -1 || Util::get_user_cpu_time() < finalTime)) {
          if (verbosity > Options::Terse) {
            if (widen)
              cout << ": no widening";
            cout << endl;
          }
          return false;
        }
        // Widen.
        TVvec::size_type wCount = 0;
        TVvec::size_type pCount = 0;
        if (widen) {
          for (TVvec::size_type j = 0; j < vec.size(); ++j) {
            if (vec[j] != TVX && tCounts[j] > 32) {
              if (looksPeriodic(j)) {
                ++pCount;
              } else {
                vec[j] = TVX;
                ++wCount;
              }
            }
          }
        }
        widened = wCount > 0;
        if (verbosity > Options::Terse) {
          if (widen)
            cout << " w " << wCount << " p " << pCount;
          cout << endl;
        }
      }
      return widened;
    }

  private:

    /** Does the last segment of this signal have a short period ?
     *  It is assumed that the signal is not TVX. */
    bool looksPeriodic(TVvec::size_type j)
    {
      TVvec::size_type transitions = tCounts[j];
      if (transitions < i/6)
        return false;
      // High-activity signal.  Check last segment for period 8.
      // (This catches also periods 4 and 2.)
      bool periodic = true;
      for (TVvec::size_type k = i - 1; k > i - mask + 7; --k) {
        if (lasso[k][j] != lasso[k-8][j]) {
          periodic = false;
          break;
        }
      }
      return periodic;
    }


    vecSeq const & lasso;
    vector<vecSeq::size_type> tCounts;
    vecSeq::size_type i;
    vecSeq::size_type const mask;
    Options::Verbosity verbosity;
    bool widen;
    int finalTime;
  };

} // anonymous


namespace ThreeValued {

  PackedTvVector::Proxy & PackedTvVector::Proxy::operator=(TV val)
  {
    value = val;
    ref.set(index, val);
    return *this;
  }


  PackedTvVector::Proxy & PackedTvVector::Proxy::operator=(Proxy const & rhs)
  {
    // Works for self-assignment too.
    value = rhs.value;
    ref.set(index, value);
    return *this;
  }


  /**
   * Construct a PackedTvVector with unpacked size vs.
   */
  PackedTvVector::PackedTvVector(size_type vs)
  {
    usize = vs;
    size_type psize = (usize + packing_ratio - 1) / packing_ratio;
    data.resize(psize);
  }


  /**
   * Construct a PackedTvVector initialized with the contents
   * of unpacked vector v.
   */
  PackedTvVector::PackedTvVector(std::vector<TV> const & v)
  {
    usize = v.size();
    hashv = 0;
    size_type psize = (usize + packing_ratio - 1) / packing_ratio;
    data.resize(psize);
    for (size_type i = 0; i < psize; ++i) {
      storage_t elem = 0;
      for (size_type j = 0; j < packing_ratio; ++j) {
        std::vector<TV>::size_type k = i * packing_ratio + j;
        if (k < usize)
          elem |= (storage_t) v[k] << (storage_t) (j << 1);
        else
          break;
      }
      data[i] = elem;
      hashv ^= (unsigned long) elem;
      hashv *= 0x9e3779b9UL;
    }
  }


  /**
   * Copy constructor.
   */
  PackedTvVector::PackedTvVector(PackedTvVector const & from) :
    usize(from.usize), data(from.data) {}


  /**
   * Assignment operator.
   */
  PackedTvVector & PackedTvVector::operator=(PackedTvVector const & rhs)
  {
    if (&rhs != this) {
      usize = rhs.usize;
      data = rhs.data;
    }
    return *this;
  }


  /**
   * Getter.
   */
  TV PackedTvVector::at(size_type i) const
  {
    size_type word = findWord(i);
    size_type shift = findShift(i);
    return (TV) ((data[word] >> shift) & 3);
  }


  /**
   * Setter.
   */
  void PackedTvVector::set(size_type i, TV val)
  {
    size_type word = findWord(i);
    size_type shift = findShift(i);
    storage_t elem = data[word] & ~((storage_t) 3 << shift);
    data[word] = elem | ((storage_t) val << shift);
  }


  /**
   * Appends the contents of the PackedTvVector to the end of
   * unpacked vector v.  
   */
  void PackedTvVector::unpack(std::vector<TV> & v) const
  {
    for (PackedTvVector::size_type i = 0; i < usize; ++i) {
      TV val = at(i);
      v.push_back(val);
    }
  }


  bool operator==(PackedTvVector const & a, PackedTvVector const & b)
  {
    return a.data == b.data;
  }


  std::ostream & operator<<(std::ostream & os, TV t)
  {
    os << (t == TVTrue ? "1" : t == TVFalse ? "0" : "X");
    return os;
  }


  std::ostream & operator<<(std::ostream & os, PackedTvVector const & v) 
  {
    for (PackedTvVector::size_type i = 0; i < v.size(); ++i) {
      TV val = v.at(i);
      os << val;
    }
    return os;
  }


  /**
   * Checks for early termination of simulation because of violation
   * of a safety property.  This happens if the output is unambiguously
   * true.  This function also discharges reporting duties.
   */
  void checkEarlyConclusion(
    vector<ID> const & outputFns,
    int * pconclusion,
    Model::Mode mode,
    AIGTVSim const & tvsim,
    vecSeq::size_type thisStep,
    unsigned int * pfirstNonzero,
    TV & outVal,
    bool & unchanged,
    Options::Verbosity verbosity)
  {
    if (mode == Model::mIC3) {
      assert(outputFns.size() == 1);
      TV newOutVal = tvsim.getOutputValues()[0];
      if (outVal != newOutVal) {
        if (unchanged) {
          if (verbosity > Options::Silent) {
            cout << "First output change at cycle " << thisStep << ": "
                 << newOutVal << endl;
          }
          unchanged = false;
          if (pfirstNonzero != 0)
            *pfirstNonzero = thisStep;
        } else if (!unchanged && verbosity > Options::Terse) {
          cout << "Output changed at cycle " << thisStep << ": "
               << newOutVal << endl;
        }
        if (newOutVal == TVTrue && pconclusion != 0) {
          // Early termination.
          if (verbosity > Options::Silent) {
            cout << "Output definitely SAT after " << thisStep
                 << " steps" << endl;
          }
          *pconclusion = 1;
        }
        outVal = newOutVal;
      }
    }
  }


  /** Perform ternary simulation to convergence. */
  vecSeq::size_type computeLasso(
    Expr::Manager::View & ev,
    vector<ID> const & init,
    vector<ID> const & outputFns,
    AIGAttachment const * aat,
    vecSeq & lasso,
    vecSeq & outputValues,
    Options::Verbosity verbosity,
    bool allowWidening,
    int * pconclusion,
    Model::Mode mode,
    unsigned int * pfirstNonzero,
    bool * pwidened,
    int finalTime)
  {
    if (verbosity > Options::Informative && outputFns.size() == 1) {
      ostringstream oss;
      shortStringOfID(ev, outputFns[0], oss);
      cout << "Output " << oss.str() << endl;
    }
    AIGTVSim tvsim(aat);

    // Assumes AIGER 1.9: every latch is individually initialized.
    tvsim.reset(ev, init);

    // Accumulate in lasso the patterns obtained by simulation
    // until a loop is detected.
    vecSeq::size_type stem = 0;
    // The "brie" manages insertions and searches.
    ThreeValued::BrieTV brie(lasso);
    TVvec latchTVs(tvsim.latchBegin(), tvsim.latchEnd());
    // The order of the following two statements is important.
    brie.insert(latchTVs);
    WidenIfSlow widen(lasso, verbosity, allowWidening, finalTime);
    bool widened = false;
    // Initial settings for safety conclusion check.
    TV outVal = TVFalse;
    bool unchanged = true;
    // Simulation loop.
    while (true) {
      tvsim.step();
      vecSeq::size_type thisStep = lasso.size() - 1;
      // Check for conclusion.  This check is for safety properties.
      checkEarlyConclusion(outputFns, pconclusion, mode, tvsim,
                           thisStep, pfirstNonzero, outVal,
                           unchanged, verbosity);
      if (pconclusion != 0 && *pconclusion == 1)
        return thisStep;
      // Extract latch values from simulation result.
      latchTVs = tvsim.getNSValues();
      widened |= widen(latchTVs);
      PackedTvVector platch(latchTVs);
      if (pconclusion != 0 && mode == Model::mFAIR) {
        PackedTvVector poutputs(tvsim.getOutputValues());
        outputValues.push_back(poutputs);
      }
      vecSeq::const_iterator lit = brie.find(platch);
      if (lit != lasso.cend()) {
        stem = lit - lasso.cbegin();
        break;
      }
      brie.insert(platch);
      // Make next state values current in preparation for next cycle.
      copy(latchTVs.begin(), latchTVs.end(), tvsim.latchBegin());
    }
    if (mode == Model::mIC3) {
      if (unchanged) {
        if (pconclusion != 0)
          *pconclusion = 0;
        // Passing property.
        if (verbosity > Options::Silent) {
          cout << "Output UNSAT over all reachable states" << endl;
        }
        if (pfirstNonzero != 0)
          *pfirstNonzero = lasso.size();
      }
    }
#if 0
    if (verbosity > Options::Informative) {
      cout << "Lasso capacity before shrinking: " << lasso.capacity() << endl;
    }
    lasso.shrink_to_fit();
    if (verbosity > Options::Informative) {
      cout << "Lasso capacity after shrinking: " << lasso.capacity() << endl;
    }
#endif

    // Report preliminary findings.
    if (verbosity > Options::Silent) {
      cout << "Stem length: " << stem << " Cycle: " << lasso.size() - stem
           << " (with" << (widened ? "" : "out") << " widening)" << endl;
    }
    if (pwidened != 0)
      *pwidened = widened;
    return stem;
  }

} // ThreeValued
