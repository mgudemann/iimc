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

#include<map>
#include<algorithm>
#include "TechMapCNF.h"
#include "Cut.h"
#include "CutAlgorithm.h"
#include "AIGAttachment.h"
#include "TurboTruthTable.h"

namespace
{


  class CNFCut : public CNF::Cut
  {
  protected:
    double cost;
    double cut_cost;

  public:

    CNFCut() : Cut(), cost(0.0)
    { }

    CNFCut(::Opt::NodeIndex i) : Cut(i), cost(0.0), cut_cost(0.0)
    { }

    CNFCut(const CNFCut& c) : Cut(c), cost(c.cost), cut_cost(c.cut_cost)
    { }

    // generate singleton cut
    template<typename CostFun>
    CNFCut(const CNF::AIG& aig, const std::vector<std::vector<CNFCut> >& cuts, const CNF::NodeIndex i, CostFun& cf) : Cut(i), cost(0.0)
    {
      computeCost(aig, cuts, i, cf);
    }

    template<typename CostFun>
    void computeCost(const CNF::AIG& aig, const std::vector<std::vector<CNFCut> >& cuts, CNF::NodeIndex i, CostFun& cf)
    {
      std::pair<double, double> costs = cf(aig, cuts, *this, i);
      cost = costs.first;
      cut_cost = costs.second;
    }

    CNFCut& operator=(const CNFCut& rhs)
    {
      *static_cast< ::CNF::Cut*>(this) = rhs;
      cost = rhs.cost;
      cut_cost = rhs.cut_cost;
      return *this;
    }

    bool operator<(const CNFCut& rhs) const
    { return cost < rhs.cost; }

    double getCost() const
    { return cost; }

    void setCost(const double c)
    { cost = c; }

    double getCutCost() const
    { return cut_cost; }

  };

}

namespace std {
  template<>
  struct hash<CNFCut> : public hash< ::CNF::Cut>
  { };
}

namespace {

#ifndef NIOS
  std::ostream& operator<<(std::ostream& ostr, CNFCut& c)
  {
    ostr << *static_cast<CNF::Cut*>(&c) << ": " << c.getCost();
    return ostr;
  }
#endif

  template<typename TTT, typename Map>
  void truthtable(const CNF::AIG& aig, const CNF::NodeIndex i, TTT& tt, Map& visited)
  {

    // handle false and true
    if(i == 0) {
      // i should be in visited
      assert(visited.find(i) != visited.end());
      tt.makefalse(visited[i]);
    }
    
    if(visited.find(i) != visited.end())
      return;


    truthtable(aig, ::Opt::indexOf(aig[i][0]), tt, visited);
    truthtable(aig, ::Opt::indexOf(aig[i][1]), tt, visited);

    assert(visited.find(::Opt::indexOf(aig[i][0])) != visited.end());
    assert(visited.find(::Opt::indexOf(aig[i][1])) != visited.end());

    typename Map::value_type::second_type tta;
    tt.copy(tta, visited[::Opt::indexOf(aig[i][0])]);
    if(::Opt::isNot(aig[i][0])) {
      tt.negate(tta);
    }

    typename Map::value_type::second_type ttb;
    tt.copy(ttb, visited[::Opt::indexOf(aig[i][1])]);
    if(::Opt::isNot(aig[i][1])) {
      tt.negate(ttb);
    }

    visited[i] = tta;
    tt.conjoin(tta, ttb);
  }


  struct CNFClauseCountCost
  {
    typedef ::TruthTable::TurboTruthTable ttt;
    unsigned cost_count;
    std::vector<unsigned> cut_size;
    ::TruthTable::TurboTruthTableManager tt;
    Options::Verbosity verbosity;

    CNFClauseCountCost(unsigned max_cut, Options::Verbosity v) : cost_count(0), cut_size(max_cut), verbosity(v)
    { }

    CNFClauseCountCost(const CNFClauseCountCost& c)
    {
      // do not copy a cost function
      assert(false);
    }

    void timeout()
    {
      if(verbosity >= ::Options::Informative)
        ::std::cout << "TMCNF: Timed out.  Switching to k = 2, l = 1" << ::std::endl;
    }


    std::pair<double, double> operator()(const CNF::AIG& aig, const std::vector<std::vector<CNFCut> >& cuts, CNFCut& c, const CNF::NodeIndex i)
    {
      // print cut
      //std::cout << "Calculating cost of cut: " << c << std::endl;
      if(c.contains(i)) {
      //if(c.size() == 1) {
        // trivial cut
        assert(c.contains(i));
        if(aig[i].isVar() || i == 0) {
          // zero cost for inputs
          return std::make_pair(0.0,0.0);
        } else {
          // cost equal to least expensive cut for trivial cut - processed last, so this is possible
          assert(cuts.size() > i);
          assert(cuts[UIGET(i)].size() > 0);
          double cost = cuts[UIGET(i)][0].getCost();
          return std::make_pair(cost, cost);
        }
      } else {
        // metrics ignore trivial cut costs and input costs
        ++cost_count;
        if(verbosity >= ::Options::Logorrheic) {
          if(cost_count % 10000 == 0)
            std::cout << cost_count << " Cost Functions Evaluated" << std::endl;
        }
        ++cut_size[c.size()-1];
        // generate truth table variables for cut
        typedef ::std::map<CNF::NodeIndex, ttt> ITTmap;
        ITTmap v;
        ttt empty;

        for(CNFCut::iterator it = c.begin(); it != c.end(); ++it) {
          v[*it] = empty;
          //std::cout << "Cut input: " << *it << std::endl;
        }

        tt.reset(v.begin(), v.end());

        //std::cout << "VSize: " << v.size() << std::endl;

        //std::cout << "TTSize: " << tt.size() << std::endl;

        // compute truth table of cut
        truthtable(aig, i, tt, v);

        //std::cout << "Evaluating Cost: " << tt.toString(v[i]) << std::endl;

        // compute cost of implementation
        
        std::vector<std::vector<long> > cover;
        tt.isop(v[i], cover);
        tt.negate(v[i]);
        tt.isop(v[i], cover);
        double cost = (double) cover.size();
        double cut_area = cost;

        typedef std::unordered_set<CNF::NodeIndex> VarList;
        VarList vars;
        for(unsigned clause_it = 0; clause_it < cover.size(); ++clause_it) {
          for(unsigned lit_it = 0; lit_it < cover[clause_it].size(); ++lit_it) {
            CNFCut::iterator cut_it = c.begin();
            std::advance(cut_it, std::abs(cover[clause_it][lit_it])-1);
            vars.insert(*cut_it);
          }
        }

        // enter cost for children implementation
        for(VarList::iterator it = vars.begin(); it != vars.end(); ++it) {
          assert(static_cast<unsigned>(UIGET(*it)) < cuts.size());
          assert(cuts[UIGET(*it)].size() != 0);
          double child_cost = cuts[UIGET(*it)][0].getCost();
          //std::cout << "  Child " << *it << " cost: " << child_cost << std::endl;
          cost += child_cost;
        }
        
        // divide cost by the fanout
        double res = cost / std::max(1.0,static_cast<double>(aig.nFanout(i)));
        return std::make_pair(res, cut_area);
      }
    }
  };

  void printCover(std::vector<std::vector<long> >& c)
  {
    for(unsigned i = 0; i < c.size(); ++i) {
      std::cout << " (";
      for(unsigned j = 0; j < c[i].size(); ++j) {
        std::cout << " " << c[i][j];
      }
      std::cout << ")";
    }
    std::cout << std::endl;
  }

  class generateCNF
  {
    typedef ::TruthTable::TurboTruthTable ttt;
    ::std::vector< ::std::vector< ::Opt::NodeRef> >& cnf;
    ::TruthTable::TurboTruthTableManager tt;
    ::Options::Verbosity verbosity;

  public:
    generateCNF(::std::vector< ::std::vector< ::Opt::NodeRef > >& cnf, ::Options::Verbosity v) : cnf(cnf), verbosity(v)
    { }


    void operator()(const CNF::AIG& aig, const CNFCut& c, const CNF::NodeIndex& i)
    {
      if(verbosity >= ::Options::Logorrheic)
        std::cout << "TMCNF: Picked cut " << c << "->" << i << std::endl;
      // generate truth table variables for cut
      typedef ::std::map<CNF::NodeIndex, ttt> ITTmap;
      ITTmap v;
      ttt empty;


      ::std::map<long, CNF::NodeIndex> vartoindex;
      unsigned index = 0;
      for(CNFCut::iterator it = c.begin(); it != c.end(); ++it, ++index) {
        v[*it] = empty;
        vartoindex[index] = *it;
      }

      tt.reset(v.begin(), v.end());

      // compute truth table of cut
      truthtable(aig, i, tt, v);


      // compute cover
      
      std::vector<std::vector<long> > pos_cover;
      std::vector<std::vector<long> > neg_cover;
      tt.isop(v[i], pos_cover);
      tt.negate(v[i]);
      tt.isop(v[i], neg_cover);

#if 0
      std::cout << "pos_cover: ";
      printCover(pos_cover);
      std::cout << "neg_cover: ";
      printCover(neg_cover);
#endif

      unsigned curr_clause = cnf.size();
      for(std::vector<std::vector<long> >::iterator clind = pos_cover.begin(); clind != pos_cover.end(); ++clind, ++curr_clause) {
        assert(cnf.size() == curr_clause);
        // make room for new clause
        cnf.resize(curr_clause+1);
        // add curr node id to clause
        cnf[curr_clause].push_back(::Opt::refOf(i, false));
        // add the negation of each literal to the clause
        for(std::vector<long>::iterator j = clind->begin(); j != clind->end(); ++j) {

          long l = *j;
          long ul = abs(l);
          bool neg = l < 0;
          cnf[curr_clause].push_back(::Opt::refOf(vartoindex[ul-1], !neg));
        }
      }

      
      for(std::vector<std::vector<long> >::iterator clind = neg_cover.begin(); clind != neg_cover.end(); ++clind, ++curr_clause) {
        // make room for new clause
        cnf.resize(curr_clause+1);
        // add curr node id to clause
        cnf[curr_clause].push_back(::Opt::refOf(i, true));
        // add the negation of each literal to the clause
        for(std::vector<long>::iterator j = clind->begin(); j != clind->end(); ++j) {

          long l = *j;
          long ul = abs(l);
          bool neg = l < 0;
          cnf[curr_clause].push_back(::Opt::refOf(vartoindex[ul-1], !neg));
        }
      }
    }
  };

  void printCuts(std::vector<std::vector<CNFCut> >& cuts)
  {
    for(unsigned i = 0; i < cuts.size(); ++i) {
      std::cout << "Node " << i << std::endl;
      for(unsigned j = 0; j < cuts[i].size(); ++j) {
        std::cout << "  " << cuts[i][j] << std::endl;
      }
    }
  }
} // namespace

namespace CNF
{
  void printCNF(std::vector<std::vector< ::Opt::NodeRef> >& cnf)
  {
    bool outfirst = true;
    for(unsigned i = 0; i < cnf.size(); ++i) {
      if(outfirst) {
        outfirst = false;
        std::cout << "(";
      } else {
        std::cout << ") /\\ (";
      }

      bool infirst = true;

      for(unsigned j = 0; j < cnf[i].size(); ++j) {
        if(infirst) {
          infirst = false;
        } else {
          std::cout << " \\/ ";
        }

        std::cout << cnf[i][j];
      }

    }

    std::cout << ")" << std::endl;
  }

  void techMap(Options::Verbosity verbosity, const ::AIGAttachment& aigat, unsigned k, unsigned b, unsigned refinements, ::std::vector< ::Opt::NodeRef>& outrefs, ::std::vector< ::std::vector< ::Opt::NodeRef> >& cnf, double timeOut, bool add_roots)
  {
    assert(k > 1);
    assert(b > 0);
    const AIG& aig = aigat.aig;
    
    // enumerate all of the cuts
    CNFClauseCountCost cf(k, verbosity);

    // create storage for cuts
    ::std::vector<std::vector<CNFCut> > cuts;

    if(verbosity >= ::Options::Verbose)
      ::std::cout << "TMCNF: Timeout: " << timeOut << ::std::endl;

    // seed cuts with trivial cut for false
    cuts.resize(1);
    cuts[0].push_back(CNFCut(0));
    if(verbosity >= ::Options::Verbose)
      ::std::cout << "TMCNF: Starting cut enumeration" << ::std::endl;
    int64_t en_start_time = ::Util::get_cpu_time(false);
    enumerateCuts(aig, cuts, k, b, timeOut, cf);
    int64_t en_end_time = ::Util::get_cpu_time(false);

    if(verbosity >= ::Options::Informative)
      ::std::cout << "TMCNF: Cut Enumeration time: " << static_cast<double>(en_end_time-en_start_time)/1000000.0 << ::std::endl;

    double timeleft = timeOut - static_cast<double>(en_end_time-en_start_time)/1000000.0;


    // get the outputs
    std::vector< NodeIndex> outputs;

    for(std::vector< ::Opt::NodeRef>::iterator i = outrefs.begin(); i != outrefs.end(); ++i) {
      outputs.push_back(::Opt::indexOf(*i));
    }

    //printCuts(cuts);

    if(refinements > 0 && timeleft > 0)
    {
      std::vector<int> refcount(aig.size());

      // generate initial mapping from area flow
      for(std::vector< ::Opt::NodeIndex>::iterator i = outputs.begin(); i != outputs.end(); ++i) {
        recursiveSelect(aig, cuts, refcount, *i, 0);
        // reference the outputs
        refcount[UIGET(*i)]++;
      }

      for(unsigned refine_count = 0; refine_count < refinements; ++refine_count) {
        //std::cout << "Refinement " << refine_count + 1 << std::endl;
        // perform refinement
        refineCuts(aig, cuts, refcount, timeleft);
        //printCuts(cuts);
      }

    }

    if(verbosity >= ::Options::Informative)
      ::std::cout << "TMCNF: Refinement time: " << static_cast<double>(::Util::get_cpu_time(false) - en_end_time)/1000000.0 << std::endl;

    // create a closure for generating the CNF
    generateCNF gcnf(cnf, verbosity);

    int64_t gn_start_time = ::Util::get_cpu_time(false);

    // visit best cuts according to cost function starting from the outputs
    bestCuts(aig, cuts, outputs.begin(), outputs.end(), gcnf);

    int64_t gn_end_time = ::Util::get_cpu_time(false);

    if(verbosity >= ::Options::Informative)
      ::std::cout << "TMCNF: CNF generation time: " << static_cast<double>(gn_end_time-gn_start_time)/1000000.0 << ::std::endl;

    //printCNF(cnf);

    if(add_roots) {
      // add outputs
      unsigned clause = cnf.size();
      for(std::vector< ::Opt::NodeRef>::iterator i = outrefs.begin(); i != outrefs.end(); ++i, ++clause) {
        cnf.resize(cnf.size()+1);
        cnf[clause].push_back(*i);
      }
    }

    
    if(verbosity >= ::Options::Informative) {
      for(unsigned z = 0; z < cf.cut_size.size(); ++z) {
        ::std::cout << "TMCNF: Number of cuts size " << (z+1) << ": " << cf.cut_size[z] << ::std::endl;
      }
    }
  }

    
  void techMap(Options::Verbosity verbosity, const ::AIGAttachment& aigat, unsigned k, unsigned b, unsigned refinements, ::std::vector<ID>& outputs, ::Expr::Manager::View& v, ::std::vector< ::std::vector<ID> >& cnf, ::std::vector<ID>& roots, double timeOut, bool add_roots)
  {
    // convert outputs into AIG references
    ::std::vector< ::Opt::NodeRef> aig_outputs;
    for(unsigned outi = 0; outi < outputs.size(); ++outi) {
      ::Opt::IDRefMap::const_iterator fit = aigat.id2ref.find(outputs[outi]);
      assert(fit != aigat.id2ref.end());
      aig_outputs.push_back(fit->second);
    }

    // make roots match the size of outputs
    roots.resize(aig_outputs.size());

    // a place for AIG CNF
    ::std::vector< ::std::vector< ::Opt::NodeRef> > nrcnf;

    // do CNF generation
    techMap(verbosity, aigat, k, b, refinements, aig_outputs, nrcnf, timeOut, add_roots);

    // convert AIG CNF to Expr CNF
    typedef ::std::vector< ::std::vector< ::Opt::NodeRef> > aigcnf;
    std::map< ::Opt::NodeIndex, ID> newvars;
    cnf.resize(0);
    unsigned clause = 0;
    for(aigcnf::iterator i = nrcnf.begin(); i != nrcnf.end(); ++i, ++clause) {
      cnf.resize(cnf.size()+1);
      for(::std::vector< ::Opt::NodeRef>::iterator j = i->begin(); j != i->end(); ++j) {
        ID lit;
        if(*j == 0) {
          // map to false
          lit =  v.bfalse();
        } else if(*j == 1) {
          // map to true
          lit = v.btrue();
        } else if(aigat.aig[ ::Opt::indexOf(*j)].isVar()) {
          // use existing inputs
          lit = aigat.ref2id.find(::Opt::refOf(::Opt::indexOf(*j), false))->second;
          if(::Opt::isNot(*j)) {
            // negate them if necessary
            lit = v.apply(::Expr::Not, lit);
          }
        } else {
          std::map< ::Opt::NodeIndex, ID>::iterator fj = newvars.find(::Opt::indexOf(*j));
          if(fj == newvars.end()) {
            // create new variable
            ::std::stringstream s;
            s << "tmv" << *j;
            lit = v.newVar(s.str());
            newvars[::Opt::indexOf(*j)] = lit;
          } else {
            // use existing var
            lit = fj->second;
          }
          if(::Opt::isNot(*j)) {
            lit = v.apply(::Expr::Not, lit);
          }
        }

        cnf[clause].push_back(lit);
      }
    }

    // fill in the roots vector
    unsigned j = 0;
    for(::std::vector< ::Opt::NodeRef>::iterator i = aig_outputs.begin(); i != aig_outputs.end(); ++i,++j) {
      if(*i == 0) {
        // map to false
        roots[j] = v.bfalse();
      } else if(*i == 1) {
        // map to true
        roots[j] = v.btrue();
      } else if(aigat.aig[ ::Opt::indexOf(*i)].isVar()) {
        // use existing input
        roots[j] = aigat.ref2id.find(::Opt::refOf(::Opt::indexOf(*i), false))->second;
        if(::Opt::isNot(*i)) {
          // negate as necessary
          roots[j] = v.apply(::Expr::Not, roots[j]);
        }
      } else {
        // use existing map
        std::map< ::Opt::NodeIndex, ID>::iterator fi = newvars.find(::Opt::indexOf(*i));
        // it should be found
        assert(fi != newvars.end());
        roots[j] = fi->second;
        if(::Opt::isNot(*i)) {
          // negate as necessary
          roots[j] = v.apply(::Expr::Not, roots[j]);
        }
      }
    }
  }
} // namespace CNF


