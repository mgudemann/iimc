/* -*- C++ -*- */

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

#ifndef _IC3_
#define _IC3_

/** @file IC3.h **/

#include "BddAttachment.h"
#include "CNFAttachment.h"
#include "COI.h"
#include "ExprAttachment.h"
#include "MC.h"
#include "Model.h"
#include "ProofAttachment.h"
#include "RchAttachment.h"
#include "SAT.h"

#include <boost/program_options.hpp>

/** namespace of IC3 */
namespace IC3 {

  enum ProofProcType {NONE, STRENGTHEN, WEAKEN, SHRINK};

  inline bool _IDVectorComp(const std::vector<ID> & v1, const std::vector<ID> & v2) {
    std::vector<ID>::const_iterator it1 = v1.begin(), it2 = v2.begin();
    for (; it1 != v1.end() && it2 != v2.end(); ++it1, ++it2) {
      if (*it1 < *it2) return true;
      if (*it1 > *it2) return false;
    }
    return (it1 == v1.end() && it2 != v2.end());
  }

  class IDVectorComp {
  public:
    bool operator()(const std::vector<ID> & v1, const std::vector<ID> & v2) {
      return _IDVectorComp(v1, v2);
    }
  };
  typedef std::set<std::vector<ID>, IDVectorComp> CubeSet;

  struct LevClauses {
  public:
    LevClauses(int _level, std::vector< std::vector<ID> > _clauses) :
        level(_level), clauses(_clauses) {}
    int level;
    std::vector< std::vector<ID> > clauses;
  };

  struct IC3Options {
  public:
    IC3Options(const boost::program_options::variables_map & opts, bool _rev = false) {
      reverse = _rev;
      timeout = _rev ? opts["ic3r_timeout"].as<int>() : opts["ic3_timeout"].as<int>();
      eqprop = opts.count("ic3_xeqprop") == 0;
      xeq = opts.count("ic3_aeq");
      nRuns = opts["ic3_nRuns"].as<unsigned int>();
      ecSz = opts["ic3_ms"].as<unsigned int>();
      bddInit = opts.count("ic3_xbddInit") == 0;
      cycle = false;
      bmcsz = false;
      proofProc = STRENGTHEN;
      printCex = opts.count("print_cex");
      printProof = opts.count("print_proof");
      constraints = NULL;
      sccH = opts.count("ic3_sccH") == 1;
      iictl = false;
      silent = false;
      incremental = false;
      propagate = false;
      lift = opts.count("ic3_lift");
      lift_aggr = opts["ic3_laggr"].as<int>();
      inf = opts.count("ic3_inf");
      inf_weak = opts.count("ic3_weak_inf");
      try_unlifted = opts.count("ic3_try_unlifted");
      stats = opts.count("ic3_stats");
      initCube = NULL;
    }
    bool reverse;
    int timeout;
    bool eqprop;
    bool xeq;
    unsigned int nRuns;
    unsigned int ecSz;
    bool bddInit;
    bool cycle;
    bool bmcsz;
    ProofProcType proofProc;
    bool printCex;
    bool printProof;
    std::vector<SAT::Clauses> * constraints;
    bool sccH;
    bool iictl;
    SAT::Clauses * iictl_clauses;
    bool silent;
    bool incremental;
    bool propagate;
    bool lift;
    int lift_aggr;
    bool inf;
    bool inf_weak;
    bool try_unlifted;
    bool stats;
    std::vector<ID> * initCube;
  };

  MC::ReturnValue check(Model & m, IC3Options & opts,
                        std::vector<Transition> * cex = NULL,
                        std::vector< std::vector<ID> > * proofCNF = NULL,
                        std::vector<ID> * gprop = NULL,
                        std::vector<CubeSet> * cubes = NULL,
                        std::vector<LevClauses> * propClauses = NULL,
                        CubeSet * indCubes = NULL,
                        bool useRAT = true,
                        bool * bmcProof = NULL);

  MC::ReturnValue reach(Model & m, IC3Options & opts,
                        std::vector< std::vector< std::vector<ID> > > & proofs,
                        std::vector<Transition> * cex = NULL);

  MC::ReturnValue reach2(Model & m, IC3Options & opts,
                         std::vector<Transition> * cex = NULL,
                         std::vector< std::vector< std::vector<ID> > > * proofs = NULL,
                         std::vector<CubeSet> * cubes = NULL,
                         std::vector<LevClauses> * propClauses = NULL,
                         CubeSet * indCubes = NULL);
  
  bool mic(Model & m, IC3Options & opts, std::vector<ID> & cube);

  void postProcessProof(Model & m, std::vector< std::vector<ID> > & proof,
      ProofProcType type, IC3Options & opts, std::vector<ID> * gprop = NULL);

  class IC3Action : public Model::Action {
  public:
    IC3Action(Model & m, bool reverse = false) : Model::Action(m), reverse(reverse) {
      ExprAttachment::Factory eaf;
      requires(Key::EXPR, &eaf);
      COIAttachment::Factory caf;
      requires(Key::COI, &caf);
      RchAttachment::Factory raf;
      requires(Key::RCH, &raf);
      BddAttachment::Factory baf;
      prefer(Key::BDD, &baf);
      toNothing();
      AIGAttachment::Factory aaf;
      if (!m.options().count("ic3_xeqprop")) requires(Key::AIG, &aaf);
      ProofAttachment::Factory paf;
      requires(Key::PROOF, &paf);
      CNFAttachment::Factory cnfaf;
      requires(Key::CNF, &cnfaf);
    }
    virtual void exec() {
      IC3Options opts(options(), reverse);
      MC::ReturnValue rv;
      std::vector<Transition> cex;
      std::vector< std::vector<ID> > proof;
      rv = check(model(), opts, opts.printCex ? &cex : NULL,
          opts.printProof ? &proof : NULL);
      ProofAttachment * pat = (ProofAttachment *) model().attachment(Key::PROOF);
      if (rv.returnType != MC::Unknown) {
        if (rv.returnType == MC::Proof) {
          pat->setConclusion(0);
          if(opts.printProof) {
            if(options().count("improve_proof")) {
              int t = options()["improve_proof"].as<int>();
              ProofProcType type = t == 0 ? STRENGTHEN : t == 1 ? WEAKEN : SHRINK;
              postProcessProof(model(), proof, type, opts);
            }
            pat->setProof(proof);
          }
        }
        else if (rv.returnType == MC::CEX) {
          pat->setConclusion(1);
          if(opts.printCex) {
            pat->setCex(cex);
          }
        }
      }
      model().release(pat);
    }
  private:
    bool reverse;
  };

}

#endif
