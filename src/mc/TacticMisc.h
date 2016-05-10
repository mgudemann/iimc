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

#ifndef _TacticMisc_
#define _TacticMisc_

/** @file TacticMisc.h */

#include "Model.h"
#include "ExprAttachment.h"
#include "Util.h"

typedef boost::program_options::variables_map options_map;
/**
 * Action to print the expressions for a model.
 */
class PrintExprAction : public Model::Action {
public:
  /**
   * Constructor used in initialization.
   */
  PrintExprAction(Model & m) : Model::Action(m) {
    ExprAttachment::Factory f;
    requires(Key::EXPR, &f);
  }
  /**
   * Print expressions.
   */
  virtual void exec() {
    std::cout << model().string();
  }
};

/**
 * Action to print a dot file for a model.
 */
class PrintDotAction : public Model::Action {
public:
  /**
   * Constructor used in initialization.
   */
  PrintDotAction(Model & m) : Model::Action(m) {
    ExprAttachment::Factory f;
    requires(Key::EXPR, &f);
  }
  /**
   * Print dot.
   */
  virtual void exec() {
    std::cout << model().dot();
  }
};

/**
 * Class to print the circuit graph in dot format.
 */
class PrintCircuitGraphAction : public Model::Action {
public:
  /**
   * Constructor used in initialization.
   */
  PrintCircuitGraphAction(Model & m) : Model::Action(m) {
    ExprAttachment::Factory f;
    requires(Key::EXPR, &f);
  }
  /**
   * Print circuit graph in dot format.
   */
  virtual void exec() {
    ExprAttachment const *eat = 
      (ExprAttachment const *) _model.constAttachment(Key::EXPR);
    assert(eat != 0);
    std::cout << eat->circuitGraph();
    _model.constRelease(eat);
  }
};


/**
 * Action to print a Verilog module for a model.
 */
class PrintVerilogAction : public Model::Action {
public:
  /**
   * Constructor used in initialization.
   */
  PrintVerilogAction(Model & m) : Model::Action(m) {
    ExprAttachment::Factory f;
    requires(Key::EXPR, &f);
  }
  /**
   * Print model.
   */
  virtual void exec() {
    std::cout << model().verilog();
  }
};

/**
 * Action to print Blif-MV for a model.
 */
class PrintBlifMvAction : public Model::Action {
public:
  /**
   * Constructor used in initialization.
   */
  PrintBlifMvAction(Model & m) : Model::Action(m) {
    ExprAttachment::Factory f;
    requires(Key::EXPR, &f);
  }
  /**
   * Print expressions.
   */
  virtual void exec() {
    std::cout << model().blifMv();
  }
};

/**
 * Action to print system information.
 */
class PrintSystemInfoAction : public Model::Action {
public:
  PrintSystemInfoAction(Model & m) : Model::Action(m) {}
  /**
   * Print system info.
   */
  virtual void exec() {
    Util::printSystemInfo();
  }
};

/**
 * Action to print CPU time.
 */
class PrintCpuTimeAction : public Model::Action {
public:
  PrintCpuTimeAction(Model & m) : Model::Action(m) {}
  /**
   * Print CPU time.
   */
  virtual void exec() {
    Util::printCpuTime();
  }
};


/**
 * Action to print conclusions.
 */
class Conclusion : public Model::Action {
public:
  Conclusion(Model & m) : Model::Action(m) {
    ProofAttachment::Factory f;
    requires(Key::PROOF, &f);
  }
  /**
   * Do nothing.  
   *
   * The whole point of this action is to instantiate the proof attachment.
   */
  virtual void exec() {}
};

/**
 * Action to analyze SCCs in the COI of primary outputs.
 */
class AnalyzeSccs : public Model::Action {
public:
  AnalyzeSccs(Model & m) : Model::Action(m) {
    ExprAttachment::Factory f;
    requires(Key::EXPR, &f);
  }
  /**
   * Analyze SCCs.
   */
  virtual void exec() {
    Expr::Manager::View *v = model().newView();
    ExprAttachment const *eat = 
      (ExprAttachment const *) model().constAttachment(Key::EXPR);
    std::vector<ID> const &nsfv = eat->nextStateFns();
    std::vector<ID> const &roots = eat->outputFns();
    std::vector<ID> const &leaves = eat->stateVars();
    analyzeSccs(*v, roots, leaves, nsfv);
    model().constRelease(eat);
    delete v;
  }
};

/**
 * Action to print quotient graph for the circuit SCCs in the COI of primary
 * outputs in dot format
 */
class PrintCircuitSccGraph : public Model::Action {
public:
  PrintCircuitSccGraph(Model & m) : Model::Action(m) {
    ExprAttachment::Factory f;
    requires(Key::EXPR, &f);
  }
  /**
   * Print circuit SCCs
   */
  virtual void exec() {
    Expr::Manager::View *v = model().newView();
    ExprAttachment const *eat = 
      (ExprAttachment const *) model().constAttachment(Key::EXPR);
    std::vector<ID> const &nsfv = eat->nextStateFns();
    std::vector<ID> const &roots = eat->outputFns();
    std::vector<ID> const &leaves = eat->stateVars();
    std::cout << printSccQuotientGraph(*v, roots, leaves, nsfv);
    model().constRelease(eat);
    delete v;
  }
};

/**
 * Action to print out the status info of an Expr attachment, such as
 * the max/min/average length of combinational paths
 */
class PrintExprInfo : public Model::Action {
public:
  PrintExprInfo(Model & m) : Model::Action(m)
  {
    ExprAttachment::Factory eaf;
    requires(Key::EXPR, &eaf);
  }
  virtual void exec()
  {
    ExprAttachment const *eat = (ExprAttachment *)model().constAttachment(Key::EXPR);
    eat->info();
    model().constRelease(eat);
  }
};

class PrintExprSize : public Model::Action {
public:
  PrintExprSize(Model & m) : Model::Action(m) {
    ExprAttachment::Factory f;
    requires(Key::EXPR, &f);
  }

  virtual void exec() {
    ExprAttachment const * const eat =
      (ExprAttachment const *) model().constAttachment(Key::EXPR);

    std::vector<ID> ids = eat->nextStateFns();
    ids.insert(ids.end(), eat->outputFns().begin(), eat->outputFns().end());
    ids.insert(ids.end(), eat->badFns().begin(), eat->badFns().end());
    ids.insert(ids.end(), eat->constraints().begin(), eat->constraints().end());
    for(vector< vector<ID> >::const_iterator it = eat->justiceSets().begin();
        it != eat->justiceSets().end(); ++it) {
      ids.insert(ids.end(), it->begin(), it->end());
    }
    ids.insert(ids.end(), eat->fairnessFns().begin(), eat->fairnessFns().end());

    Expr::Manager::View *v = model().newView();
    std::cout << "Model has " << sizeOf(*v, ids) << " nodes" << std::endl;

    delete v;
  }
};

#endif // _TacticMisc_
