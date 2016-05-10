/* -*- C++ -*- */

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

#ifndef _TacticMisc_
#define _TacticMisc_

/** @file TacticMisc.h */

#include <boost/dynamic_bitset.hpp>

#include "Model.h"
#include "options.h"
#include "ExprAttachment.h"
#include "ProofAttachment.h"
#include "Util.h"

#include <cmath>

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
  void exec() {
    std::cout << model().string();
  }
private:
  static ActionRegistrar action;
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
  void exec() {
    std::cout << model().dot();
  }
private:
  static ActionRegistrar action;
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
  void exec() {
    ExprAttachment const * const eat = 
      (ExprAttachment const *) _model.constAttachment(Key::EXPR);
    assert(eat != 0);
    std::cout << eat->circuitGraph();
    _model.constRelease(eat);
  }
private:
  static ActionRegistrar action;
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
  void exec() {
    std::cout << model().verilog();
  }
private:
  static ActionRegistrar action;
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
  void exec() {
    std::cout << model().blifMv();
  }
private:
  static ActionRegistrar action;
};


/**
 * Action to print AIGER for a model.
 */
class PrintAIGERAction : public Model::Action {
public:
  /**
   * Constructor used in initialization.
   */
  PrintAIGERAction(Model & m) : Model::Action(m) {
    ExprAttachment::Factory ef;
    requires(Key::EXPR, &ef);
  }
  /**
   * Print AIGER.
   */
  void exec() {
    try {
      std::string filename;
      if (_model.options().count("aiger_output") > 0)
        filename =  _model.options()["aiger_output"].as<std::string>();
      else
        filename = "test.aig";
      model().AIGER(filename);
    } catch (std::runtime_error const & e) {
      std::cout << "print_aiger failed: " << e.what() << std::endl;
    }
  }
private:
  static ActionRegistrar action;
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
  void exec() {
    Util::printSystemInfo();
  }
private:
  static ActionRegistrar action;
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
  void exec() {
    Util::printCpuTime();
  }
private:
  static ActionRegistrar action;
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
  void exec() {}
private:
  static ActionRegistrar action;
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
  void exec();
private:
  static ActionRegistrar action;
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
  void exec();
private:
  static ActionRegistrar action;
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
  void exec()
  {
    ExprAttachment const * const eat = (ExprAttachment const *)model().constAttachment(Key::EXPR);
    eat->info();
    model().constRelease(eat);
  }
private:
  static ActionRegistrar action;
};


/**
 * Action to print the number of nodes in the expressions of a model
 */
class PrintExprSize : public Model::Action {
public:
  PrintExprSize(Model & m) : Model::Action(m) {
    ExprAttachment::Factory f;
    requires(Key::EXPR, &f);
  }

  void exec();
private:
  static ActionRegistrar action;
};


/**
 * Action to print the expressions that define the outputs
 */
class PrintOutputExpressions : public Model::Action {
public:
  PrintOutputExpressions(Model & m) : Model::Action(m) {
    ExprAttachment::Factory f;
    requires(Key::EXPR, &f);
  }

  void exec();
private:
  static ActionRegistrar action;
};


/**
 * Action to print a dot file describing the state graph of the model
 * (if it is small enough)
 */
class PrintStateGraph : public Model::Action {
public:
  PrintStateGraph(Model & m) : Model::Action(m) {
    ExprAttachment::Factory f;
    requires(Key::EXPR, &f);
  }

  void exec();
private:
  static ActionRegistrar action;
};

#endif // _TacticMisc_
