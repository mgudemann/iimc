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

#ifndef _ExprAttachment_
#define _ExprAttachment_

/** @file ExprAttachment.h */

//#include <ostream>
#include "AIGAttachment.h"
#include "Model.h"

/**
 * Expression attachment.
 *
 * This is a tuple of sets of expressions describing input, output, and
 * state variables, as well as next-state and output functions, initial
 * conditions and constraints.
 */
class ExprAttachment : public Model::Attachment {
public:
  ExprAttachment(Model& model) : Model::Attachment(model) {
    AIGAttachment::Factory f;
    prefer(Key::AIG, &f);
    toNothing();
  }
  ExprAttachment(const ExprAttachment& from);
  ExprAttachment& operator=(ExprAttachment& rhs);
  ~ExprAttachment() {}

  /** Return the key of this type of attachment. */
  Key::Type key() const { return Key::EXPR; }
  /** Build the model when necessary. */
  void build();

  /** Add an input variable to the model. */
  void addInput(const ID);
  /** Add input variables to the model. */
  void addInputs(const std::vector<ID>&);
  /** Discard the current inputs of the model. */
  void clearInputs();
  /** Add a state variable and its update function to the model. */
  void setNextStateFn(const ID, const ID);
  /** Add state variables and their update functions to the model. */
  void setNextStateFns(const std::vector<ID>&, const std::vector<ID>&);
  /** Discard the current next state functions of the model. */
  void clearNextStateFns();
  /** Add an output variable and its defining function to the model. */
  void setOutputFn(const ID, const ID);
  /** Add output variables and their defining functions to the model. */
  void setOutputFns(const std::vector<ID>&, const std::vector<ID>&);
  /** Discard the current output functions of the model. */
  void clearOutputFns();
  /**
   * Add one expression to the list of initial conditions.
   *
   * The expression must be a function of the state variables.
   */
  void addInitialCondition(const ID);
  /**
   * Add expressions to the list of initial conditions.
   *
   * The expressions must be functions of the state variables.
   */
  void addInitialConditions(const std::vector<ID>&);
  /** Discard the current initial conditions of the model. */
  void clearInitialConditions();
  /** Add one expression to the list of constraints. */
  void addConstraint(const ID);
  /** Add expressions to the list of constraints. */
  void addConstraints(const std::vector<ID>&);
  /** Discard the current relational constraints of the model. */
  void clearConstraints();
  /** Add bad variable and its defining function to the model. */
  void setBadFn(const ID, const ID);
  /** Add bad variables and their defining functions to the model. */
  void setBadFns(const std::vector<ID>&, const std::vector<ID>&);
  /** Discard the current bad assertions. */
  void clearBadFns();
  /** Add Buechi fairness variable and its defining function to the model. */
  void setFairnessFn(const ID, const ID);
  /** Add Buechi fairness variables and their defining function to the model. */
  void setFairnessFns(const std::vector<ID>&, const std::vector<ID>&);
  /** Discard the current Buechi constraints of the model. */
  void clearFairnessFns();
  /** Deprecated */
  void addFairnessConstraint(const ID);
  void clearFairnessConstraints() { clearFairnessFns(); }
  /** Add one justice set. */
  void setJusticeSet(const ID, const std::vector<ID> &);
  /** Discard the current justice constraints of the model. */
  void clearJusticeSets();
  /** Add one CTL property */
  void addCtlProperty(const ID);
  /** Add CTL properties */
  void addCtlProperties(const std::vector<ID> &);
  /** Discard the current CTL properties of the model. */
  void clearCtlProperties();
  /** Return a vector with the input variables of the model. */
  const std::vector<ID>& inputs() const { return _inputs; }
  /** Return a vector with the state variables of the model. */
  const std::vector<ID>& stateVars() const { return _state_vars; }
  /** Return a vector with the next state functionss of the model. */
  const std::vector<ID>& nextStateFns() const { return _next_state_fns; }
  /** Return a vector with the output variables of the model. */
  const std::vector<ID>& outputs() const { return _outputs; }
  /** Return a vector with the output variables of the model. */
  const std::vector<ID>& outputFns() const { return _output_fns; }
  /** Return a vector with the bad variables of the model. */
  const std::vector<ID>& bad() const { return _bad; }
  /** Return a vector with the bad functions of the model. */
  const std::vector<ID>& badFns() const { return _bad_fns; }
  /** Return a vector with the fairness variables of the model. */
  const std::vector<ID>& fairness() const { return _fairness; }
  /** Return a vector with the fairness functions of the model. */
  const std::vector<ID>& fairnessFns() const { return _fairness_fns; }
  /** Return a vector with the justice variables of the model. */
  const std::vector<ID>& justice() const { return _justice; }
  /** Return a vector with the justice sets of the model. */
  const std::vector< std::vector<ID> >& justiceSets() const { return _justice_fn_sets; }
  /** Return a vector with the initial conditions of the model. */
  const std::vector<ID>& initialConditions() const { return _initial_cond; }
  /** Return a vector with the constraints on the transition relation. */
  const std::vector<ID>& constraints() const { return _constraints; }
  /** Return a vector with the fairness constraints of the model. */
  ID nextStateFnOf(const ID varId) const;
  /** Vectorized "nextStateFnOf(ID)". */
  std::vector<ID> nextStateFnOf(const std::vector<ID>&) const;
  /** Look up the function associated with the given output variable. */
  ID outputFnOf(const ID varId) const;
  /** Vectorized "outputFnOf(ID)". */
  std::vector<ID> outputFnOf(const std::vector<ID>&) const;
  /** Look up the function associated with the given bad variable. */
  ID badFnOf(const ID varId) const;
  /** Vectorized "badFnOf(ID)". */
  std::vector<ID> badFnOf(const std::vector<ID>&) const;
  /** Look up the function associated with the given Buechi fairness variable. */
  ID fairnessFnOf(const ID varId) const;
  /** Vectorized "fairnessFnOf(ID)". */
  std::vector<ID> fairnessFnOf(const std::vector<ID>&) const;
  /** Deprecated */
  std::vector<ID> fairnessConstraints() const;
  /** Look up the function associated with the given justice variable. */
  const std::vector<ID> & justiceSetOf(const ID varId) const;
  /** Return a vector with the CTL properties. */
  const std::vector<ID>& ctlProperties() const { return _ctl_properties; }
  /** True if id is an input, output, or state variable of the model. */
  bool isVariable(const ID id) const;
  /** True if id is an input of the model. */
  bool isInput(const ID id) const;
  /** True if id is an output of the model. */
  bool isOutput(const ID id) const;
  /** True if id is a "bad" output. */
  bool isBad(const ID id) const;
  /** True if id is a "fairness" output. */
  bool isFairness(const ID id) const;
  /** True if id corresponds to a set of "justice" outputs. */
  bool isJusticeSet(const ID id) const;
  /** True if id is a state variable of the model. */
  bool isStateVar(const ID id) const;
  /** Mark as "keepers" all the expressions in the model. */
  void keep(Expr::Manager::View *) const;
  /** Promote all the expressions of the model to the global context. */
  void global(Expr::Manager::View *);
  /** Construct a string from a model. */
  std::string string(bool includeDetails = false) const;
  /** Describes a model in dot format. */
  std::string dot(bool terse = true) const;
  /** Describes a model's circuit graph in dot format. */
  std::string circuitGraph(bool terse = true) const;
  /** Describes a model in Verilog. */
  std::string verilog() const;
  /** Describes a model in Blif-MV. */
  std::string blifMv() const;
  /** Output status information of a model **/
  void info() const;

  class Factory : public Model::AttachmentFactory {
  public:
    virtual ExprAttachment * operator()(Model & model) {
      return new ExprAttachment(model);
    }
  };

protected:
  ExprAttachment* clone() const { return new ExprAttachment(*this); }
private:
  typedef std::vector<ID> mod_vec;
  typedef mod_vec::iterator v_iter;
  typedef mod_vec::const_iterator const_v_iter;
  typedef mod_vec::size_type v_size;
  typedef std::unordered_map<ID, v_size> mod_map;
  typedef mod_map::iterator m_iter;
  typedef mod_map::const_iterator const_m_iter;
  typedef std::vector< std::vector<ID> > mod_vec_vec;

  void addOrUpdate(const ID vid, const ID fid, mod_vec& vvec, mod_vec& fvec, mod_map& var_to_fn);
  void addOrUpdate(const mod_vec& vids, const mod_vec& fids,
                   mod_vec& vvec, mod_vec& fvec, mod_map& var_to_fn);
  bool isVarWithType(const ID id, const mod_vec& vm, const mod_map& vtf) const;

  mod_vec _inputs;
  mod_vec _state_vars;
  mod_vec _next_state_fns;
  mod_vec _outputs;
  mod_vec _output_fns;
  mod_vec _initial_cond;
  mod_vec _constraints;
  mod_vec _bad;
  mod_vec _bad_fns;
  mod_vec _fairness;
  mod_vec _fairness_fns;
  mod_vec _justice;
  mod_vec_vec _justice_fn_sets;
  mod_vec _ctl_properties;
  mod_map _input_var_to_fn;
  mod_map _state_var_to_fn;
  mod_map _output_var_to_fn;
  mod_map _bad_var_to_fn;
  mod_map _constraint_var_to_fn;
  mod_map _justice_var_to_fn_set;
  mod_map _fairness_var_to_fn;
};

#endif // _ExprAttachment_
