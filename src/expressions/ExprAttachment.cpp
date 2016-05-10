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

#include "ExprUtil.h"
#include "ExprVerilog.h"
#include "ExprAttachment.h"
#include "AIGER.h"
#include "options.h"

using namespace std;

/** Copy constructor. */
ExprAttachment::ExprAttachment(const ExprAttachment& from) : 
  Model::Attachment(from),
  _inputs(from._inputs),
  _aut_state_vars(from._aut_state_vars),
  _state_vars(from._state_vars),
  _next_state_fns(from._next_state_fns),
  _outputs(from._outputs),
  _output_fns(from._output_fns),
  _initial_cond(from._initial_cond),
  _constraints(from._constraints),
  _constraint_fns(from._constraint_fns),
  _bad(from._bad),
  _bad_fns(from._bad_fns),
  _fairness(from._fairness),
  _fairness_fns(from._fairness_fns),
  _justice(from._justice),
  _justice_fn_sets(from._justice_fn_sets),
  _input_var_to_fn(from._input_var_to_fn),
  _state_var_to_fn(from._state_var_to_fn),
  _output_var_to_fn(from._output_var_to_fn),
  _bad_var_to_fn(from._bad_var_to_fn),
  _constraint_var_to_fn(from._constraint_var_to_fn),
  _justice_var_to_fn_set(from._justice_var_to_fn_set),
  _fairness_var_to_fn(from._fairness_var_to_fn) {}

ExprAttachment& ExprAttachment::operator=(ExprAttachment& rhs) {
  if (&rhs != this) {
    _model = rhs._model;
    if (rhs._ts == 0)
      _ts = 0;
    else
      _ts = Model::newTimestamp();
    _inputs = rhs._inputs;
    _aut_state_vars = rhs._aut_state_vars;
    _state_vars = rhs._state_vars;
    _next_state_fns = rhs._next_state_fns;
    _outputs = rhs._outputs;
    _output_fns = rhs._output_fns;
    _initial_cond = rhs._initial_cond;
    _constraints = rhs._constraints;
    _constraint_fns = rhs._constraint_fns;
    _bad = rhs._bad;
    _bad_fns = rhs._bad_fns;
    _fairness = rhs._fairness;
    _fairness_fns = rhs._fairness_fns;
    _justice = rhs._justice;
    _justice_fn_sets = rhs._justice_fn_sets;
    _input_var_to_fn = rhs._input_var_to_fn;
    _state_var_to_fn = rhs._state_var_to_fn;
    _output_var_to_fn = rhs._output_var_to_fn;
    _bad_var_to_fn = rhs._bad_var_to_fn;
    _constraint_var_to_fn = rhs._constraint_var_to_fn;
    _justice_var_to_fn_set = rhs._justice_var_to_fn_set;
    _fairness_var_to_fn = rhs._fairness_var_to_fn;
  }
  return *this;
}

void ExprAttachment::build() {
  if (model().verbosity() > Options::Silent)
    cout << "ExprAttachment: building ";
  AIGAttachment * const aat = (AIGAttachment *) model().constAttachment(Key::AIG);
  if (aat != 0 && !aat->empty()) {
    if (model().verbosity() > Options::Silent)
      cout << "from AIG" << endl;
    // do something snazzy, namely, call AIG2Expr
    aat->AIG2Expr();
  }
  else {
    if (model().verbosity() > Options::Silent)
      cout << "from file" << endl;
    assert(options().count("input-file"));
    std::string inputFile = options()["input-file"].as<std::string>();
    Parser::parseAIGER(inputFile, model());
  }
  if (aat != 0) model().constRelease(aat);
}

void ExprAttachment::addOrUpdate(const ID vid, const ID fid, mod_vec& vvec, mod_vec& fvec, mod_map& var_to_fn)
{
  m_iter i = var_to_fn.find(vid);
  if (i == var_to_fn.end()) {
    var_to_fn[vid] = vvec.size();
    vvec.push_back(vid);
    fvec.push_back(fid);
  } else {
    vvec[i->second] = vid;
    fvec[i->second] = fid;
  }
}

void ExprAttachment::addOrUpdate(const mod_vec& vids, const mod_vec& fids,
                                 mod_vec& vvec, mod_vec& fvec,
                                 mod_map& var_to_fn)
{
  assert(vids.size() == fids.size()); // check interface contract
  assert(vvec.size() == fvec.size()); // check internal consistency
  vvec.reserve(vvec.size()+vids.size());
  fvec.reserve(fvec.size()+fids.size());
  for (v_size i = 0; i != vids.size(); ++i)
    addOrUpdate(vids[i], fids[i], vvec, fvec, var_to_fn);
}

void ExprAttachment::addInput(const ID inputId)
{
  _input_var_to_fn[inputId] = _inputs.size();
  _inputs.push_back(inputId);
}

void ExprAttachment::addInputs(const mod_vec& inputVec)
{
  _inputs.reserve(_inputs.size()+inputVec.size());
  for (const_v_iter i = inputVec.begin(); i != inputVec.end(); ++i) {
    _input_var_to_fn[*i] = _inputs.size();
    _inputs.push_back(*i);
  }
}

void ExprAttachment::clearInputs()
{
  for (const_v_iter i = _inputs.begin(); i != _inputs.end(); ++i)
    _input_var_to_fn.erase(*i);
  _inputs.clear();
}

void ExprAttachment::addAutStateVar(const ID stateVarId)
{
  //Make sure state variable exists
  const_m_iter iter = _state_var_to_fn.find(stateVarId);
  assert(iter != _state_var_to_fn.end());
  _aut_state_var_to_fn[stateVarId] = _aut_state_vars.size();
  _aut_state_vars.push_back(stateVarId);
}

void ExprAttachment::addAutStateVars(const mod_vec& stateVarVec)
{
  _aut_state_vars.reserve(_aut_state_vars.size()+stateVarVec.size());
  for (const_v_iter i = stateVarVec.begin(); i != stateVarVec.end(); ++i)
    addAutStateVar(*i);
}

void ExprAttachment::clearAutStateVars()
{
  for (const_v_iter i = _aut_state_vars.begin(); i != _aut_state_vars.end(); ++i)
    _aut_state_var_to_fn.erase(*i);
  _aut_state_vars.clear();
}


void ExprAttachment::setNextStateFn(const ID varId, const ID fnId)
{
  addOrUpdate(varId, fnId, _state_vars, _next_state_fns, _state_var_to_fn);
}

void ExprAttachment::setNextStateFns(const mod_vec& varVec, const mod_vec& fnVec)
{
  addOrUpdate(varVec, fnVec, _state_vars, _next_state_fns, _state_var_to_fn);
}

void ExprAttachment::clearNextStateFns()
{
  for (v_size i = 0; i != _state_vars.size(); ++i)
    _state_var_to_fn.erase(_state_vars[i]);
  _state_vars.clear();
  _next_state_fns.clear();
}

void ExprAttachment::setOutputFn(const ID varId, const ID fnId)
{
  addOrUpdate(varId, fnId, _outputs, _output_fns, _output_var_to_fn);
}

void ExprAttachment::setOutputFns(const mod_vec& varVec, const mod_vec& fnVec)
{
  addOrUpdate(varVec, fnVec, _outputs, _output_fns, _output_var_to_fn);
}

void ExprAttachment::clearOutputFns()
{
  for (v_size i = 0; i != _outputs.size(); ++i)
    _output_var_to_fn.erase(_outputs[i]);
  _outputs.clear();
  _output_fns.clear();
}

void ExprAttachment::addInitialCondition(const ID initId)
{
  _initial_cond.push_back(initId);
}

void ExprAttachment::addInitialConditions(const mod_vec& initVec)
{
  _initial_cond.reserve(_initial_cond.size()+initVec.size());
  _initial_cond.insert(_initial_cond.end(),initVec.begin(),initVec.end());
}

void ExprAttachment::clearInitialConditions()
{
  _initial_cond.clear();
}

void ExprAttachment::addConstraint(const ID constrId, const ID fnId)
{
  addOrUpdate(constrId, fnId, _constraints, _constraint_fns, _constraint_var_to_fn);
}

void ExprAttachment::addConstraints(const mod_vec& constrVec, const mod_vec& fnVec)
{
  addOrUpdate(constrVec, fnVec, _constraints, _constraint_fns, _constraint_var_to_fn);
}

void ExprAttachment::clearConstraints()
{
  for (v_size i = 0; i != _constraints.size(); ++i)
    _constraint_var_to_fn.erase(_constraints[i]);
  _constraints.clear();
  _constraint_fns.clear();
}

void ExprAttachment::setBadFn(const ID varId, const ID fnId)
{
  addOrUpdate(varId, fnId, _bad, _bad_fns, _bad_var_to_fn);
}

void ExprAttachment::setBadFns(const mod_vec& varVec, const mod_vec& fnVec)
{
  addOrUpdate(varVec, fnVec, _bad, _bad_fns, _bad_var_to_fn);
}

void ExprAttachment::clearBadFns()
{
  for (v_size i = 0; i != _bad.size(); ++i)
    _bad_var_to_fn.erase(_bad[i]);
  _bad.clear();
  _bad_fns.clear();
}

void ExprAttachment::setFairnessFn(const ID varId, const ID fnId)
{
  addOrUpdate(varId, fnId, _fairness, _fairness_fns, _fairness_var_to_fn);
}

void ExprAttachment::setFairnessFns(const mod_vec& varVec, const mod_vec& fnVec)
{
  addOrUpdate(varVec, fnVec, _fairness, _fairness_fns, _fairness_var_to_fn);
}

void ExprAttachment::clearFairnessFns()
{
  for (v_size i = 0; i != _fairness.size(); ++i)
    _fairness_var_to_fn.erase(_fairness[i]);
  _fairness.clear();
  _fairness_fns.clear();
}

void ExprAttachment::addFairnessConstraint(const ID fnId) {
  // won't be indexable via fairnessFnOf
  addOrUpdate(0, fnId, _fairness, _fairness_fns, _fairness_var_to_fn);
}

void ExprAttachment::setJusticeSet(const ID varId, const mod_vec& fnIds)
{
  m_iter i = _justice_var_to_fn_set.find(varId);
  if (i == _justice_var_to_fn_set.end()) {
    _justice_var_to_fn_set[varId] = _justice.size();
    _justice.push_back(varId);
    _justice_fn_sets.push_back(fnIds);
  } else {
    _justice[i->second] = varId;
    _justice_fn_sets[i->second] = fnIds;
  }
}

void ExprAttachment::clearJusticeSets()
{
  for (v_size i = 0; i != _justice.size(); ++i)
    _justice_var_to_fn_set.erase(_justice[i]);
  _justice.clear();
  _justice_fn_sets.clear();
}

void ExprAttachment::addCtlProperty(const ID propId)
{
  _ctl_properties.push_back(propId);
}

void ExprAttachment::addCtlProperties(const mod_vec& propVec)
{
  _ctl_properties.reserve(_ctl_properties.size()+propVec.size());
  _ctl_properties.insert(_ctl_properties.end(),propVec.begin(),propVec.end());
}

void ExprAttachment::clearCtlProperties()
{
  _ctl_properties.clear();
}

void ExprAttachment::addAutomaton(const Automaton& automaton) {
  _automata.push_back(automaton);
}

void ExprAttachment::addAutomata(const vector<Automaton>& automata) {
  _automata.reserve(_automata.size()+automata.size());
  _automata.insert(_automata.end(),automata.begin(),automata.end());
}

void ExprAttachment::clearAutomata() {
  _automata.clear();
}

ID ExprAttachment::nextStateFnOf(const ID varId) const
{
  const_m_iter iter = _state_var_to_fn.find(varId);
  assert(iter != _state_var_to_fn.end());
  return _next_state_fns[iter->second];
}

vector<ID> ExprAttachment::nextStateFnOf(const mod_vec& ids) const
{
  mod_vec fns;
  for (const_v_iter i = ids.begin(); i != ids.end(); ++i)
    fns.push_back(nextStateFnOf(*i));
  return fns;
}

ID ExprAttachment::outputFnOf(const ID varId) const
{
  const_m_iter iter = _output_var_to_fn.find(varId);
  assert(iter != _output_var_to_fn.end());
  return _output_fns[iter->second];
}

vector<ID> ExprAttachment::outputFnOf(const mod_vec& ids) const
{
  mod_vec fns;
  for (const_v_iter i = ids.begin(); i != ids.end(); ++i)
    fns.push_back(outputFnOf(*i));
  return fns;
}

ID ExprAttachment::badFnOf(const ID varId) const
{
  const_m_iter iter = _bad_var_to_fn.find(varId);
  assert(iter != _bad_var_to_fn.end());
  return _bad_fns[iter->second];
}

vector<ID> ExprAttachment::badFnOf(const mod_vec& ids) const
{
  mod_vec fns;
  for (const_v_iter i = ids.begin(); i != ids.end(); ++i)
    fns.push_back(badFnOf(*i));
  return fns;
}

ID ExprAttachment::constraintFnOf(const ID varId) const
{
  const_m_iter iter = _constraint_var_to_fn.find(varId);
  assert(iter != _constraint_var_to_fn.end());
  return _constraint_fns[iter->second];
}

vector<ID> ExprAttachment::constraintFnOf(const mod_vec& ids) const
{
  mod_vec fns;
  for (const_v_iter i = ids.begin(); i != ids.end(); ++i)
    fns.push_back(constraintFnOf(*i));
  return fns;
}

ID ExprAttachment::fairnessFnOf(const ID varId) const
{
  const_m_iter iter = _fairness_var_to_fn.find(varId);
  assert(iter != _fairness_var_to_fn.end());
  return _fairness_fns[iter->second];
}

vector<ID> ExprAttachment::fairnessFnOf(const mod_vec& ids) const
{
  mod_vec fns;
  for (const_v_iter i = ids.begin(); i != ids.end(); ++i)
    fns.push_back(fairnessFnOf(*i));
  return fns;
}

vector<ID> ExprAttachment::fairnessConstraints() const
{
  return _fairness_fns;
}

const vector<ID> & ExprAttachment::justiceSetOf(const ID varId) const
{
  const_m_iter iter = _justice_var_to_fn_set.find(varId);
  assert(iter != _justice_var_to_fn_set.end());
  return _justice_fn_sets[iter->second];
}

bool ExprAttachment::isVariable(const ID id) const
{
  return (_input_var_to_fn.find(id) != _input_var_to_fn.end() ||
          _state_var_to_fn.find(id) != _state_var_to_fn.end() ||
          _output_var_to_fn.find(id) != _output_var_to_fn.end() ||
          _bad_var_to_fn.find(id) != _bad_var_to_fn.end() ||
          _constraint_var_to_fn.find(id) != _constraint_var_to_fn.end() ||
          _justice_var_to_fn_set.find(id) != _justice_var_to_fn_set.end() ||
          _fairness_var_to_fn.find(id) != _fairness_var_to_fn.end());
}

bool ExprAttachment::isVarWithType(const ID id, const mod_vec& v,
                                   const mod_map& var_to_fn) const
{
  const_m_iter iter = var_to_fn.find(id);
  return (iter != var_to_fn.end()) && (iter->second < v.size()) && (v[iter->second] == id);
}

bool ExprAttachment::isInput(const ID id) const
{
  return isVarWithType(id, _inputs, _input_var_to_fn);
}

bool ExprAttachment::isOutput(const ID id) const
{
  return isVarWithType(id, _outputs, _output_var_to_fn);
}

bool ExprAttachment::isStateVar(const ID id) const
{
  return isVarWithType(id, _state_vars, _state_var_to_fn);
}

bool ExprAttachment::isBad(const ID id) const
{
  return isVarWithType(id, _bad, _bad_var_to_fn);
}

bool ExprAttachment::isFairness(const ID id) const
{
  return isVarWithType(id, _fairness, _fairness_var_to_fn);
}

bool ExprAttachment::isJusticeSet(const ID id) const
{
  return isVarWithType(id, _justice, _justice_var_to_fn_set);
}

void  ExprAttachment::keep(Expr::Manager::View *v) const
{
  v->keep(_inputs);
  v->keep(_state_vars);
  v->keep(_outputs);
  v->keep(_output_fns);
  v->keep(_next_state_fns);
  v->keep(_initial_cond);
  v->keep(_constraint_fns);
  v->keep(_bad);
  v->keep(_bad_fns);
  v->keep(_fairness);
  v->keep(_fairness_fns);
  v->keep(_justice);
  for (v_size i = 0; i != _justice_fn_sets.size(); ++i)
    v->keep(_justice_fn_sets[i]);
}

void  ExprAttachment::global(Expr::Manager::View *v)
{
  v->global(_inputs);
  v->global(_state_vars);
  v->global(_outputs);
  v->global(_output_fns);
  v->global(_next_state_fns);
  v->global(_initial_cond);
  v->global(_constraint_fns);
  v->global(_bad);
  v->global(_bad_fns);
  v->global(_fairness);
  v->global(_fairness_fns);
  v->global(_justice);
  for (v_size i = 0; i != _justice_fn_sets.size(); ++i)
    v->global(_justice_fn_sets[i]);
  // Reset the maps that are now invalid.
  _input_var_to_fn.clear();
  _state_var_to_fn.clear();
  _output_var_to_fn.clear();
  _bad_var_to_fn.clear();
  _constraint_var_to_fn.clear();
  _justice_var_to_fn_set.clear();
  _fairness_var_to_fn.clear();
  for (v_size i = 0; i != _outputs.size(); ++i)
    _output_var_to_fn[_outputs[i]] = i;
  for (v_size i = 0; i != _inputs.size(); ++i)
    _input_var_to_fn[_inputs[i]] = i;
  for (v_size i = 0; i != _state_vars.size(); ++i)
    _state_var_to_fn[_state_vars[i]] = i;
  for (v_size i = 0; i != _bad.size(); ++i)
    _bad_var_to_fn[_bad[i]] = i;
  for (v_size i = 0; i != _constraint_fns.size(); ++i)
    _constraint_var_to_fn[_constraint_fns[i]] = i;
  for (v_size i = 0; i != _fairness.size(); ++i)
    _fairness_var_to_fn[_fairness[i]] = i;
  for (v_size i = 0; i != _justice.size(); ++i)
    _justice_var_to_fn_set[_justice[i]] = i;
}


std::string ExprAttachment::string(bool includeDetails) const
{
  Expr::Manager::View *v = _model.newView();

  std::ostringstream ret;
  ret << "EXPR (Timestamp = " << _ts << "):\nInputs:";
  for (const_v_iter i = _inputs.begin(); i != _inputs.end(); ++i)
    ret << Expr::stringOf(*v, *i, 1);

  ret << endl << "State Variables:";
  for (const_v_iter i = _state_vars.begin(); i != _state_vars.end(); ++i)
    ret << Expr::stringOf(*v, *i, 1);

  ret << endl << "Next State Functions:" << endl;
  for (v_size i = 0; i != _state_vars.size(); ++i) {
    ret << Expr::stringOf(*v, v->prime(_state_vars[i]), 1) + " =";
    if (i < _next_state_fns.size())
      ret << Expr::stringOf(*v, _next_state_fns[i],1);
    else
      ret << " undefined";
    ret << endl;
  }

  ret << "Outputs:" << endl;
  for (v_size i = 0; i != _outputs.size(); ++i) {
    ret << Expr::stringOf(*v, _outputs[i], 1) + " =";
    if (i < _output_fns.size())
      ret << Expr::stringOf(*v, _output_fns[i], 1);
    else
      ret << " undefined";
    ret << endl;
  }

  ret << "Initial:" << endl;
  for (const_v_iter i = _initial_cond.begin(); i != _initial_cond.end(); ++i)
    ret << Expr::stringOf(*v, *i, 1) << endl;

  ret << "Constraints:" << endl;
  for (const_v_iter i = _constraint_fns.begin(); i != _constraint_fns.end(); ++i)
    ret << Expr::stringOf(*v, *i, 1) << endl;

  ret << "Bad:" << endl;
  for (v_size i = 0; i != _bad.size(); ++i) {
    ret << Expr::stringOf(*v, _bad[i], 1) + " =";
    if (i < _bad_fns.size())
      ret << Expr::stringOf(*v, _bad_fns[i], 1);
    else
      ret << " undefined";
    ret << endl;
  }

  ret << "Buechi Fairness:" << endl;
  for (v_size i = 0; i != _fairness.size(); ++i) {
    ret << Expr::stringOf(*v, _fairness[i], 1) + " =";
    if (i < _fairness_fns.size())
      ret << Expr::stringOf(*v, _fairness_fns[i], 1);
    else
      ret << " undefined";
    ret << endl;
  }

  ret << "Buechi Justice:" << endl;
  for (v_size i = 0; i != _justice.size(); ++i) {
    ret << Expr::stringOf(*v, _justice[i], 1) + " =" << endl;
    if (i < _justice_fn_sets.size())
      for (v_size j = 0; j != _justice_fn_sets[i].size(); ++j)
        ret << Expr::stringOf(*v, _justice_fn_sets[i][j], 2) << endl;
    else
      ret << " undefined";
    ret << endl;
  }

  ret << "CTL Properties:" << endl;
  for (v_size i = 0; i != _ctl_properties.size(); ++i) {
    ret << Expr::stringOf(*v, _ctl_properties[i], 1);
    ret << endl;
  }
  
  delete v;
  return ret.str();

} // ExprAttachment::string


std::string ExprAttachment::dot(bool terse) const
{
  Expr::Manager::View * v = _model.newView();
  std::ostringstream dot;
  // Build graph header.
  dot << "digraph \"" << _model.name() << "\" {" << endl 
      << "edge [dir=none];" << endl;
  // Build the source subgraph with next state and output variables.
  dot << "{ rank=source;" << endl;
  for (const_v_iter i = _state_vars.begin(); i != _state_vars.end(); ++i) {
    ID y = v->prime(*i);
    dot << y << " [label=\"" << Expr::stringOf(*v, y) << "\"];" << endl;
  }
  for (const_v_iter i = _outputs.begin(); i != _outputs.end(); ++i) {
    dot << *i << " [label=\"" << Expr::stringOf(*v, *i) << "\"];" << endl;
  }
  dot << "}" << endl;
  // Add edges to corresponding functions.
  for (const_v_iter i = _state_vars.begin(); i != _state_vars.end(); ++i) {
    ID y = v->prime(*i);
    dot << y << " -> " << nextStateFnOf(*i) << ";" << endl;
  }
  for (const_v_iter i = _outputs.begin(); i != _outputs.end(); ++i) {
    dot << *i << " -> " << outputFnOf(*i) << ";" << endl;
  }
  // Create subgraph of the functions.
  vector<ID> src(_next_state_fns);
  src.insert(src.end(),_output_fns.begin(),_output_fns.end());
  dot << dotOf(*v, src, _model.name(), terse, true) << "}" << endl;
  // Engame.
  delete v;
  return dot.str();

} // ExprAttachment::dot


std::string ExprAttachment::circuitGraph(bool terse) const
{
  Expr::Manager::View * v = _model.newView();
  std::ostringstream dot;
  // Build graph header.
  dot << "digraph \"" << _model.name() 
      << "\" { orientation=landscape; rankdir=LR;\n" ;
  // Build the source subgraph with the output variables.
  for (const_v_iter i = _outputs.begin(); i != _outputs.end(); ++i) {
    dot << *i << " [shape=box,label=\"" << Expr::stringOf(*v, *i) << "\"];\n";
    ID of = outputFnOf(*i);
    Expr::Op nop = v->op(of);
    if (nop == Expr::Not) {
      ID nof = v->apply(Expr::Not, of);
      dot << nof << " -> " << *i << " [style = dashed];\n";
    } else {
      dot << of << " -> " << *i << ";\n";
    }
  }
  // Create subgraph of the functions.
  vector<ID> src(_next_state_fns);
  src.insert(src.end(),_output_fns.begin(),_output_fns.end());
  dot << circuitGraphOf(*v, src, _model.name(), terse, true);
  // Add connections from next state functions to current state variables.
  for (const_v_iter i = _state_vars.begin(); i != _state_vars.end(); ++i) {
    ID nsf = nextStateFnOf(*i);
    Expr::Op nop = v->op(nsf);
    if (nop == Expr::Not) {
      ID nnsf = v->apply(Expr::Not, nsf);
      dot << nnsf << " -> " << *i << " [style = dashed];\n";
    } else {
      dot << nsf << " -> " << *i << ";\n";
    }
  }
  dot << "}\n";
  // Engame.
  delete v;
  return dot.str();

} // ExprAttachment::circuitGraph


std::string ExprAttachment::verilog() const
{
  Expr::Manager::View *v = _model.newView();

  std::ostringstream ret;
  bool hasClock = _state_vars.size() > 0;
  ret << "module " << _model.name();
  if (hasClock)
    ret << "(\n  clock";
  for (const_v_iter i = _inputs.begin(); i != _inputs.end(); ++i) {
    ret << ((i == _inputs.begin() && !hasClock) ? "(\n  " : ",\n  ");
    ret << Expr::stringOf(*v, *i);
  }
  for (const_v_iter i = _outputs.begin(); i != _outputs.end(); ++i) {
    ret << ((i == _outputs.begin() && _inputs.size() == 0 && !hasClock)
	    ? "(\n  " : ",\n  ");
    ret << Expr::stringOf(*v, *i);
  }
  ret << ");\n";
  if (hasClock)
    ret << "  input clock;\n";
  for (const_v_iter i = _inputs.begin(); i != _inputs.end(); ++i) {
    ret << "  input " << Expr::stringOf(*v, *i) << ";\n";;
  }
  for (const_v_iter i = _outputs.begin(); i != _outputs.end(); ++i) {
    ret << "  output " << Expr::stringOf(*v, *i) << ";\n";;
  }
  vector<ID> roots = _output_fns;
  roots.insert(roots.end(),_next_state_fns.begin(),_next_state_fns.end());
  ret << verilogOf(*v, roots);
  if (hasClock) {
    for (const_v_iter i = _state_vars.begin(); i != _state_vars.end(); ++i) {
      ret << "  reg " << Expr::stringOf(*v, *i) << "; ";
      // Only valid for AIGER 1.0!
      ret << "initial " << Expr::stringOf(*v, *i) << " = 0;\n";
    }
    for (v_size i = 0; i != _state_vars.size(); ++i) {
      ret << "  always @ (posedge clock) ";
      ret << Expr::stringOf(*v, _state_vars[i]) << " <= ";
      if (i < _next_state_fns.size())
        Expr::shortStringOfID(*v, _next_state_fns[i], ret);
      else
	ret << " x";
      ret << ";\n";
    }
  }
  for (v_size i = 0; i != _outputs.size(); ++i) {
    ret << "  assign " << Expr::stringOf(*v, _outputs[i]) << " = ";
    Expr::shortStringOfID(*v, _output_fns[i], ret);
    ret << ";\n";;
  }
  ret << "endmodule // " << _model.name() << std::endl;
  delete v;
  return ret.str();

} // ExprAttachment::verilog

namespace {

  bool nameWithPhase(
    const ID id,
    Expr::Manager::View *v,
    ostringstream& buf)
  {
    ostringstream wbuf;
    Expr::shortStringOfID(*v, id, wbuf);
    string name = wbuf.str();
    bool phase = name[0] != '!';
    if (phase)
      buf << name;
    else
      buf << name.substr(1,name.size()-1);
    return phase;
  }

  void makeInverter(
    const ID id,
    Expr::Manager::View *v,
    ostringstream& buf)
  {
    buf << ".names ";
    (void) nameWithPhase(id, v, buf);
    buf << " ";
    (void) nameWithPhase(id, v, buf);
    buf << "$n\n0 1\n1 0\n";
  }

}

std::string ExprAttachment::blifMv() const
{
  Expr::Manager::View *v = _model.newView();

  std::ostringstream ret;
  ret << ".model " << _model.name() << "\n";
  for (const_v_iter i = _inputs.begin(); i != _inputs.end(); ++i) {
    ret << ".inputs " << Expr::stringOf(*v, *i) << "\n";
  }
  if(!_outputs.empty())
    ret << "#Normal Outputs\n";
  for (const_v_iter i = _outputs.begin(); i != _outputs.end(); ++i) {
    ret << ".outputs " << Expr::stringOf(*v, *i) << "\n";
  }
  if(!_bad.empty())
    ret << "#Bad State Properties\n";
  for (const_v_iter i = _bad.begin(); i != _bad.end(); ++i) {
    ret << ".outputs " << Expr::stringOf(*v, *i) << "\n";
  }
  if(!_constraint_fns.empty())
    ret << "#Invariant Constraints\n";
  //Constraints currently don't have names
  for (unsigned index = 0; index < _constraint_fns.size(); ++index) {
    if(v->nprimes(_constraint_fns[index]) == 0) {
      ret << ".outputs constraint_" << index << "\n";
    }
  }
  if(!_justice.empty())
    ret << "#Justice Properties\n";
  for (const_v_iter i = _justice.begin(); i != _justice.end(); ++i) {
    const vector<ID> & justiceSet = justiceSetOf(*i);
    ret << ".outputs";
    for (unsigned index = 0; index < justiceSet.size(); ++index) {
      ret << " " << Expr::stringOf(*v, *i) << "_" << index;
    }
    ret << "\n";
  }
  if(!_fairness.empty())
    ret << "#Fairness Constraints\n";
  for (const_v_iter i = _fairness.begin(); i != _fairness.end(); ++i) {
    ret << ".outputs " << Expr::stringOf(*v, *i) << "\n";
  }

  for (v_size i = 0; i != _state_vars.size(); ++i) {
    ret << ".latch ";
    bool phase = nameWithPhase(_next_state_fns[i], v, ret);
    if (!phase)
      ret << "$n";
    //Expr::shortStringOfID(*v, _next_state_fns[i], ret);
    ret << " " << Expr::stringOf(*v, _state_vars[i]);
    // Only valid for AIGER!
    ret << "\n.r " << Expr::stringOf(*v, _state_vars[i]) << "\n0\n";
    if (!phase)
      makeInverter(_next_state_fns[i], v, ret);
  }

  vector<ID> roots = _output_fns;
  roots.insert(roots.end(),_bad_fns.begin(),_bad_fns.end());
  for(const_v_iter i = _constraint_fns.begin(); i != _constraint_fns.end(); ++i) {
    vector<ID> conj;
    conjuncts(*v, *i, conj);
    roots.push_back(conj[0]);
  }
  for (v_size i = 0; i != _justice_fn_sets.size(); ++i) {
    roots.insert(roots.end(), _justice_fn_sets[i].begin(), _justice_fn_sets[i].end());
  }
  roots.insert(roots.end(),_fairness_fns.begin(),_fairness_fns.end());
  roots.insert(roots.end(),_next_state_fns.begin(),_next_state_fns.end());
  ret << blifMvOf(*v, roots);

  for (v_size i = 0; i != _outputs.size(); ++i) {
    ret << ".names ";
    bool phase = nameWithPhase(_output_fns[i], v, ret);
    ret << " " << Expr::stringOf(*v, _outputs[i]) << "\n.def 0\n";
    if (phase)
      ret << "1 1\n";
    else
      ret << "0 1\n";
  }
  for (v_size i = 0; i != _bad.size(); ++i) {
    ret << ".names ";
    bool phase = nameWithPhase(_bad_fns[i], v, ret);
    ret << " " << Expr::stringOf(*v, _bad[i]) << "\n.def 0\n";
    if (phase)
      ret << "1 1\n";
    else
      ret << "0 1\n";
  }
  for (v_size i = 0; i != _constraint_fns.size(); ++i) {
    vector<ID> conj;
    conjuncts(*v, _constraint_fns[i], conj);
    ret << ".names ";
    bool phase = nameWithPhase(conj[0], v, ret);
    ret << " constraint_" << i << "\n.def 0\n";
    if (phase)
      ret << "1 1\n";
    else
      ret << "0 1\n";
  }
  for (v_size i = 0; i != _justice.size(); ++i) {
    for (v_size j = 0; j != _justice_fn_sets[i].size(); ++j) {
      ret << ".names ";
      bool phase = nameWithPhase(_justice_fn_sets[i][j], v, ret);
      ret << " " << Expr::stringOf(*v, _justice[i]) << "_" << j << "\n.def 0\n";
      if (phase)
        ret << "1 1\n";
      else
        ret << "0 1\n";
    }
  }
  for (v_size i = 0; i != _fairness.size(); ++i) {
    ret << ".names ";
    bool phase = nameWithPhase(_fairness_fns[i], v, ret);
    ret << " " << Expr::stringOf(*v, _fairness[i]) << "\n.def 0\n";
    if (phase)
      ret << "1 1\n";
    else
      ret << "0 1\n";
  }


  ret << ".end" << std::endl;
  delete v;
  return ret.str();

} // ExprAttachment::blifMv

void ExprAttachment::AIGER(std::string filename) const
{
  Expr::Manager::View *v = _model.newView();
  aiger * aig = aiger_init();

  // Add I L O B C J F
  for (const_v_iter i = _inputs.begin(); i != _inputs.end(); ++i)
    aiger_add_input(aig, AIGERlit(*i), Expr::stringOf(*v, *i).c_str());

  // Build map for latch resets.  This is based on AIGER 1.9
  // and should be revised if the standard ever changes.
  unordered_map<ID,bool> initLatch;
  for (const_v_iter i = _initial_cond.begin(); i != _initial_cond.end(); ++i) {
    Expr::Op iop = v->op(*i);
    if (iop == Expr::Not)
      initLatch[v->apply(Expr::Not, *i)] = false;
    else
      initLatch[*i] = true;
  }
  mod_vec next_state_fns = _next_state_fns;
  Expr::AIGOfExprs(*v,next_state_fns);
  mod_vec roots = next_state_fns;
  for (v_size i = 0; i != _state_vars.size(); ++i) {
    unsigned alit = AIGERlit(_state_vars[i]);
    aiger_add_latch(aig, alit, AIGERlit(next_state_fns[i]),
                    Expr::stringOf(*v, _state_vars[i]).c_str());
    unordered_map<ID,bool>::const_iterator p = initLatch.find(_state_vars[i]);
    if (p == initLatch.end()) {
      // uninitialized latch
      aiger_add_reset(aig, alit, alit);
    } else if (p->second) {
      // latch set to 1
      aiger_add_reset(aig, alit, 1U);
    }
  }

  mod_vec output_fns = _output_fns;
  Expr::AIGOfExprs(*v,output_fns);
  roots.insert(roots.end(), output_fns.begin(), output_fns.end());
  for (v_size i = 0; i != _outputs.size(); ++i)
    aiger_add_output(aig, AIGERlit(output_fns[i]), Expr::stringOf(*v, _outputs[i]).c_str());

  mod_vec bad_fns = _bad_fns;
  Expr::AIGOfExprs(*v,bad_fns);
  roots.insert(roots.end(), bad_fns.begin(), bad_fns.end());
  for (v_size i = 0; i != _bad.size(); ++i)
    aiger_add_bad(aig, AIGERlit(bad_fns[i]), Expr::stringOf(*v, _bad[i]).c_str());

  mod_vec constraintFns = _constraint_fns;
  Expr::AIGOfExprs(*v,constraintFns);
  roots.insert(roots.end(), constraintFns.begin(), constraintFns.end());
  for (v_size i = 0; i != _constraints.size(); ++i)
    aiger_add_constraint(aig, AIGERlit(constraintFns[i]), Expr::stringOf(*v, _constraints[i]).c_str());

  for (vector<mod_vec>::size_type i = 0; i != _justice_fn_sets.size(); ++i) {
    mod_vec justice_set = _justice_fn_sets[i];
    Expr::AIGOfExprs(*v,justice_set);
    roots.insert(roots.end(), justice_set.begin(), justice_set.end());
    unsigned *a = new unsigned[justice_set.size()];
    transform(justice_set.begin(), justice_set.end(), a, AIGERlit);
    aiger_add_justice(aig, justice_set.size(), a, Expr::stringOf(*v, _justice[i]).c_str());
    delete [] a;
  }

  mod_vec fairness_fns = _fairness_fns;
  Expr::AIGOfExprs(*v,fairness_fns);
  roots.insert(roots.end(), fairness_fns.begin(), fairness_fns.end());
  for (v_size i = 0; i != fairness_fns.size(); ++i)
    aiger_add_fairness(aig, AIGERlit(fairness_fns[i]), Expr::stringOf(*v, _fairness[i]).c_str());

  // Add AND gates and closing comments.
  AIGEROf(*v, roots, aig);
  aiger_add_comment(aig, PACKAGE_STRING);
  aiger_add_comment(aig, _model.name().c_str());
  aiger_add_comment(aig, "AIGER " AIGER_VERSION);

  // Check consistency and write file.
  char const * msg = aiger_check(aig);
  if (msg)
    throw(runtime_error(msg));

  if (!aiger_open_and_write_to_file(aig, filename.c_str())) {
    std::string s("unable to write ");
    s += filename;
    throw(runtime_error(s.c_str()));
  }
  aiger_reset(aig);

} // ExprAttachment::AIGER

#include <cassert>
#include <unordered_map>
#include <algorithm>

namespace
{

class ExprInfoFolder : public Expr::Manager::View::Folder {
public:
  ExprInfoFolder(Expr::Manager::View &v, unordered_map<ID, pair<int, int> > &length,
      unordered_map<ID, int> &fanout)
    : Expr::Manager::View::Folder(v), _length(length), _fanout(fanout) {}
  virtual ID fold(ID id, int n, const ID * const args)
  {
    switch (view().op(id)) {
      case Expr::True:
      case Expr::Var:
        _length[id] = make_pair(0, 0);
        break;
      case Expr::Not:
        assert(_length.find(args[0]) != _length.end());
        _length[id] = make_pair(_length[args[0]].first, _length[args[0]].second);
        break;
      case Expr::And:
        assert(_length.find(args[0]) != _length.end());
        assert(_length.find(args[1]) != _length.end());
        _length[id] = make_pair(min(_length[args[0]].first, _length[args[1]].first)+1,
            max(_length[args[0]].second, _length[args[1]].second)+1);

        if (view().op(args[0]) == Expr::Not)
          _fanout[view().apply(Expr::Not, args[0])]++;
        else
          _fanout[args[0]]++;
        if (view().op(args[1]) == Expr::Not)
          _fanout[view().apply(Expr::Not, args[1])]++;
        else
          _fanout[args[1]]++;
        break;
      default:
        assert(false);
    }
    return id;
  }
private:
  unordered_map<ID, pair<int, int> > &_length;
  unordered_map<ID, int> &_fanout;
};

} // namespace

void ExprAttachment::info() const {
  Expr::Manager::View *v = _model.newView();

  cout << "Inputs: " << _inputs.size() << " latches: " << _next_state_fns.size()
       << " outputs: " << _output_fns.size() << endl;

  // compute the length of longest combinational path
  vector<ID> ids;
  ids.insert(ids.end(), _output_fns.begin(), _output_fns.end());
  ids.insert(ids.end(), _next_state_fns.begin(), _next_state_fns.end());

  unordered_map<ID, pair<int, int> > length;
  unordered_map<ID, int> fanout;
  ExprInfoFolder f(*v, length, fanout);
  v->fold(f, ids);

  int min_length = 2000000000, max_length = 0;
  for (unsigned i = 0; i < ids.size(); ++i) {
    if (min_length > length[ids[i]].first) min_length = length[ids[i]].first;
    if (max_length < length[ids[i]].second) max_length = length[ids[i]].second;
  }
  cout << "Length of maximum combinational path: " << max_length << endl;

  for (unsigned i = 0; i < _output_fns.size(); ++i) {
    cout << "Length of minimum combinational path to output " << i
      << ": " << length[_output_fns[i]].first << endl;
    cout << "Length of maximum combinational path to output " << i
      << ": " << length[_output_fns[i]].second << endl;
  }

  int max_fanout = 0;
  int min_fanout = 2000000000;
  double total_fanout = 0.0;
  for (unordered_map<ID, int>::const_iterator fit = fanout.begin();
       fit != fanout.end(); ++fit) {
    int this_fanout = fit->second;
    total_fanout += (double) this_fanout;
    if (this_fanout > max_fanout)
      max_fanout = this_fanout;
    if (this_fanout < min_fanout)
      min_fanout = this_fanout;
  }
  cout << "Maximum/average/minimum fanout: " << max_fanout << "/" 
       << (total_fanout / (double) fanout.size())
       << "/" << min_fanout << endl;
    
  Options::Verbosity verbosity = _model.verbosity();
  if (verbosity > Options::Verbose) {
    // Print input fanout.
    for (unsigned i = 0; i < _inputs.size(); ++i) {
      cout << Expr::stringOf(*v, _inputs[i]) << " " << fanout[_inputs[i]] << endl;
    }
  }

  delete v;
} // ExprAttachment::info

void ExprAttachment::supportStateVars(Expr::Manager::View & v, ID id,
                                     set<ID> & stateVars) const {
  var_folder vf(v, _state_var_to_fn, stateVars);
  v.fold(vf, id);
}

void ExprAttachment::supportStateVars(Expr::Manager::View & v, vector<ID> ids,
                                      set<ID> & stateVars) const {
  var_folder vf(v, _state_var_to_fn, stateVars);
  v.fold(vf, ids);
}


void ExprAttachment::supportNodes(Expr::Manager::View & v, ID id,
				  set<ID> & intNodes) const {
  node_folder vf(v, intNodes);
  v.fold(vf, id);
}

void ExprAttachment::supportNodes(Expr::Manager::View & v, vector<ID> ids,
				     set<ID> & intNodes) const {
  node_folder vf(v, intNodes);
  v.fold(vf, ids);
}

