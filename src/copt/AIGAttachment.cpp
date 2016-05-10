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

#include "ExprAttachment.h"
#include "AIGAttachment.h"

AIGAttachment::AIGAttachment(Model &model) : Model::Attachment(model)
{
  ExprAttachment::Factory f;
  requires(Key::EXPR, &f);
}

AIGAttachment::AIGAttachment(const AIGAttachment &from, Model & model) :
  Model::Attachment(from, model),
  aig(from.aig),
  ref2id(from.ref2id),
  id2ref(from.id2ref)
{
}

std::string AIGAttachment::string(bool includeDetails) const
{
  if (includeDetails) {
    std::ostringstream ret;
    ret << "AIG (Timestamp = " << _ts << "):\n  node array\n  "
        << aig.size()-1 << " variables";
    return ret.str();
  } else {
    return "AIG: node array";
  }
}

void AIGAttachment::build()
{
  Options::Verbosity verbosity = _model.verbosity();
  if (verbosity > Options::Silent)
    std::cout << "AIGAttachment: Building AIG for model " << _model.name() << std::endl;

  buildAIG(_model);
  if (verbosity >= Options::Verbose)
    std::cout << "AIGAttachment: Done with building AIG" << std::endl;
}

ID AIGAttachment::IDOf(Opt::NodeRef ref, Expr::Manager::View &v,
    Opt::IDRefMap& newId2ref, Opt::RefIDMap& newRef2id) const
{
  using namespace Opt;

  //Terminal cases: false, true, inverted node, variable
  if (ref == 0) return v.bfalse();
  if (ref == 1) return v.btrue();

  if (isNot(ref)) {
    ID neg = v.apply(Expr::Not, IDOf(invert(ref), v, newId2ref, newRef2id));
    newId2ref.insert(IDRefMap::value_type(neg, ref));
    newRef2id.insert(RefIDMap::value_type(ref, neg));
    return neg;
  }

  RefIDMap::iterator it = newRef2id.find(ref);
  if(it != newRef2id.end()) {
    return it->second;
  }

  const NodeIndex index = indexOf(ref);
  const AIGNode &node = aig[UIGET(index)];
  if (node.isVar()) {
    assert(newRef2id.find(ref) != newRef2id.end());
    return newRef2id[ref];
  }

  NodeRef fanin1ref = node[0];
  NodeRef fanin2ref = node[1];

  ID fanin1Id = IDOf(fanin1ref, v, newId2ref, newRef2id);
  ID fanin2Id = IDOf(fanin2ref, v, newId2ref, newRef2id);

  ID ret = v.apply(Expr::And, fanin1Id, fanin2Id);
  newId2ref.insert(IDRefMap::value_type(ret, ref));
  newRef2id.insert(RefIDMap::value_type(ref, ret));
  return ret;
}

void AIGAttachment::AIG2Expr()
{
  using namespace Opt;

  auto eat = _model.attachment<ExprAttachment>(Key::EXPR);
  Expr::Manager::View *v = _model.newView();

  const std::vector<NodeRef>& nextStateFns = aig.nextStateFnRefs();
  const std::vector<ID>& stateVars = eat->stateVars();
  assert(nextStateFns.size() == stateVars.size());

  const std::vector<NodeRef>& outputFns = aig.outputFnRefs();
  const std::vector<ID>& outputs = eat->outputs();
  assert(outputFns.size() == outputs.size());

  const std::vector<NodeRef>& badFns = aig.badFnRefs();
  const std::vector<ID>& bad = eat->bad();
  assert(badFns.size() == bad.size());

  const std::vector<NodeRef>& constraintFns = aig.constraintFnRefs();
  const std::vector<ID>& constraints = eat->constraints();

  const std::vector< std::vector<NodeRef> >& justiceFnSets = aig.justiceFnSetRefs();
  const std::vector<ID>& justice = eat->justice();
  assert(justiceFnSets.size() == justice.size());

  const std::vector<NodeRef>& fairnessFns = aig.fairnessFnRefs();
  const std::vector<ID>& fairness = eat->fairness();
  assert(fairnessFns.size() == fairness.size());

  IDRefMap newId2ref;
  RefIDMap newRef2id;
  //Insert the false and true nodes (AIG ref 0 = false, ref 1 = true)
  newId2ref.insert(IDRefMap::value_type(v->bfalse(), 0));
  newId2ref.insert(IDRefMap::value_type(v->btrue(), 1));
  newRef2id.insert(RefIDMap::value_type(0, v->bfalse()));
  newRef2id.insert(RefIDMap::value_type(1, v->btrue()));

  //Add all the inputs and state variables to the newId2ref and newRef2id maps
  for(unsigned i = 1; i <= aig.numInputs() + aig.numStateVars(); ++i) {
    NodeRef ref = refOf(i, false);
    assert(ref2id.find(ref) != ref2id.end());
    ID id = ref2id[ref];
    newId2ref.insert(IDRefMap::value_type(id, ref));
    newRef2id.insert(RefIDMap::value_type(ref, id));
  }

  for (unsigned i = 0; i < nextStateFns.size(); ++i) {
    //Recursively build an ID for this next state function
    ID fid = IDOf(nextStateFns[i], *v, newId2ref, newRef2id);
    //Set the next state function of the corresponding latch to fid
    eat->setNextStateFn(stateVars[i], fid);
  }

  if(!_model.options().count("satsweep_assumeProperty")) {
    for (unsigned i = 0; i < outputFns.size(); ++i) {
      //Recursively build an ID for this next state function
      ID fid = IDOf(outputFns[i], *v, newId2ref, newRef2id);
      //Set the output function of the corresponding output to fid
      eat->setOutputFn(outputs[i], fid);
    }
    for (unsigned i = 0; i < badFns.size(); ++i) {
      //Recursively build an ID for this next state function
      ID fid = IDOf(badFns[i], *v, newId2ref, newRef2id);
      //Set the bad function of the corresponding bad variable to fid
      eat->setBadFn(bad[i], fid);
    }
    for (unsigned i = 0; i < constraintFns.size(); ++i) {
      //Recursively build an ID for this next state function
      ID fid = IDOf(constraintFns[i], *v, newId2ref, newRef2id);
      //Add constraint
      eat->addConstraint(constraints[i],fid);
    }
    for (unsigned i = 0; i < justiceFnSets.size(); ++i) {
      std::vector<ID> just;
      for (unsigned j = 0; j < justiceFnSets[i].size(); ++j) {
        //Recursively build an ID for this next state function
        ID fid = IDOf(justiceFnSets[i][j], *v, newId2ref, newRef2id);
        //Set the bad function of the corresponding bad variable to fid
        just.push_back(fid);
      }
      eat->setJusticeSet(justice[i], just);
    }
    for (unsigned i = 0; i < fairnessFns.size(); ++i) {
      //Recursively build an ID for this next state function
      ID fid = IDOf(fairnessFns[i], *v, newId2ref, newRef2id);
      //Set the fairness function of the corresponding fairness variable to fid
      eat->setFairnessFn(fairness[i], fid);
    }


  }

  model().release(eat);
  delete v;

  id2ref = newId2ref;
  ref2id = newRef2id;

  // Make this attachment current with ExprAttachment.
  if(!_model.options().count("satsweep_assumeProperty")) {
    updateTimestamp();
  }
}


void AIGAttachment::buildAIG(Model &model)
{
  using namespace Opt;

  class TopologyFolder : public Expr::Manager::View::Folder {
  public:
    TopologyFolder(Expr::Manager::View &v, AIG &aig, IDRefMap &id2ref, RefIDMap &ref2id) :
      Expr::Manager::View::Folder(v), _aig(aig), _id2ref(id2ref), _ref2id(ref2id) {}
    virtual ID fold(ID id, int n, const ID * const idArgs)
    {
      Expr::Manager::View &v = view();
      switch (v.op(id)) {
      case Expr::Var: {
        //All variables must already be there
        if (_id2ref.find(id) == _id2ref.end())
          std::cout << Expr::stringOf(v, id) << std::endl;
        assert(_id2ref.find(id) != _id2ref.end());
        break; }
      case Expr::Not: {
        assert(_id2ref.find(v.apply(Expr::Not, id)) != _id2ref.end());
        NodeRef ref = _id2ref.find(v.apply(Expr::Not, id))->second;
        _id2ref.insert(IDRefMap::value_type(id, invert(ref)));
        _ref2id.insert(RefIDMap::value_type(invert(ref), id));
        break; }
      case Expr::And: {
        assert(n == 2);
        NodeRef args[2];
        assert(_id2ref.find(idArgs[0]) != _id2ref.end());
        args[0] = _id2ref.find(idArgs[0])->second;
        assert(_id2ref.find(idArgs[1]) != _id2ref.end());
        args[1] = _id2ref.find(idArgs[1])->second;
        NodeIndex index = _aig.addNode(args[0], args[1]);
        NodeRef ref = refOf(index, false);
        _id2ref.insert(IDRefMap::value_type(id, ref));
        _ref2id.insert(RefIDMap::value_type(ref, id));
        break; }
      case Expr::True:
        break;
      case Expr::Or: {
        assert(n == 2);
        NodeRef args[2];
        assert(_id2ref.find(idArgs[0]) != _id2ref.end());
        args[0] = _id2ref.find(idArgs[0])->second;
        assert(_id2ref.find(idArgs[1]) != _id2ref.end());
        args[1] = _id2ref.find(idArgs[1])->second;
        NodeIndex index = _aig.addNode(invert(args[0]), invert(args[1]));
        NodeRef ref = refOf(index, false);
        _id2ref.insert(IDRefMap::value_type(id, invert(ref)));
        _ref2id.insert(RefIDMap::value_type(invert(ref), id));
        break; }
      default:
        assert(false);
        break;
      }
      return id;
    }
  private:
    AIG &_aig;
    IDRefMap &_id2ref;
    RefIDMap &_ref2id;
  };

  id2ref.clear();
  ref2id.clear();
  aig.clear();
  
  Expr::Manager::View *v = model.newView();

  //Insert the false and true nodes (AIG ref 0 = false, ref 1 = true)
  id2ref.insert(IDRefMap::value_type(v->bfalse(), 0));
  id2ref.insert(IDRefMap::value_type(v->btrue(), 1));
  ref2id.insert(RefIDMap::value_type(0, v->bfalse()));
  ref2id.insert(RefIDMap::value_type(1, v->btrue()));

  ExprAttachment const * const eat = (ExprAttachment const *)model.constAttachment(Key::EXPR);

  const std::vector<ID>& inputs = eat->inputs();
  //Add all inputs to the AIG
  for(unsigned i = 0; i < inputs.size(); ++i) {
    NodeIndex index = aig.addNode();
    NodeRef ref = refOf(index, false);
    id2ref.insert(IDRefMap::value_type(inputs[i], ref));
    ref2id.insert(RefIDMap::value_type(ref, inputs[i]));
  }
  //Set the number of inputs in the AIG
  aig.numInputs() = inputs.size();

  const std::vector<ID>& stateVars = eat->stateVars();
  //Add all state variables to the AIG
  for(unsigned i = 0; i < stateVars.size(); ++i) {
    NodeIndex index = aig.addNode();
    NodeRef ref = refOf(index, false);
    id2ref.insert(IDRefMap::value_type(stateVars[i], ref));
    ref2id.insert(RefIDMap::value_type(ref, stateVars[i]));
  }
  //Set the number of state variables in the AIG
  aig.numStateVars() = stateVars.size();

  const std::vector<ID>& nextStateFns = eat->nextStateFns();
  const std::vector<ID>& outputFns = eat->outputFns();
  const std::vector<ID>& badFns = eat->badFns();
  const std::vector<ID>& constraintFns = eat->constraintFns();
  const std::vector< std::vector<ID> >& justiceFnSets = eat->justiceSets();
  const std::vector<ID>& fairnessFns = eat->fairnessFns();

  std::vector<ID> ids;
  ids.insert(ids.end(), nextStateFns.begin(), nextStateFns.end());
  ids.insert(ids.end(), outputFns.begin(), outputFns.end());
  ids.insert(ids.end(), badFns.begin(), badFns.end());
  ids.insert(ids.end(), constraintFns.begin(), constraintFns.end());
  for (size_t i = 0; i < justiceFnSets.size(); ++i)
    ids.insert(ids.end(), justiceFnSets[i].begin(), justiceFnSets[i].end());
  ids.insert(ids.end(), fairnessFns.begin(), fairnessFns.end());

  TopologyFolder folder(*v, aig, id2ref, ref2id);
  v->fold(folder, ids);

  for(unsigned i = 0; i < nextStateFns.size(); ++i) {
    assert(id2ref.find(nextStateFns[i]) != id2ref.end());
    aig.nextStateFnRefs().push_back(id2ref[nextStateFns[i]]);
    assert(ref2id[aig.nextStateFnRefs().back()] == nextStateFns[i]);
  }
  assert(aig.numStateVars() == aig.nextStateFnRefs().size());

  for(unsigned i = 0; i < outputFns.size(); ++i) {
    if(id2ref.find(outputFns[i]) != id2ref.end()) {
      aig.outputFnRefs().push_back(id2ref[outputFns[i]]);
      assert(ref2id[aig.outputFnRefs().back()] == outputFns[i]);
    }
  }

  //Add properties/constraints
  for(unsigned i = 0; i < badFns.size(); ++i) {
    if(id2ref.find(badFns[i]) != id2ref.end()) {
      aig.badFnRefs().push_back(id2ref[badFns[i]]);
      assert(ref2id[aig.badFnRefs().back()] == badFns[i]);
    }
  }
  for(unsigned i = 0; i < constraintFns.size(); ++i) {
    assert(id2ref.find(constraintFns[i]) != id2ref.end());
    aig.constraintFnRefs().push_back(id2ref[constraintFns[i]]);
    assert(ref2id[aig.constraintFnRefs().back()] == constraintFns[i]);
  }
  for(unsigned i = 0; i < justiceFnSets.size(); ++i) {
    aig.justiceFnSetRefs().push_back(std::vector<NodeRef>());
    for(unsigned j = 0; j < justiceFnSets[i].size(); ++j) {
      if(id2ref.find(justiceFnSets[i][j]) != id2ref.end()) {
        aig.justiceFnSetRefs()[i].push_back(id2ref[justiceFnSets[i][j]]);
        assert(ref2id[aig.justiceFnSetRefs()[i].back()] == justiceFnSets[i][j]);
      }
    }
  }
  for(unsigned i = 0; i < fairnessFns.size(); ++i) {
    if(id2ref.find(fairnessFns[i]) != id2ref.end()) {
      aig.fairnessFnRefs().push_back(id2ref[fairnessFns[i]]);
      assert(ref2id[aig.fairnessFnRefs().back()] == fairnessFns[i]);
    }
  }

  delete v;
  model.constRelease(eat);
}

void AIGAttachment::AIGOutputs(std::vector<Opt::NodeRef>& out) const
{
  using namespace Opt;

  ExprAttachment const * const eat = (ExprAttachment const *)_model.constAttachment(Key::EXPR);

#if 0
  for(IDRefMap::const_iterator i = id2ref.begin(); i != id2ref.end(); ++i) {
    std::cout << "id2ref: " << i->first << " " << i->second << std::endl;
  }
#endif

  std::vector<ID> outputs = eat->outputs();
  std::vector<ID> outputFns = eat->outputFnOf(outputs);

#if 0
  for(std::vector<ID>::iterator i = outputFns.begin(); i != outputFns.end(); ++i) {
    std::cout << "output id: " << *i << std::endl;
  }
#endif

  for(std::vector<ID>::iterator i = outputFns.begin(); i != outputFns.end(); ++i) {
    //std::cout << *i << std::endl;
    IDRefMap::const_iterator ref = id2ref.find(*i);
    assert(ref != id2ref.end());
    out.push_back(ref->second);
  }

  _model.constRelease(eat);
}
