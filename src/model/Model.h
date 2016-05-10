/* -*- C++ -*- */

/********************************************************************
Copyright (c) 2010-2013, Regents of the University of Colorado

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

#ifndef _Model_
#define _Model_

/** @file Model.h */

#include <boost/program_options.hpp>
#include <unordered_map>
#include <deque>

#include "Key.h"
#include "Expr.h"
#include "SAT.h"
#include "cuddObj.hh"
#include "Verbosity.h"

#include <ostream>

/** Type of timestamps. */
typedef uint64_t TS;

/**
 * A class to hold the description of models to be analyzed.
 *
 * A model is a collection of attachments.
 */
class Model {
public:
  enum Mode { mNONE, mIC3, mFAIR, mIICTL };
  class Action;
  class Attachment;
  class AttachmentFactory;

  /**
   * A constructor that creates its own new manager.
   */
  Model(boost::program_options::variables_map & opts, std::string name = "anonymous"):
    _name(name), _options(opts), _manager(new Expr::Manager),
    _owns_manager(true) {
  }
  /**
   * A constructor that is passed someone else's manager.
   */
  Model(Expr::Manager * mgr, boost::program_options::variables_map & opts, std::string name = "anonymous"):
    _name(name), _options(opts), _manager(mgr),_owns_manager(false) {
    assert(_manager != 0);
  }

  /**
   * Copy constructor.
   *
   */
  Model(const Model& from): 
    _name(from._name), _options(from._options), _manager(from._manager),
    _owns_manager(false), _bdd_manager(from._bdd_manager),
    _tactics(from._tactics), verbosityLevel(from.verbosityLevel) {
    cloneAttachments(from);
  }
  /**
   * Assignment operator.
   */
  Model& operator=(const Model& rhs) {
    if (&rhs != this) {
      _name = rhs._name;
      //_options = rhs._options;
      _manager = rhs._manager;
      _owns_manager = false;
      _bdd_manager = rhs._bdd_manager;
      _tactics = rhs._tactics;
      verbosityLevel = rhs.verbosityLevel;
      cloneAttachments(rhs);
    }
    return *this;
  }
  /**
   * Destructor that frees manager if object owns it.
   */
  ~Model();
  /**
   * Return the model's name.
   */
  const std::string& name() const { return _name;}
  void setName(std::string name) { _name = name; }
  /**
   * Return a view of the model's manager.
   *
   * This view is used to create expressions to be added to the model.
   */
  Expr::Manager::View * newView() const { return _manager->newView(); }
  /**
   * Return a SAT manager based on the model's Expr manager.
   */
  SAT::Manager * newSATManager() const { 
    return new SAT::Manager(*_manager, verbosityLevel > 0); 
  }
  /**
   * Return a reference to the model's BDD manager.
   */
  Cudd const &  bddManager() const { return _bdd_manager; }

  Cudd newBddManager(Cudd newMgr) { 
    Cudd saveMgr = _bdd_manager;
    _bdd_manager = newMgr;
    return saveMgr;
  }

  Expr::Manager* manager() const { return _manager; }
  const boost::program_options::variables_map & options() const { return _options; }
  boost::program_options::variables_map & options() { return _options; }
  void setOptionValue(const std::string & option, const boost::any & value);
  void setOption(const std::string & option);
  void setVerbosity(Options::Verbosity l) { verbosityLevel = l; }
  Options::Verbosity verbosity() const { return verbosityLevel; }
  void setDefaultMode(Mode mode) { _defaultMode = mode; }
  Mode defaultMode() const { return _defaultMode; }
  // Printout methods.
  std::string string(bool includeDetails = false) const;
  std::string dot(bool terse = true) const;
  std::string verilog() const;
  std::string blifMv() const;
  void AIGER(std::string filename) const;
  // Attachment map interface.
  void attach(Attachment * attachment);
  void detach(Key::Type key);
  void detach(Attachment * attachment);
  Attachment * attachment(Key::Type key) const;
  Attachment const * constAttachment(Key::Type key) const;
  void release(Attachment * at) const;
  void constRelease(Attachment const * at) const;
  // Tactic queue interface.
  void pushBackTactic(Action * tactic);
  void pushFrontTactic(Action * tactic);
  Action * popTactic();
  void clearTactics();
  // Timestamp management interface.
  static TS newTimestamp() { return ++_stamp; }
  static TS nextTimestamp() { _usedNextTS = true; return _stamp+1; }
  static void endEpoch() { 
    if (_usedNextTS) ++_stamp;
    _usedNextTS = false;
  }
private:
  class KeyHash {
  public:
    size_t operator()(const Key::Type key) const { return key; }
  };
  void cloneAttachments(const Model& from);

  /* Types */
  typedef std::unordered_map<Key::Type, Attachment*, KeyHash> at_map;
  typedef std::deque<Action *> act_q;

  std::string _name;
  boost::program_options::variables_map & _options;
  Expr::Manager *_manager;
  bool _owns_manager;
  Cudd _bdd_manager;
  at_map _attachments;
  act_q _tactics;
  static TS _stamp;
  static bool _usedNextTS;
  Options::Verbosity verbosityLevel;
  Mode _defaultMode;
};

class Model::AttachmentFactory {
public:
  virtual Model::Attachment * operator()(Model & model) = 0;
};

class Model::Action {
public:
  Action(Model & model) : _model(model), _ts(0) {}

  virtual ~Action() {}

  void make();

  virtual void exec() = 0;

  void requires(Key::Type key, Model::AttachmentFactory * fact);

  void prefer(Key::Type key, Model::AttachmentFactory * fact);
  void orElse(Key::Type key, Model::AttachmentFactory * fact);

  void over(Key::Type key, Model::AttachmentFactory * fact);
  void toNothing();

  Model& model() const { return _model; }
  Cudd const & bddManager() const { return _model.bddManager(); }
  const boost::program_options::variables_map & options() const { return _model.options(); }

  void updateTimestamp() { _ts = Model::nextTimestamp(); }
  TS timestamp() const { return _ts; }
  bool empty() const {return _ts == 0; }

protected:

  typedef std::pair<Key::Type, Model::AttachmentFactory *> ReqPair;

  TS mostRecentTimeStamp(std::set<Model::Action*>& visited);
  void done(bool needLast = true);

  std::vector<ReqPair> _reqBuild;
  Model& _model;
  std::vector< std::vector<Key::Type> > _dep;
  TS _ts;

  TS _make(bool);
};

class Model::Attachment : public Model::Action {
public:
  Attachment(Model& model) : Model::Action(model) {}
  Attachment(const Attachment& from) : Action(from) {
    //std::cout << "Generic Attachment Copy constructor" << std::endl;
    if (from._ts == 0)
      _ts = 0;
    else
      _ts = Model::newTimestamp();
  }
  virtual Attachment* clone() const { return 0; }
  virtual Attachment& operator=(Attachment& rhs) {
    if (&rhs != this) {
      _model = rhs._model;
      _dep = rhs._dep;
      if (rhs.timestamp() == 0)
	_ts = 0;
      else
	_ts = Model::newTimestamp();
    }
    return *this;
  }
  virtual ~Attachment() {}

  virtual void build() = 0;
  virtual Key::Type key() const = 0;
  virtual std::string string(bool includeDetails = false) const = 0;
  virtual std::string dot(bool terse = true) const { return ""; }
  virtual std::string verilog() const { return ""; }
  virtual std::string blifMv() const { return ""; }
  virtual void AIGER(std::string filename) const {}

  void exec();

protected:
  void make() { assert (false); }
};

std::ostream & operator<<(std::ostream & os, Model::Mode m);

#endif // _Model_
