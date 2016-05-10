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

#ifndef _Model_
#define _Model_

/** @file Model.h */

#include <boost/program_options.hpp>
#include <unordered_map>
#include <deque>
#include <thread>
#include <chrono>
#include <future>
#include <ostream>
#include <iostream>

#include "Key.h"
#include "Expr.h"
#include "SAT.h"
#include "cuddObj.hh"
#include "Verbosity.h"

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
  class Attachment_handle;
  template<typename T>
  class AttachmentRW;

  /**
   * A constructor that creates its own new manager.
   */
  Model(boost::program_options::variables_map & opts, std::string name = "anonymous"):
    _name(name), _options(opts), _manager(new Expr::Manager),
    _owns_manager(true), _theView(0), _defaultMode(mNONE), _ppDisabled(false) {
  }
  /**
   * A constructor that is passed someone else's manager.
   */
  Model(Expr::Manager * mgr, boost::program_options::variables_map & opts, std::string name = "anonymous"):
    _name(name), _options(opts), _manager(mgr), _owns_manager(false),
    _theView(0), _defaultMode(mNONE), _ppDisabled(false) {
    assert(_manager != 0);
  }

  /**
   * Copy constructor.
   *
   */
  Model(const Model& from): 
    _name(from._name), _options(from._options), _manager(from._manager),
    _owns_manager(false), _theView(0), _bdd_manager(from._bdd_manager),
    _tactics(from._tactics), verbosityLevel(from.verbosityLevel),
    _defaultMode(from._defaultMode), _ppDisabled(from._ppDisabled) {
    cloneAttachments(from);
  }
  /**
   * Assignment operator.
   */
  Model& operator=(const Model& rhs)=delete;
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
  Expr::Manager::View * newView() const {
    if (_theView) {
      Expr::Manager::View * vc = new Expr::Manager::View(*_theView);
      return vc;
    }
    return _manager->newView();
  }
  /**
   * Return a SAT manager based on the model's Expr manager.
   */
  SAT::Manager * newSATManager() const { 
    return new SAT::Manager(*_manager, verbosityLevel > 0 || _options.count("ic3_stats")); 
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
  void setView(Expr::Manager::View * view) { _theView = view; }
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
  /**
   * Retrieve the attachment associated with key.
   *
   * A null pointer is returned if no attachment for the given key exists.
   */
  template<typename T>
  AttachmentRW<T> attachment(Key::Type key) const {
    at_map::const_iterator iter = _attachments.find(key);
    if (iter == _attachments.end()) {
      return AttachmentRW<T>();
    } else {
      // Here we'll deal with locks when we have them.
      return AttachmentRW<T>((T *) iter->second);
    }
  }
  Attachment const * constAttachment(Key::Type key) const;
  /**
   * Release an attachment obtained with attachment().
   * It is OK to release a nullptr attachment (nothing happens).
   *
   * The timestamp of the attachment is increased as a side effect.
   */
  template<typename T>
  void release(AttachmentRW<T> const & at) const {
    if (at) {
      at->updateTimestamp();
      assert(at.owns_lock());
      at.unlock();
      assert(!at.owns_lock());
    }
  }
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
  std::promise<void>& getFcbmcPromise(void) { return fcbmcPromise; }
  std::promise<void>& getGshPromise(void) { return gshPromise; }
  bool ppIsDisabled(void) { return _ppDisabled; }
  void disablePp() { _ppDisabled = true; }
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
  Expr::Manager::View * _theView;
  Cudd _bdd_manager;
  at_map _attachments;
  act_q _tactics;
  static TS _stamp;
  static bool _usedNextTS;
  Options::Verbosity verbosityLevel;
  Mode _defaultMode;
  std::promise<void> fcbmcPromise;
  std::promise<void> gshPromise;
  bool _ppDisabled;
};

class Model::AttachmentFactory {
public:
  virtual Model::Attachment * operator()(Model & model) = 0;
};

class Model::Action {
public:
  Action(Model & model) : _model(model), _ts(0), _termination_flag_p(0) {}
  Action(const Action& from, Model & model) : _reqBuild(from._reqBuild),
                                              _model(model), _dep(from._dep),
                                              _ts(from._ts),
                                              _termination_flag_p(0) {}

  virtual ~Action() {}

  void make();
  void makeDeps() { _make(true); Model::endEpoch(); }

  virtual void exec() = 0;
  virtual bool isFork() { return false; }
  virtual bool isJoin() { return false; }
  virtual bool isBegin() { return false; }
  virtual bool isEnd() { return false; }

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

  /** Set shared future for termination handling. */
  void setTerminationFlag(std::atomic<bool> * p) { _termination_flag_p = p; }
  /** Return true if the future has been made ready. */
  bool futureReady(void) const;
  std::vector< std::vector<Key::Type> > const & dependencies() const { return _dep; }

protected:

  typedef std::pair<Key::Type, Model::AttachmentFactory *> ReqPair;

  TS mostRecentTimeStamp(std::set<Model::Action const *>& visited) const;
  void done(bool needLast = true);

  // Dependency tracking info.
  std::vector<ReqPair> _reqBuild;
  Model & _model;
  std::vector< std::vector<Key::Type> > _dep;
  TS _ts;
  std::atomic<bool> * _termination_flag_p;

  TS _make(bool action);
};

class Model::Attachment : public Model::Action {
public:
  Attachment(Model& model) : Model::Action(model) {}
  Attachment(Attachment const &)=delete;
  Attachment(const Attachment& from, Model& model) : Action(from, model) {
    //std::cout << "Generic Attachment Copy constructor" << std::endl;
    /*
    if (from._ts == 0)
      _ts = 0;
    else
      _ts = Model::newTimestamp();
    */
  }
  Attachment & operator=(Attachment const &)=delete;
  virtual Attachment* clone(Model &) const { return 0; }
  virtual ~Attachment() {}

  std::unique_lock<std::mutex> lock(void) const
  {
    return std::unique_lock<std::mutex>(mutex_);
  }

  virtual void build() = 0;
  virtual Key::Type key() const = 0;
  virtual std::string string(bool includeDetails = false) const = 0;
  virtual std::string dot(bool) const { return ""; }
  virtual std::string dot(void) const { return ""; }
  virtual std::string verilog() const { return ""; }
  virtual std::string blifMv() const { return ""; }
  virtual void AIGER(std::string) const {}

  void exec();

protected:
  void make() { assert (false); }
  mutable std::mutex mutex_;
};


std::ostream & operator<<(std::ostream & os, Model::Mode m);

/** This is the pure abstract class from which the two attachment handles
 * are derived.  Since these handles store locks, the classes are move-only.
 */
class Model::Attachment_handle {
public:
  virtual ~Attachment_handle() {}
  virtual void unlock(bool verbose = false) const = 0;
  virtual bool owns_lock(void) const = 0;
};

/** Handle class for read-write access. */
template<typename T>
class Model::AttachmentRW : public Model::Attachment_handle {
public:
  AttachmentRW(void) : at_(0) {}
  AttachmentRW(T * const at) : lock_(at->lock()), at_(at) {}
  AttachmentRW(const AttachmentRW&) = delete;
  AttachmentRW(AttachmentRW&& other): lock_(std::move(other.lock_)), at_(std::move(other.at_)) {}
  void lock(void) const { lock_.lock(); }
  void unlock(bool verbose = false) const { if (verbose) std::cout << "unlock" << std::endl; lock_.unlock(); }
  bool owns_lock(void) const { return lock_.owns_lock(); };
  T * operator->(void) const;
  T & operator*(void) const;
  operator bool() const {return at_; }
  std::unique_lock<std::mutex>& get_lock(void) const { return lock_; }
private:
  mutable std::unique_lock<std::mutex> lock_;
  T * const at_;
};

template<typename T>
T * Model::AttachmentRW<T>::operator->(void) const
{
  if (at_)
    return at_;
  throw std::runtime_error("unbound attachment");
}

template<typename T>
T & Model::AttachmentRW<T>::operator*(void) const
{
  if (at_)
    return *at_;
  throw std::runtime_error("unbound attachment");
}

#endif // _Model_
