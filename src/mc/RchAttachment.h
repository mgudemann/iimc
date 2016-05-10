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

#ifndef _RchAttachment_
#define _RchAttachment_

/** @file RchAttachment.h */

#include "BddTrAttachment.h"
#include "Model.h"

/**
 * A class to hold reachability infomation on a model.
 */
class RchAttachment : public Model::Attachment {
public:
  RchAttachment(Model& model) : 
    Model::Attachment(model), _view(_model.newView()), _cex_lb(0),
    _has_tv_info(false), _fw_steps_bdd(0), _bw_steps_bdd(0),
    _fw_bdd_complete(false), _bw_bdd_complete(false) {
    ExprAttachment::Factory f;
    requires(Key::EXPR, &f);
  }
  ~RchAttachment() { delete _view; }
  /** Copy constructor. */
  RchAttachment(const RchAttachment& from) : 
    Model::Attachment(from),
    _fw_lb(from._fw_lb),
    _fw_ub(from._fw_ub),
    _bw_lb(from._bw_lb),
    _bw_ub(from._bw_ub),
    _cex_lb(from._cex_lb),
    _has_tv_info(from._has_tv_info),
    _stem_length(from._stem_length),
    _loop_length(from._loop_length),
    _stabilized(from._stabilized),
    _widened(from._widened),
    _fw_lb_bdd(from._fw_lb_bdd),
    _bw_lb_bdd(from._bw_lb_bdd),
    _fw_steps_bdd(from._fw_steps_bdd),
    _bw_steps_bdd(from._bw_steps_bdd),
    _fw_bdd_complete(from._fw_bdd_complete),
    _bw_bdd_complete(from._bw_bdd_complete) {
  }
  RchAttachment& operator=(RchAttachment& rhs) {
    if (&rhs != this) {
      _model = rhs._model;
      if (rhs._ts == 0)
	_ts = 0;
      else
	_ts = Model::newTimestamp();
      _fw_lb = rhs._fw_lb;
      _fw_ub = rhs._fw_ub;
      _bw_lb = rhs._bw_lb;
      _bw_ub = rhs._bw_ub;
      _cex_lb = rhs._cex_lb;
      _has_tv_info = rhs._has_tv_info;
      _stem_length = rhs._stem_length;
      _loop_length = rhs._loop_length;
      _stabilized = rhs._stabilized;
      _widened = rhs._widened;
      _fw_lb_bdd = rhs._fw_lb_bdd;
      _bw_lb_bdd = rhs._bw_lb_bdd;
      _fw_steps_bdd = rhs._fw_steps_bdd;
      _bw_steps_bdd = rhs._bw_steps_bdd;
      _fw_bdd_complete = rhs._fw_bdd_complete;
      _bw_bdd_complete = rhs._bw_bdd_complete;
    }
    return *this;
  }
  /** Return the key of this type of attachment. */
  Key::Type key() const { return Key::RCH; }
  /** Convert to string. */
  std::string string(bool includeDetails = false) const;
  /** Initialize. */
  void build();
  /** Return current lower bound on stated reachable from initial states. */
  ID forwardLowerBound() const { return _fw_lb; }
  void setForwardLowerBound(ID newFwLb) { _fw_lb = newFwLb; }
  ID updateForwardLowerBound(ID newFwLb) {
    return updateBound(newFwLb, _fw_lb, Expr::Or);
  }
  ID backwardLowerBound() const { return _bw_lb; }
  void setBackwardLowerBound(ID newBwLb) { _bw_lb = newBwLb; }
  ID updateBackwardLowerBound(ID newBwLb) {
    return updateBound(newBwLb, _bw_lb, Expr::Or);
  }
  ID forwardUpperBound() const { return _fw_ub; }
  void setForwardUpperBound(ID newFwUb) { _fw_ub = newFwUb; }
  ID updateForwardUpperBound(ID newFwUb) {
    return updateBound(newFwUb, _fw_ub, Expr::And);
  }
  ID backwardUpperBound() const { return _bw_ub; }
  void setBackwardUpperBound(ID newBwUb) { _bw_ub = newBwUb; }
  ID updateBackwardUpperBound(ID newBwUb) {
    return updateBound(newBwUb, _bw_ub, Expr::And);
  }
  /** These are currently pessimistic. */
  bool exactForward() { return _fw_lb == _fw_ub; }
  bool exactBackward() { return _bw_lb == _bw_ub; }
  unsigned int cexLowerBound() const { return _cex_lb; }
  unsigned int updateCexLowerBound(unsigned int newLb);

  /** From ternary simulation. */
  bool hasTvInfo() const { return _has_tv_info; }
  unsigned int stemLength() const { return _stem_length; }
  unsigned int loopLength() const { return _loop_length; }
  unsigned int stabilized() const { return _stabilized; }
  bool widened() const { return _widened; }
  void setTvInfo(unsigned int stem, unsigned int loop,
                 unsigned int stable, bool widened);

  /** Accessors for BDD-based bounds. */
  BDD forwardBddLowerBound() const { return _fw_lb_bdd; }
  void setForwardBddLowerBound(BDD newFwLb);
  BDD backwardBddLowerBound() const { return _bw_lb_bdd; }
  void setBackwardBddLowerBound(BDD newBwLb);

  /** 
   * Returns true if cube does not intersect the lower bound on the
   * forward reachable states.
   *
   * If a non-null pointer is passed as second argument, it is
   * supposed to be a pointer to a currently empty vector.  If the
   * return value is true, that vector will be filled with the
   * literals of an expansion of cube to a prime implicant of the
   * negation of the lower bound on the forward reachable states.
   * That is, a maximal cube that is still disjoint from the lower
   * bound on the reachable states.  If the return value is false,
   * nothing is done to prime.
   */
  bool disjointFromFwBdd(std::vector<ID> const & cube,
                         std::vector<ID>* prime = 0) const;
  /** Same as disjointFromFwBdd, but for backward reachable states. */
  bool disjointFromBwBdd(std::vector<ID> const & cube,
                         std::vector<ID>* prime = 0) const;
  bool disjointFromFwBddExpand(std::vector<ID> const & lb, std::vector<ID> const & ub,
                               std::vector<ID>* expansion) const;
  bool disjointFromBwBddExpand(std::vector<ID> const & lb, std::vector<ID> const & ub,
                               std::vector<ID>* expansion) const;

  // The number of BDD steps gives the distance from the initial or target
  // states below which it has been proved that there is no counterexample.
  int forwardStepsBdd() const { return _fw_steps_bdd; }
  int backwardStepsBdd() const { return _bw_steps_bdd; }
  void setForwardStepsBdd(int steps) { _fw_steps_bdd = steps; }
  void setBackwardStepsBdd(int steps) { _bw_steps_bdd = steps; }
  bool isBddForwardComplete(void) const { return _fw_bdd_complete; }
  bool isBddBackwardComplete(void) const { return _bw_bdd_complete; }
  void setBddForwardComplete(bool complete) { _fw_bdd_complete = complete; }
  void setBddBackwardComplete(bool complete) { _bw_bdd_complete = complete; }
  std::vector<BDD> const & forwardRings(void) const { return _forward_rings; }
  std::vector<BDD> const & backwardRings(void) const { return _backward_rings; }
  void setForwardRings(std::vector<BDD> const & rings) { _forward_rings = rings; }
  void setBackwardRings(std::vector<BDD> const & rings) { _backward_rings = rings; }

  class Factory : public Model::AttachmentFactory {
  public:
    virtual RchAttachment * operator()(Model & model) {
      return new RchAttachment(model);
    }
  };

  bool kForwardUpperBound(unsigned int k, std::vector< std::vector<ID> > & rv) const;
  void setKForwardUpperBound(unsigned int k, const std::vector< std::vector<ID> > & ub);
  bool kBackwardUpperBound(unsigned int k, std::vector< std::vector<ID> > & rv) const;
  void setKBackwardUpperBound(unsigned int k, const std::vector< std::vector<ID> > & ub);
  /**
   * Converts a vector of literals to the BDD of a cube.
   */
  BDD literalVectorToBdd(std::vector<ID> const & cube) const;
  /**
   * Converts the BDD of a cube into a vector of IDs.
   */
  void bddToLiteralVector(const BDD b, std::vector<ID>& v) const;
  /**
   * Converts a BDD into a CNF formula;
   */
  void bddToCnf(const BDD b, std::vector< std::vector<ID> >& v) const;
protected:
  RchAttachment* clone() const { return new RchAttachment(*this); }
private:
  ID updateBound(ID disjunct, ID bound, Expr::Op op);
  bool disjointFromBdd(std::vector<ID> const & cube, const BDD& bound, std::vector<ID>* prime) const;
  bool disjointFromBddExpand(std::vector<ID> const & lb, std::vector<ID> const & ub,
                             const BDD& bound, std::vector<ID>* expansion) const;

  Expr::Manager::View *_view;
  // Bounds on reachable states.
  ID _fw_lb;
  ID _fw_ub;
  // Single bounds for backward analysis are AIGER-specific, because in
  // general there are multiple targets.
  ID _bw_lb;
  ID _bw_ub;
  // Lower bound on length of counterexample (if one exists).
  unsigned int _cex_lb;
  // From ternary simulation.
  bool _has_tv_info;
  unsigned int _stem_length;
  unsigned int _loop_length;
  unsigned int _stabilized;
  bool _widened;
  // Lower bounds.
  BDD _fw_lb_bdd;
  BDD _bw_lb_bdd;
  int _fw_steps_bdd;
  int _bw_steps_bdd;
  bool _fw_bdd_complete;
  bool _bw_bdd_complete;
  std::vector<BDD> _forward_rings;
  std::vector<BDD> _backward_rings;

  bool kUpperBound(unsigned int, std::vector< std::vector<ID> > &, const std::vector< std::vector< std::vector<ID> > > &) const;
  void setKUpperBound(unsigned int, const std::vector< std::vector<ID> > &, std::vector< std::vector< std::vector<ID> > > &);
  std::vector< std::vector< std::vector<ID> > > _k_fw_ub;
  std::vector< std::vector< std::vector<ID> > > _k_bw_ub;
};

#endif // _RchAttachment_
