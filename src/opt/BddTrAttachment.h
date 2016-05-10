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

#ifndef _BddTrAttachment_
#define _BddTrAttachment_

/** @file BddTrAttachment.h */

#include "BddAttachment.h"
#include "ExprBdd.h"
#include "Model.h"

/**
 * A class to hold BDDs for the transition relation of a model.
 */
class BddTrAttachment : public Model::Attachment {
public:
  BddTrAttachment(Model& model) : Model::Attachment(model) {
    BddAttachment::Factory f;
    requires(Key::BDD, &f);
  }
  /** Copy constructor. */
  BddTrAttachment(const BddTrAttachment& from) : 
    Model::Attachment(from),
    _tr(from._tr),
    _prequantx(from._prequantx),
    _prequanty(from._prequanty),
    _init(from._init),
    _xvars(from._xvars),
    _yvars(from._yvars),
    _inv(from._inv)
  {}
  BddTrAttachment& operator=(BddTrAttachment& rhs) {
    if (&rhs != this) {
      _model = rhs._model;
      if (rhs._ts == 0)
	_ts = 0;
      else
	_ts = Model::newTimestamp();
      _tr = rhs._tr;
      _prequantx = rhs._prequantx;
      _prequanty = rhs._prequanty;
      _init = rhs._init;
      _xvars = rhs._xvars;
      _yvars = rhs._yvars;
      _inv = rhs._inv;
    }
    return *this;
  }
  /** Return the key of this type of attachment. */
  Key::Type key() const { return Key::BDD_TR; }
  std::string string(bool includeDetails = false) const;
  void build();

  class Factory : public Model::AttachmentFactory {
  public:
    virtual BddTrAttachment * operator()(Model & model) {
      return new BddTrAttachment(model);
    }
  };

  bool hasBdds() const { return _tr.size() > 0; }
  //BDD transitionRelation() const { return _tr; }
  BDD initialCondition() const { return _init; }
  std::vector<BDD> currentStateVars() const { return _xvars; }
  std::vector<BDD> nextStateVars() const { return _yvars; }
  std::vector<BDD> invariants() const { return _inv; }
  std::vector<BDD> constraints() const { return _constr; }
  BDD img(const BDD& from) const;
  BDD preimg(const BDD& from) const;
  void resetBddManager(const std::string bdd_to) const;

protected:
  BddTrAttachment* clone() const { return new BddTrAttachment(*this); }
private:
  /** Transition Relation Part */
  class RelPart {
  public:
    RelPart(BDD p, BDD fc, BDD bc) : _part(p), _fw_qc(fc), _bw_qc(bc) {}
    BDD part() const { return _part; }
    BDD fwQuantCube() const { return _fw_qc; }
    BDD bwQuantCube() const { return _bw_qc; }
  private:
    BDD _part;
    BDD _fw_qc;
    BDD _bw_qc;
  };
  std::vector<BDD> clusterConjunctsOld(std::vector<BDD>& conjuncts,
                                       unsigned int limit,
                                       Options::Verbosity verbosity, 
                                       int nvars) const;
  std::vector<BDD> clusterConjuncts(std::vector<BDD>& conjuncts,
                                    const BDD& qcube, unsigned int limit,
                                    Options::Verbosity verbosity) const;
  BDD quantifyLocalInputs(std::vector<BDD>& conjuncts, const BDD& qcube,
                          unsigned int limit, Options::Verbosity verbosity) const;
  void computeSchedule(const std::vector<BDD>& conjuncts, const BDD& wCube);
  BDD flattenOutput(const std::vector<BDD>& conjuncts, const BDD& wCube);
  std::vector< std::vector<unsigned int> > 
  dependenceMatrix(const std::vector<BDD>& conjuncts) const;
  std::vector<unsigned int>
  forceDirectedArrangement(const std::vector< std::vector<unsigned int> >& depMat) const;
  std::map< unsigned int, std::vector<unsigned int> > 
  buildTranspose(const std::vector< std::vector<unsigned int> >& depMat) const;
  std::vector<BDD> linearArrangement(const std::vector<BDD>& conjuncts) const;
  unsigned int 
  computeCost(const std::map< unsigned int, std::vector<unsigned int> >& transpose,
              const std::vector<unsigned int>& arrangement) const;

  std::vector< RelPart > _tr;
  BDD _prequantx, _prequanty;
  BDD _init;
  std::vector<BDD> _xvars, _yvars;
  std::vector<BDD> _inv;
  std::vector<BDD> _constr;
};

#endif // _BddTrAttachment_
