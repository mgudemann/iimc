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
  BddTrAttachment(Model& model) :
  Model::Attachment(model) {
    BddAttachment::Factory f;
    requires(Key::BDD, &f);
  }
  /** Copy constructor. */
  BddTrAttachment(const BddTrAttachment& from, Model & model) : 
    Model::Attachment(from, model)
  {}
  /** Return the key of this type of attachment. */
  Key::Type key() const { return Key::BDD_TR; }
  std::string string(bool includeDetails = false) const;
  void build(void);
  bool buildGSHTR(void);

  class Factory : public Model::AttachmentFactory {
  public:
    virtual BddTrAttachment * operator()(Model & model) {
      return new BddTrAttachment(model);
    }
  };

  bool hasBdds(void) const { return _tr.size() > 0; }
  //BDD transitionRelation() const { return _tr; }
  BDD initialCondition() const { return _init; }
  std::vector<BDD> currentStateVars(void) const { return _xvars; }
  std::vector<BDD> nextStateVars(void) const { return _yvars; }
  std::vector<BDD> inputVars(void) const { return _ivars; }
  std::vector<BDD> invariants(void) const { return _inv; }
  std::vector<BDD> outputFunctions(void) const { return _of; }
  std::vector<BDD> constraints(void) const { return _constr; }
  BDD img(const BDD& from, bool keepPi = false) const;
  BDD preimg(const BDD& from, bool keepPi = false) const;
  BDD preimgGSH(const BDD& from, bool keepPi = false) const;
  void resetBddManager(const std::string bdd_to) const;

protected:
  BddTrAttachment* clone(Model & model) const { return new BddTrAttachment(*this, model); }
private:
  /** Transition Relation Part */
  class RelPart {
  public:
    RelPart(BDD p, BDD fc, BDD fcn, BDD bc, BDD bcn)
      : _part(p), _fw_qc(fc), _fw_qc_no_pi(fcn), _bw_qc(bc), _bw_qc_no_pi(bcn) {}
    BDD part(void) const { return _part; }
    BDD fwQuantCube(bool noPi = false) const {
      return noPi ? _fw_qc_no_pi : _fw_qc;
    }
    BDD bwQuantCube(bool noPi = false) const {
      return noPi ? _bw_qc_no_pi : _bw_qc;
    }
  private:
    BDD _part;
    BDD _fw_qc;
    BDD _fw_qc_no_pi;
    BDD _bw_qc;
    BDD _bw_qc_no_pi;
  };
  void composeAuxiliaryFunctions(BddAttachment const * bat,
                                 BDD & f, std::unordered_map<int,ID> const & index2id);
  std::vector<BDD> clusterConjunctsOld(std::vector<BDD>& conjuncts,
                                       unsigned int limit,
                                       Options::Verbosity verbosity, 
                                       int nvars) const;
  std::vector<BDD> clusterConjuncts(std::vector<BDD>& conjuncts,
                                    const BDD& qcube, unsigned int limit,
                                    Options::Verbosity verbosity) const;
  BDD quantifyLocalInputs(std::vector<BDD>& conjuncts, const BDD& qcube,
                          unsigned int limit, Options::Verbosity verbosity) const;
  void computeSchedule(const std::vector<BDD>& conjuncts, const BDD& wCube,
                       std::unordered_map<int, ID> index2id,
                       std::vector<RelPart> & tr, BDD & prequantx, BDD & prequanty);
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
  std::vector<BDD> _xvars, _yvars, _ivars;
  std::vector<BDD> _inv;
  std::vector<BDD> _of;
  std::vector<BDD> _constr;
  std::vector< RelPart > _trGSH;
  BDD _prequantxGSH, _prequantyGSH;
};

#endif // _BddTrAttachment_
