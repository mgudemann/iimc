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

#include "ExprUtil.h"
#include "Model.h"

using namespace std;

TS Model::_stamp = 0;
bool Model::_usedNextTS = false;

Model::~Model() {
  //cout << "Model Destructor" << endl;
  for (at_map::iterator i = _attachments.begin();
       i != _attachments.end(); ++i) {
    delete i->second;
  }
  if (_owns_manager) delete _manager;
}

/**
 * Construct a string from a model.
 */
std::string Model::string(bool includeDetails) const
{
  std::ostringstream ret;
  ret << "Model " << name() << endl;

  ret << "Attachments:" << endl;
  for (at_map::const_iterator i = _attachments.begin();
       i != _attachments.end(); ++i) {
    ret << i->second->string(includeDetails) << endl;
  }

  return ret.str();
}

/**
 * Describes the expressions of a model in dot format.
 */
std::string Model::dot(bool terse) const
{
  Attachment const *eat = constAttachment(Key::EXPR);
  std::string ret = (eat == 0) ? "" : eat->dot(terse);
  constRelease(eat);
  return ret;
}

/**
 * Describes the expressions of a model in verilog.
 */
std::string Model::verilog() const
{
  Attachment const *eat = constAttachment(Key::EXPR);
  std::string ret = (eat == 0) ? "" : eat->verilog();
  constRelease(eat);
  return ret;
}

/**
 * Describes the expressions of a model in blif-mv.
 */
std::string Model::blifMv() const
{
  Attachment const *eat = constAttachment(Key::EXPR);
  std::string ret = (eat == 0) ? "" : eat->blifMv();
  constRelease(eat);
  return ret;
}

/**
 * Add an attachment to a model under a key.
 *
 * What if we try to attach twice under the same key?
 */
void Model::attach(Model::Attachment* attachment) {
  Key::Type key = attachment->key();
  _attachments[key] = attachment;
}

/**
 * Remove an attachment from a model.
 */
void Model::detach(Key::Type key) {
  at_map::iterator iter = _attachments.find(key);
  if (iter != _attachments.end()) {
    delete iter->second;
    _attachments.erase(iter);
  }
}

/**
 * Remove an attachment from a model.
 */
void Model::detach(Model::Attachment* attachment) {
  Key::Type key = attachment->key();
  at_map::iterator iter = _attachments.find(key);
  if (iter != _attachments.end()) {
    delete iter->second;
    _attachments.erase(iter);
  }
}

/**
 * Retrieve the attachment associated with key.
 *
 * A null pointer is returned if no attachment for the given key exists.
 */
Model::Attachment* Model::attachment(Key::Type key) const {
  at_map::const_iterator iter = _attachments.find(key);
  if (iter == _attachments.end()) {
    return 0;
  } else {
    // Here we'll deal with locks when we have them.
    return iter->second;
  }
}

/**
 * Retrieve the attachment associated with key for read access.
 *
 * A null pointer is returned if no attachment for the given key exists.
 */
Model::Attachment const * Model::constAttachment(Key::Type key) const {
  at_map::const_iterator iter = _attachments.find(key);
  if (iter == _attachments.end())
    return 0;
  else
    return iter->second;
}


/**
 * Release an attachment obtained with attachment().
 *
 * The timestamp of the attachment is increased as a side effect.
 */
void Model::release(Model::Attachment* at) const {
  at->updateTimestamp();
  // Here we'll deal with locks when we have them.
}


/**
 * Release an attachment obtained with constAttachment().
 */
void Model::constRelease(Model::Attachment const * at) const {
  // Here we'll deal with locks when we have them.
}


/**
 * Clone attachments.
 */
void Model::cloneAttachments(const Model& from)
{
  for (at_map::const_iterator i = from._attachments.begin();
       i != from._attachments.end(); ++i) {
    Key::Type key = i->first;
    Model::Attachment *fat = i->second;
    Model::Attachment *tat = fat->clone();
    _attachments[key] = tat;
  }
}

void Model::Action::make() {
  _make(true);
  Model::endEpoch();
  exec();
  Model::endEpoch();
}

TS Model::Action::_make(bool action) {
  set<Model::Action*> visited;
  TS mrts = mostRecentTimeStamp(visited);
  if (mrts == 0) mrts = Model::nextTimestamp();
  if (mrts > _ts) {
    for (std::vector< std::vector<Key::Type> >::const_iterator i = _dep.begin();
         i != _dep.end(); ++i) {
      for (std::vector<Key::Type>::const_iterator ti = i->begin(); ti != i->end(); ++ti) {
        Key::Type key = *ti;
        Model::Attachment *at = _model.attachment(key);
        if (at != 0 && (!at->empty() || ti+1 == i->end())) {
          mrts = max(mrts, at->_make(false));
          break;
        }
      }
    }
    if (!action) {
      exec();
      _ts = max(_ts, mrts);
    }
  }
  return _ts;
}

TS Model::Action::mostRecentTimeStamp(set<Model::Action*>& visited)
{
  if (visited.find(this) != visited.end()) return _ts;
  visited.insert(this);
  TS mostRecent = _ts;
  for (std::vector< std::vector<Key::Type> >::const_iterator i = _dep.begin();
       i != _dep.end(); ++i) {
    for (std::vector<Key::Type>::const_iterator ti = i->begin(); ti != i->end(); ++ti) {
      Key::Type key = *ti;
      Model::Attachment *at = _model.attachment(key);
      if (at != 0 && (!at->empty() || ti+1 == i->end())) {
        mostRecent = std::max(mostRecent, at->mostRecentTimeStamp(visited));
        break;
      }
    }
  }
  return mostRecent;
}

void Model::Action::requires(Key::Type key, Model::AttachmentFactory * fact) {
  _reqBuild.push_back(ReqPair(key, fact));
  done();
}

void Model::Action::prefer(Key::Type key, Model::AttachmentFactory * fact) {
  _reqBuild.push_back(ReqPair(key, fact));
}
void Model::Action::orElse(Key::Type key, Model::AttachmentFactory * fact) {
  _reqBuild.push_back(ReqPair(key, fact));
}

void Model::Action::over(Key::Type key, Model::AttachmentFactory * fact) {
  _reqBuild.push_back(ReqPair(key, fact));
  done();
}
void Model::Action::toNothing() {
  done(false);
  _dep.back().push_back(Key::NONE);
}

void Model::Action::done(bool needLast) {
  if (_reqBuild.size() > 0) {
    vector<Key::Type> keys;
    vector<ReqPair>::iterator it = _reqBuild.begin();
    for (; it != _reqBuild.end(); ++it) {
      if (_model.attachment(it->first) != 0)
        break;
      if (it+1 == _reqBuild.end() && needLast)
        _model.attach(it->second->operator()(_model));
      keys.push_back(it->first);
    }
    for (; it != _reqBuild.end(); ++it)
      keys.push_back(it->first);
    _dep.push_back(keys);
    _reqBuild.clear();
  }
}
