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

#ifndef Dispatch_
#define Dispatch_

/** @file Dispatch.h **/

#include "Model.h"
#include "options.h"

/** namespace of Dispatch */

namespace Dispatch {

  /**
   * Executes tactics in multiple threads.
   */
  class Fork : public Model::Action {
  public:
    Fork(Model & m) : Model::Action(m) {}
    void exec();
    bool isFork() { return true; }
  private:
    static ActionRegistrar action;
  };


  /**
   * Marks the end of a sequence of tactics to be executed in parallel.
   */
  class Join : public Model::Action {
  public:
    Join(Model & m) : Model::Action(m) {}
    void exec() {}
    bool isJoin() { return true; }
  private:
    static ActionRegistrar action;
  };


  /**
   * Executes tactics sequentially.
   */
  class Begin : public Model::Action {
  public:
    Begin(Model & m) : Model::Action(m) {}
    void exec();
    bool isBegin() { return true; }
    void pushBackTactic(Action * tactic);
    void pushFrontTactic(Action * tactic);
    Action * popTactic();
    void clearTactics();
  private:
    std::deque<Model::Action *> queue;
    static ActionRegistrar action;
  };


  /**
   * Marks the end of a sequence of tactics to be executed in series.
   */
  class End : public Model::Action {
  public:
    End(Model & m) : Model::Action(m) {}
    void exec() {}
    bool isEnd() { return true; }
  private:
    static ActionRegistrar action;
  };

}

#endif // Dispatch_
