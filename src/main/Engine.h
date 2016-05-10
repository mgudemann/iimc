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

#ifndef Engine_
#define Engine_

/** @file Engine.h */

#include "Model.h"
#include "Util.h"
#include <atomic>

class Engine {
public:
  Engine(Model::Action * t, std::promise<int64_t> & p, std::atomic<bool> & tf,
	 std::shared_future<void> & start_gun):
    tactic_(t), promise_(p), termination_flag_(tf), start_gun_(start_gun){}
  void operator()(void);
private:
  Model::Action * tactic_;
  std::promise<int64_t> & promise_;
  std::atomic<bool> & termination_flag_;
  std::shared_future<void> start_gun_;
};

unsigned bitCount(unsigned long x);

class joinThreads {
public:
  explicit joinThreads(std::vector<std::thread>& t, Cudd const & bddMgr,
		       std::shared_future<int64_t> & future,
		       Options::Verbosity verbosity) :
    threads_(t), bddManager_(bddMgr), future_(future), verbosity_(verbosity){}
  ~joinThreads() {
    for (auto &it : threads_)
      if (it.joinable()) {
	if (verbosity_ > Options::Silent){
	  std::ostringstream oss;
	  oss << "Joining thread " << std::hex << it.get_id() << std::endl;
	  std::cout << oss.str();
	}
        it.join();
#if 0
	if (verbosity_ > Options::Silent){
	  oss << "Detatching thread " << std::hex << it.get_id() << std::endl;
	  std::cout << oss.str();
	}
        it.detach();
	assert( !it.joinable() );
#endif
      }
    bddManager_.UnregisterTerminationCallback();
    if (verbosity_ > Options::Silent){
      std::ostringstream oss;
      int64_t lag = (Util::get_user_cpu_time() - future_.get());
      oss << "Done. Lag is: " << std::dec << lag << " us" <<  std::endl;
      std::cout << oss.str();
    }
  }
  joinThreads(joinThreads const &)=delete;
  joinThreads& operator=(joinThreads const &)=delete;
private:
  std::vector<std::thread>& threads_;
  Cudd const & bddManager_;
  std::shared_future<int64_t> future_;
  Options::Verbosity verbosity_;
};

#endif // Engine_
