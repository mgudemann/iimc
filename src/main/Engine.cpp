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

#include "Util.h"
#include "Error.h"
#include "ProofAttachment.h"
#include "Engine.h"
#include "Random.h"
/*
#include <pthread.h>
*/

using namespace std;

void Engine::operator()()
{
  /*
  pthread_attr_t attribute;
  pthread_attr_init(&attribute);
  size_t sz;
  pthread_attr_getstacksize(&attribute, &sz);
  cout << "sz: " << sz << endl;
  */
  int64_t startTime = Util::get_thread_cpu_time();
  ostringstream oss;
  Options::Verbosity verbosity = tactic_->model().verbosity();
  Random::register_thread();
  auto const id = this_thread::get_id();
  // Wait until the thread dispatcher has finished initializations.
  start_gun_.wait();
  if (verbosity > Options::Silent){
    oss << "Starting thread " << hex << id << endl;
    cout << oss.str();
    oss.str("");
  }
  try {
    tactic_->setTerminationFlag(&termination_flag_);
    tactic_->make();
    // Check whether there is a conclusion.
    ProofAttachment const * pat =
      (ProofAttachment const *) tactic_->model().constAttachment(Key::PROOF);
    bool done = pat && pat->hasConclusion();
    tactic_->model().constRelease(pat);
    if (done && this_thread::get_id() == id) {
      // Use try-catch because set_value throws if promise already set.
      try {
        promise_.set_value(Util::get_user_cpu_time());
      } catch (future_error const & e) {
        if (verbosity > Options::Silent)
          oss << "Thread " << id << " beaten to the line: "
              << e.code().message() << endl;
      }
    }
  } catch (Incomplete const & e) {
    // Thread timed out or was terminated.
    if (verbosity > Options::Silent)
      oss << "Thread " << id << " " << e.what() << endl;
#ifndef NOTCOMP
  } catch (exception const & e) {
    // If an exception can say "what", let's hear.
    if (verbosity > Options::Silent)
      oss << "Thread " << id << " " << e.what() << endl;
  } catch (Exception const & e) {
    // If an exception can say "what", let's hear.
    if (verbosity > Options::Silent)
      oss << "Thread " << id << " " << e.what() << endl;
  } catch (...) {
    if (verbosity > Options::Silent)
      oss << "Thread " << id << " threw an unrecognized exception" << endl;
#else
  } catch (...) {
    // Use try-catch because set_exception throws if another exception
    // is already registered.
    try {
      promise_.set_exception(current_exception());
    } catch (future_error const & e) {
      if (verbosity > Options::Silent)
        oss << "Thread " << id << " multiple exceptions: "
            << e.code().message() << endl;
    }
#endif
  }
  if (verbosity > Options::Silent) {
    int64_t endTime = Util::get_thread_cpu_time();
    oss << "Thread " << id << " spent " << ((endTime - startTime) / 1000000.0)
        << " s" << endl;
    cout << oss.str();
  }
  delete tactic_;
}
