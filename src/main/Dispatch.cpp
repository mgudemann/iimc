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

#include "Error.h"
#include "Dispatch.h"
#include "ProofAttachment.h"
#include "Engine.h"
#include "Util.h"
#include "Random.h"
#include <set>

using namespace std;

namespace {
  int callback(void const * handler_arg)
  {
    shared_future<unsigned> const * futurep =
      static_cast<shared_future<unsigned> const *>(handler_arg);
    auto const status = futurep->wait_for(std::chrono::seconds(0));
    return status == std::future_status::ready;
  }
}

namespace Dispatch {

  void Fork::exec() {
    assert(_dep.empty());
    deque<Model::Action *> actQueue;
    Model::Action * tactic;
    Begin * seriesBegin = 0;
    Options::Verbosity verbosity = model().verbosity();
    // Gather tactics and their common dependencies.
    set< vector<Key::Type> > depsets;
    while ((tactic = model().popTactic()) && !tactic->isJoin()) {
      if (tactic->isFork())
        throw InputError("Illegal tactic sequence.");
      if (seriesBegin != 0) {
        if (tactic->isBegin())
          throw InputError("Illegal tactic sequence.");
        if (tactic->isEnd()) {
          seriesBegin = 0;
        } else {
          seriesBegin->pushBackTactic(tactic);
        }
      } else {
        actQueue.push_back(tactic);
        if (tactic->isBegin())
          seriesBegin = (Begin *) tactic;
      }
      vector< vector<Key::Type> > const & deps = tactic->dependencies();
      for (vector< vector<Key::Type> >::const_iterator it = deps.begin(); it != deps.end(); ++it) {
        if (depsets.find(*it) != depsets.end()) {
          _dep.push_back(*it);
        }
        depsets.insert(*it);
      }
    }
    delete tactic; // delete the join if tactic != nullptr
    if (verbosity > Options::Terse)
      cout << "Collected " << _dep.size() << " dependencies" << endl;
    _make(true);
    if (verbosity > Options::Silent)
      cout << "Spawning " << actQueue.size() << " threads" << endl;
    // This block contains the multi-threaded code.
    {
      // To avoid mingling output from different threads, write message
      // pieces to local stream and then send to cout only complete
      // messages.
      ostringstream oss;
      // Producers write to promise and consumers read from future.
      // The pair start_promise/start_gun is used to give time to
      // the dispatched of the threads to perform initializations
      // before the engines start.  This function is the producer
      // and the engines are the consumers.
      promise<void> start_promise;
      shared_future<void> start_gun(start_promise.get_future());
      assert(start_gun.valid());
      // The pair promise/future is used to check for termination.
      // The first thread to find a conclusion is the producer.
      promise<int64_t> promise;
      shared_future<int64_t> future(promise.get_future());
      atomic<bool> thatsAllFolks(false);
      assert(future.valid());
      // Threads automatically check the completion future every time
      // they request a new random number.
      Random::set_termination_flag(thatsAllFolks);

      // Unregistering is done by RAII.
      model().bddManager().RegisterTerminationCallback(&callback, &future); 

      // Spawn threads, each running a different "task."
      vector<std::thread> t;
      // This object is destroyed at the end of the enclosing block, at
      // which point all threads still joinable are joined.  We use it
      // for RAII-style exception safety.
      joinThreads joiner(t, model().bddManager(), future, verbosity);

      while (!actQueue.empty()) {
        tactic = actQueue.front();
        actQueue.pop_front();
        t.push_back(std::thread(Engine(tactic, promise, thatsAllFolks, 
				       start_gun))); 
	std::thread::id tid = t.back().get_id();
	if (verbosity > Options::Terse){
	  oss << "Spawning thread: " << hex << tid << endl;
	  cout << oss.str();
	  oss.str("");
	}
      }
      // We are done with initialization.  Fire the gun.
      start_promise.set_value();

      // Wait for the first thread to finish.
      if (verbosity > Options::Silent) {
        oss << "Waiting..." << endl;
        cout << oss.str();
        oss.str("");
      }

      future.wait();
      thatsAllFolks = true;
      if (verbosity > Options::Silent) {
        oss << "Done.  Raw time is: " << future.get() << endl;
        cout << oss.str();
      }
    }
  }


  void Begin::exec() {
    Model::Action * tactic;
    while ((tactic = popTactic())) {
      if (tactic->isJoin() || tactic->isBegin())
        throw InputError("Illegal tactic sequence");
      bool done = tactic->isEnd();
      if (!done) {
        tactic->make();
        ProofAttachment const * pat =
          (ProofAttachment const *) model().constAttachment(Key::PROOF);
        done = pat && pat->hasConclusion();
        model().constRelease(pat);
      }
      delete tactic;
      if (done) {
        break;
      }
    }
  }


  /**
   * Add a tactic to the end of the line.
   */
  void Begin::pushBackTactic(Action * tactic)
  {
    queue.push_back(tactic);
  }


  /**
 * Add a tactic to the beginning of the line.
 */
  void Begin::pushFrontTactic(Action * tactic)
  {
    queue.push_front(tactic);
  }

  /**
   * Dequeue the tactic that is first in line.
   */
  Model::Action * Begin::popTactic()
  {
    if (queue.empty()) return 0;
    Action * tactic = queue.front();
    queue.pop_front();
    return tactic;
  }

  /**
   * Squash remaining tactics.
   */
  void Begin::clearTactics()
  {
    while (!queue.empty()) {
      delete queue.front();
      queue.pop_front();
    }
  }

}
