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

#include <iostream>
#include <fstream>
#include <time.h>
#ifndef NOTCOMP
/*
#include <sys/resource.h>
*/
#endif
#include <sys/resource.h>

#include "Error.h"
#include "Key.h"
#include "options.h"
#include "Model.h"
#include "ProofAttachment.h"
#include "RchAttachment.h"
#include "SeqAttachment.h"
#include "Random.h"

using namespace std;
using namespace boost::program_options;
using namespace Options;

namespace {

/** Apply tactics to model. */
void dispatcher(Model & model) {

  Model::Action * tactic;
  while ((tactic = model.popTactic())) {
    tactic->make();
    delete tactic;
    ProofAttachment const * const pat = (ProofAttachment const *) model.constAttachment(Key::PROOF);
    bool done = pat && pat->hasConclusion();
    model.constRelease(pat);
    if (done) {
      model.clearTactics();
      break;
    }
  }
}

}

int main(int argc, char * argv[]) {

#ifndef NOTCOMP
  /*
  rlimit rl;
  int result;
  result = getrlimit(RLIMIT_STACK, &rl);
  //cout << "rlim_cur: " << rl.rlim_cur << endl;
  //cout << "rlim_max: " << rl.rlim_max << endl;
  assert(result == 0);
  if (rl.rlim_cur == RLIM_INFINITY) {
    rl.rlim_cur = 1073741824L;
    result = setrlimit(RLIMIT_STACK, &rl);
    assert(result == 0);
    string call;
    for (int i = 0; i != argc; ++i) {
      call += argv[i];
      call += " ";
    }
    int ret = system(call.c_str());
    return ret;
  }
  */
#endif

  const rlim_t kStackSize = 32L * 1024L * 1024L;
  rlimit rl;
  int result;
  result = getrlimit(RLIMIT_STACK, &rl);
  cout << "rlim_cur: " << rl.rlim_cur << endl;
  cout << "rlim_max: " << rl.rlim_max << endl;
  assert(result == 0);
  if(rl.rlim_cur<kStackSize)
  {
    rl.rlim_cur = kStackSize;
    result = setrlimit(RLIMIT_STACK, &rl);
    assert(result == 0);
    cout << "rlim_new: " << kStackSize << endl;
  }

  CommandLineOptions options;
  Model model(options.options(), "main");

  int status;
  try {
    status = options.parseCommandLineOptions(model, argc, argv);
  }
  catch(InputError const & ie) {
    cerr << ie.what() << endl;
    return 1;
  }

  model.setVerbosity(
    options.options().count("verbosity") 
    ? (Options::Verbosity) options.options()["verbosity"].as<int>()
    : Options::Informative);
  // Echo command line.
  if (model.verbosity() > Options::Terse) {
    cout << "#";
    for (int i = 0; i != argc; ++i)
      cout << " " << argv[i];
    cout << endl;
  }

  if (status != 0)
    return status;

  int rseed = options.options()["rand"].as<int>();
  Random::register_thread();
  if (rseed == -1) {
    // sets initial random seed for all threads
    Random::set_seed(time(0));
  }

  int ret = 1;
  try { 
    dispatcher(model);
    ret = 0;
  } catch (Exception const & e) {
    cerr << e.what() << endl;
  } catch (...) {
  }

  auto pat = model.attachment<ProofAttachment>(Key::PROOF);
  if (pat) {
    //Acquire RchAttachment in write-mode to lock out everybody else trying to
    //write a u-line
    auto rat = model.attachment<RchAttachment>(Key::RCH);
    if(!(pat->conclusion() == 1 && options.options().count("print_cex")))
      pat->printConclusion();
    if(pat->conclusion() == 0 && options.options().count("print_proof")) {
      pat->addEquivalenceInfo();
      if(options.options().count("proof_file")) {
        string filename = options.options()["proof_file"].as<string>();
        ofstream proofFile(filename.c_str());
        pat->printProof(proofFile);
        proofFile.close();
      }
      else {
        pat->printProof();
      }
    }
    else if(pat->conclusion() == 1 && options.options().count("print_cex")) {
      pat->produceEvidenceForFailure();
    }
    model.release(rat);
  }
  model.release(pat);

#if 1
  return ret;
#else
  exit(ret);
#endif
}
