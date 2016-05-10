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
#include "AutoDriver.h"

using namespace std;
using namespace Expr;

void build(Model& model);

namespace bpo = boost::program_options;

int
main(int argc, char *argv[])
{
  try {
    // Set up options.  See boost::program_options tutorial.
    bpo::options_description visible("Allowed options");
    visible.add_options()
      ("help,h", "write this help message")
      ("trace_parsing,p", "trace parsing")
      ("trace_scanning,s", "trace scanning")
      ("dot,d", "print automaton in dot format")
      ("verbosity,v", 
       bpo::value<int>()->default_value(0),
       "Set verbosity level (0-4)")
      ;
    bpo::options_description hidden("Hidden options");
    hidden.add_options()
      ("input-file",
       bpo::value<string>(),
       "input file")
      ;
    bpo::options_description cmdline_options;
    cmdline_options.add(visible).add(hidden);
    bpo::positional_options_description pod;
    pod.add("input-file", -1);
    bpo::variables_map vm;
    bpo::store(bpo::command_line_parser(argc, argv).options(cmdline_options).positional(pod).run(), vm);
    bpo::notify(vm);
    if (vm.count("help")) {
      cout << "Usage: " << argv[0] << " [options] file\n";
      cout << visible << "\n";
      return 0;
    }

    // Build model.
    Model model(vm, "test");
    Options::Verbosity verbosity = vm.count("verbosity")
      ? (Options::Verbosity) vm["verbosity"].as<int>()
      : Options::Silent;
    model.setVerbosity(verbosity);
    model.attach(new ExprAttachment(model));
    build(model);

    // Create parser and use it.
    auto eat = model.attachment<ExprAttachment>(Key::EXPR);
    auto_driver driver(eat.operator->());
    if (vm.count("trace_parsing"))
      driver.trace_parsing = true;
    if (vm.count("trace_scanning"))
      driver.trace_scanning = true;
    string filename;
    if (vm.count("input-file")) {
      filename = vm["input-file"].as<string>();
      assert(filename.size() != 0);
    } else {
      cout << "Error: Missing file name.\n";
      cout << "Usage: " << argv[0] << " [options] file\n";
      cout << visible << "\n";
      return 1;
    }
    if (!driver.parse(filename)) {
      const vector<Automaton>& automata = eat->automata();
      if (verbosity > Options::Silent) {
        for (size_t index = 0; index < automata.size(); ++index)
          cout << driver.toString(index) << endl;
      }
      if (vm.count("dot")) {
        for (size_t index = 0; index < automata.size(); ++index)
          cout << driver.toDot(index) << endl;
      }
    }
    model.release(eat);
    if (verbosity > Options::Terse) {
      cout << model.string(true);
    }
    return 0;
  } catch(exception const & e) {
    cout << e.what() << "\n";
    return 1;
  }
} // main


/**
 * Create model with three inputs, two state variables and two outputs.
 */
void build(Model& model)
{
  auto eat = model.attachment<ExprAttachment>(Key::EXPR);
  assert(eat != 0);
  Manager::View *v = model.newView();
  v->begin_local();
  vector<ID> w;
  w.push_back(v->newVar("i0"));
  w.push_back(v->newVar("i1"));
  w.push_back(v->newVar("i2"));
  eat->addInputs(w);
  ID x0 = v->newVar("l0");
  ID x1 = v->newVar("l1");
  ID f0 = v->apply(Or, w[0], w[1]);
  ID f1 = v->apply(And, w[2], x0);
  eat->setNextStateFn(x0,f0);
  eat->setNextStateFn(x1,f1);
  vector<ID> z;
  z.push_back(v->newVar("o0"));
  z.push_back(v->newVar("o1"));
  vector<ID> l;
  l.push_back(v->apply(And, x0, v->apply(Not, x1)));
  l.push_back(f1);
  eat->setOutputFns(z,l);
  ID init = v->apply(And, v->apply(Not, x0), v->apply(Not, x1));
  eat->addInitialCondition(init);
  ID buechi = v->apply(Not, v->apply(And, x0, x1));
  eat->addFairnessConstraint(buechi);
  // Commit and clean up.
  eat->global(v);
  v->end_local();
  eat->keep(v);
  v->clean();
  delete v;
  model.release(eat);

} // build
