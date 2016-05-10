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
#include "AIGER.h"
#include "DIMACS.h"
#include "Util.h"
#include "ExprUtil.h"
#include "ExprAttachment.h"

#include <fstream>
#include <string>
#include <vector>
#include <cstdlib>
#include <boost/program_options.hpp>

using namespace std;

namespace {

  namespace po = boost::program_options;

  typedef po::options_description op_desc;
  typedef po::positional_options_description pos_desc;
  typedef po::variables_map var_map;

  const string default_file_0 = "/examples/aig19/counter3.aig";
  const string default_file_1 = "/examples/dimacs/par8-1-c.cnf";
  pos_desc pos_opt;

  op_desc options()
  {
    op_desc visible("Usage: test_opt [options] file...\nOptions:");
    op_desc hidden;

    pos_opt.add("file",-1);
    visible.add_options()
      ("help,h", "Print this help message")
      ("verbosity,v",po::value<int>()->default_value(0),
     "Set verbosity level (0-4)")
      ("format,m", po::value<size_t>(), "Format of input: 0 for AIGER, 1 for DIMACS");
    hidden.add_options()
      ("file,f", po::value<string>(), "Input file");

    op_desc desc;
    desc.add(visible).add(hidden);
    return desc;
  }

}

void test_AIGER(const string & file, var_map vm, int verbosity) {
  Model model(vm);
  model.attach(new ExprAttachment(model));
  Parser::parseAIGER(file, model);
  if (verbosity) {
    cout << model.string() << endl;
    //  cout << "# of state variables: " << model.stateVars().size() << endl;
  }
}

void test_DIMACS(const string & file, int verbosity) {
  Expr::Manager manager;
  Expr::Manager::View * v = manager.newView();
  SAT::Clauses clauses;
  Parser::parseDIMACS(file, *v, clauses);
  if (verbosity) {
    cout << "#clauses: " << clauses.size() << endl;
    for (size_t i = 0; i < clauses.size(); i++) {
      SAT::Clause & c = clauses[i];
      for (size_t j = 0; j < c.size(); j++)
        cout << Expr::stringOf(*v, c[j]) << " ";
      cout << endl;
    }
  }
  delete v;
}

int main(int argc, char * argv[]) {
  var_map vm;
  op_desc desc = options();
  try {
    po::store(po::command_line_parser(argc, argv).
              options(desc).positional(pos_opt).run(), vm);
  }
  catch(exception const & e) {
    cerr << e.what() << endl;
    return 1;
  }
  po::notify(vm);

  if (vm.count("help")) {
    cout << desc << endl;
    return 0;
  }

  int verbosity = vm["verbosity"].as<int>();

  size_t format = 0;
  if (vm.count("format")) {
    format = vm["format"].as<size_t>();
  }

  try {
    if (vm.count("file")) {
      const string file = vm["file"].as<string>();
      if (format == 0) test_AIGER(file,vm,verbosity);
      else test_DIMACS(file,verbosity);
    } else {
      string srcdir = Util::get_env_var("srcdir");
      const string file_0 = srcdir + default_file_0;
      test_AIGER(file_0,vm,verbosity);
      const string file_1 = srcdir + default_file_1;
      test_DIMACS(file_1,verbosity);
    }
  }
  catch(InputError const & e) {
    cerr << e.what() << endl;
    return 1;
  }

  return 0;
}
