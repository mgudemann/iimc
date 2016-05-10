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

#include "config.h"
#include <iostream>
#include <vector>

#include "CutSweep.h"
#include "BddReach.h"
#include "BMC.h"
#include "COI.h"
#include "IC3.h"
#include "IIC.h"
#include "Error.h"
#include "Expr.h"
#include "ExprUtil.h"
#include "Fair.h"
#include "FSIS.h"
#include "options.h"
#include "SAT.h"
#include "SATSweep.h"
#include "SequentialEquivalence.h"
#include "StuckAt.h"
#include "TacticMisc.h"
#include "CNFTestAction.h"
#include "CNFDummyAction.h"
#include "DIMACSAction.h"

using namespace std;
using namespace boost::program_options;

namespace {
  enum Filetype { AIGER };

  // Returns the Filetype based on the filename's extension.
  Filetype filetype(string name) {
    size_t dotp = name.find_last_of('.');
    if (dotp == name.npos || dotp == name.size()-1)
      throw InputError("File " + name + " lacks an extension.  Cannot determine filetype.");
    string extension = name.substr(dotp+1, name.size()-dotp-1);
    if (extension == "aig" || extension == "aag")
      return AIGER;
    throw InputError("The filetype of " + name + ", as indicated by its extension, is unknown.");
  }
}

namespace Options {

  /**
   * Constructor adds the desired command line options
   */
  CommandLineOptions::CommandLineOptions() : visible("iimc Usage: \
  ./iimc <Input File> [OPTIONS] \nOptions") {

    //Add the input file option as a positional option (i.e., last argument
    //passed which doesn't need a --option_name)
    posOpt.add("input-file", -1);

    //Add the options
    visible.add_options()
      ("help,h", "Print this help message")

      ("version,V", "Print version information")

      ("verbosity,v", 
       value<int>(&verbosityLevel)->default_value(0),
       "Set verbosity level (0-4)")

      ("print_cex",
       "Print counterexample trace if property fails")

      ("cex_file",
       value<string>(),
       "File to print counterexample trace to. If option not specified, counterexample is printed to stdout")

      ("xmap_cex",
       "Disable mapping counterexample back to original model")

      ("print_proof",
       "Print one-step inductive strengthening of the property obtained by IC3 if property holds")

      ("proof_file",
       value<string>(),
       "File to print proof CNF to. If option not specified, proof is printed to stdout")

      ("improve_proof",
       value<int>(),
       "Post-process proof obtained by IC3. Argument is a number (0-2) for selecting type of post-processing: 0 for strengthening the proof, 1 for weakening the proof, and 2 for minimizing the proof")

      ("print_info,p",
       "Print system info")

      ("rand,r",
       value<int>()->default_value(-1),
       "Control random initialization.  Set to -1 to use the clock.")

      ("tactic,t",
       value< vector<string> >(&tacticSpec_),
       "Specify a tactic sequence")

      ("bmc_bound",
       value<unsigned int>()->default_value(1000),
       "BMC option: set bound for k")

      ("bmc_isim",
       "BMC option: expand initial condition through simulation")

      ("bmc_timeout",
       value<int>()->default_value(30),
       "BMC option: set timeout")

      ("ic3_nRuns",
       value<unsigned int>()->default_value(20),
       "IC3 option: number of simulation runs for equivalence")

      ("ic3_xeqprop",
       "IC3 option: disable equivalence propagation")

      ("ic3_xbddInit",
       "IC3 option: disable BDD initial expansion")

      ("ic3_aeq",
       "IC3 option: enable augmented equivalence propagation")

      ("ic3_ms",
       value<unsigned int>()->default_value(10000),
       "IC3 option: maximum number of part size to allow equivalence propagation")

      ("ic3_sccH",
       "IC3 option: use SCC heuristic")

      ("ic3_timeout",
       value<int>()->default_value(-1),
       "ic3 option: set timeout")

      ("ic3r_timeout",
       value<int>()->default_value(20),
       "ic3r option: set timeout")

      ("ic3_lift",
       "ic3 option: lift CTIs")

      ("ic3_laggr",
       value<int>()->default_value(0),
       "ic3 option: Aggression level for lifting CTIs")

      ("ic3_inf",
        "ic3 option: Check for truly inductive clauses and store them separately")

       ("ic3_weak_inf",
        "ic3 option: Check for truly inductive clauses and store them separately without interfering with IC3's normal operation. Is not useful unless used in conjunction with ic3_lift")

       ("ic3_try_unlifted",
        "ic3 option: If lifting is enabled, try inductiveness of unlifted cube as well and take the most forward of the two (lifted and unlifted)")

       ("ic3_stats",
        "ic3 option: Extract and print statistics about the ic3 run")
 
      ("fair_xincr",
       "FAIR Option: Disable incremental use of IC3")

      ("ctl",
       value<std::string>(),
       "CTL property file")

      ("parse_graph",
       "print the parse graph of the property in dot format")

      ("fsis_disable_lifting",
       "FSIS option: disable lifting of CTI state")

      ("fsis_subsum_freq",
       value<int>()->default_value(100),
       "FSIS option: how often to apply subsumption on discovered clauses. Use 0 for no subsumption.")

      // AARON 9/25: setting default to 10
      ("satsweep_timeout",
       value<int>()->default_value(10),
       "Time limit for SAT sweeping (in s)")

      ("satsweep_satTimeout",
       value<double>()->default_value(0.1),
       "SAT Sweeping: time limit for SAT solver after which class is dropped (in s)")

      ("satsweep_verbosity",
       value<int>(),
       "SAT sweep option: verbosity level for SAT sweeping (0-4)")

      ("satsweep_numIters",
       value<unsigned>()->default_value(30),
       "SAT sweeping option: terminate initial refinement if no changes in node equivalence classes occur for numIters successive iterations")

      ("satsweep_depthQuantiles",
       value<unsigned>()->default_value(4),
       "SAT sweeping option: the number of depth quantiles to use for limiting the depth of the nodes on which a SAT query is performed")

      ("satsweep_verify",
       "SAT sweeping option: verify the correctness of simplification by checking the equivalence of the two circuits")

      ("satsweep_assumeProperty",
       "SAT sweeping option: assume property while sweeping")

      ("cutsweep_nodeMax",
       value<int>(),
       "Cut sweep option: specify the maximal number of BDD nodes in a cut")

      ("cutsweep_cutMax",
       value<int>(),
       "Cut sweep option: specify the number of cuts kept besides the singleton cut")

      ("cutsweep_timeout",
       value<int>(),
       "Time limit for Cut sweeping (in s)")

      ("cutsweep_verbosity",
       value<int>(),
       "Cut sweep option: verbosity level for cut sweeping (0-4)")

      ("bdd_sweeping",
       "Merge equivalent node pairs during BDD construction")

      ("bdd_reorderings",
       value<unsigned int>(),
       "Maximum number of dynamic BDD variable reordering")

      ("bdd_order",
       value<std::string>(),
       "File containing a variable order")

      ("bdd_static",
       value<std::string>()->default_value("interleaving"),
       "Static ordering algorithm (interleaving, plain, linear)")

      ("bdd_rand",
       value<unsigned int>(),
       "BDD reorderinng randomization factor")

      ("bdd_threshold",
       value<unsigned int>()->default_value(2000),
       "Size limit for introduction of auxiliary variables")

      ("bdd_timeout",
       value<unsigned long>()->default_value(90),
       "Time limit for BDD construction (in s)")

      ("bdd_tr_timeout",
       value<unsigned long>(),
       "Time limit for BDD transition relation construction (in s)")

      ("bdd_fw_timeout",
       value<unsigned long>()->default_value(90),
       "Time limit for BDD-based forward analysis (in s)")

      ("bdd_bw_timeout",
       value<unsigned long>(),
       "Time limit for BDD-based backward analysis (in s)")

      ("bdd_tr_cluster",
       value<unsigned int>()->default_value(2500),
       "Size limit for transition relation clusters")

      ("bdd_mf",
       "Minimize frontier during BDD-based reachability analysis")

      ("bdd_group",
       "Use the group sifting reordering algorithm")

      ("bdd_trav",
       "Ignore property failure in BDD forward reachability analysis")

      ("bdd_save_fw_reach",
       "Save BDD for reachable states after successful reachability analysis")

      ("bdd_info",
       "Add BDD info to summary")

      ("bdd_sw_threshold",
       value<unsigned int>()->default_value(250),
       "Size limit for introduction of auxiliary variables during sweeping")

      ("bdd_sw_reorderings",
       value<unsigned int>()->default_value(0),
       "Maximum number of dynamic BDD variable reordering during sweeping")

      ("bdd_sw_timeout",
       value<unsigned long>(),
       "Time limit for BDD sweeping (in s)")

      ("tmcnf_k", value<unsigned>()->default_value(8),
       "Technology Mapping CNF Conversion: maximum cut size")

      ("tmcnf_l", value<unsigned>()->default_value(5),
       "Technology Mapping CNF Conversion: keep the best l cuts")

      ("tmcnf_refinements", value<unsigned>()->default_value(0),
       "Technology Mapping CNF Conversion: perform n refinement passes")

      ("cnf_techmap", "Use technology mapping for CNF conversion")

      ("cnf_nice", "Use NICE DAGs for CNF conversion")

      ("nice_k", value<unsigned>()->default_value(2), "Limit for k-limited mergin")

      ("nice_limit", value<unsigned>()->default_value(50), "Limit for number of clauses for a node before variable introduction")

      ("cnf_simp_disable", "Disable CNF simplifier")

      ("cnf_timeout", value<double>(), "Maximum time for hard effort CNF conversion.  After timeout, it will still produce correct CNF.")

      ("fair_k", value<int>()->default_value(1), "fair option: set K for query")

      ("pi", value<unsigned>()->default_value(0), "Property index")
      ;
    hidden.add_options()
      ("input-file", value<string>(&inputFileName), "Input file");
    cmdline_options.add(visible).add(hidden);
  }

  int CommandLineOptions::parseCommandLineOptions(Model& model, int argc, char * argv[]) {

    // Set-up.
    try {

      store(command_line_parser(argc, argv).options(
      cmdline_options).positional(posOpt).run(), varMap);
    }
    catch(exception& e) {
      cout << e.what() << endl;
      return 1;
    }

    notify(varMap);

    // Process options that cause immediate return.
    if(varMap.count("help")) {
      cout << visible << endl;
      return 1;
    }

    if (varMap.count("version")) {
      cout << PACKAGE_STRING << endl;
      return 1;
    }

    // Check remaining options.
    int ret = 0;

    if (varMap.count("verbosity")) {
      if (verbosityLevel < 0 || verbosityLevel > 4) {
        cout << "Error: Verbosity level (" << verbosityLevel 
             << ") out of range (0-4)" << endl;
        ret |= 1;
      }
    }

    if (varMap.count("improve_proof")) {
      int type = varMap["improve_proof"].as<int>();
      if (type < 0 || type > 2) {
        cout << "Error: Type of proof post-processing (" << type << ") out of range (0-2)" << endl;
        ret |= 1;
      }
    }

    if (varMap.count("satsweep_verbosity")) {
      int satsweepVerbosityLevel = varMap["satsweep_verbosity"].as<int>();
      if (satsweepVerbosityLevel < 0 || satsweepVerbosityLevel > 4) {
        cout << "Error: SAT Sweep Verbosity level (" << satsweepVerbosityLevel 
             << ") out of range (0-4)" << endl;
        ret |= 1;
      }
    }

    if(varMap.count("input-file")) {
      if (inputFileName == "") {
        cout << "Error: Empty file name" << endl;
        ret |= 1;
      } else {
        if (verbosityLevel > 0)
          cout << "Input File is " << inputFileName << endl;
        Filetype ft = filetype(inputFileName);
        assert(ft == AIGER); // filetype throws exception otherwise
      }
    }
    else {
      cout << "Error: Input file missing" << endl << endl; 
      ret |= 1;
    }

    if (ret != 0) {
      cout << visible << endl;
      return ret;
    }

    /* Register tactics. */
    bool standard = false;
    tactics_.push_back(new IIC::FixRoots(model));
    if (varMap.count("tactic")) {
      for (vector<string>::iterator it = tacticSpec_.begin();
           it != tacticSpec_.end(); it++) {
        Model::Action *t;
        if      (*it == "bmc")             t = new BMC::BMCAction(model);
        else if (*it == "ic3")             t = new IC3::IC3Action(model);
        else if (*it == "ic3r")            t = new IC3::IC3Action(model, true);
        else if (*it == "fsis")            t = new FSIS::FSISAction(model);
        else if (*it == "bdd_build")       t = new BddBuildAction(model);
        else if (*it == "bdd_fw_reach")    t = new BddFwReachAction(model);
        else if (*it == "bdd_bw_reach")    t = new BddBwReachAction(model);
        else if (*it == "bddsweep")        t = new BddSweepAction(model);
        else if (*it == "print_expr")      t = new PrintExprAction(model);
        else if (*it == "print_dot")       t = new PrintDotAction(model);
        else if (*it == "print_graph")     t = new PrintCircuitGraphAction(model);
        else if (*it == "print_scc_graph") t = new PrintCircuitSccGraph(model);
        else if (*it == "print_verilog")   t = new PrintVerilogAction(model);
        else if (*it == "print_blif_mv")   t = new PrintBlifMvAction(model);
        else if (*it == "print_expr_info") t = new PrintExprInfo(model);
        else if (*it == "print_expr_size") t = new PrintExprSize(model);
        else if (*it == "sccs")            t = new AnalyzeSccs(model);
        else if (*it == "cnftest")         t = new CNF::CNFTestAction(model);
        else if (*it == "cnfdummy")        t = new CNF::CNFDummyAction(model);
        else if (*it == "cutsweep")        t = new Action::CutSweepAction(model);
        else if (*it == "satsweep")        t = new Action::SATSweepAction(model);
        else if (*it == "coi")             t = new COIAction(model);
        else if (*it == "se")              t = new SequentialEquivalenceAction(model);
        else if (*it == "stuck")           t = new StuckAtAction(model);
        else if (*it == "sr")            {
          tactics_.push_back(new COIAction(model));
          tactics_.push_back(new StuckAtAction(model));
          tactics_.push_back(new SequentialEquivalenceAction(model));
          t = new COIAction(model);
        }
        else if (*it == "print_info")      t = new PrintSystemInfoAction(model);
        else if (*it == "print_time")      t = new PrintCpuTimeAction(model);
        else if (*it == "conclude")        t = new Conclusion(model);
        else if (*it == "dimacs")          t = new CNF::DIMACSAction(model);
        else if (*it == "fair")            t = new Fair::FairAction(model);
        else if (*it == "check")           t = new IIC::IICAction(model);
        else if (*it == "standard")        standard = true;
        else throw InputError("Unknown tactic: " + *it);
        if(!standard)
          tactics_.push_back(t);
      }
    }
    else standard = true;

    if (standard) {
      tactics_.push_back(new COIAction(model));
      tactics_.push_back(new StuckAtAction(model));
      tactics_.push_back(new SequentialEquivalenceAction(model));
      tactics_.push_back(new COIAction(model));
      tactics_.push_back(new BddSweepAction(model));
      tactics_.push_back(new Action::SATSweepAction(model));
      tactics_.push_back(new StuckAtAction(model));
      tactics_.push_back(new SequentialEquivalenceAction(model));
      tactics_.push_back(new COIAction(model));
      tactics_.push_back(new IIC::IICAction(model));
    }

    return 0;
  }

}
