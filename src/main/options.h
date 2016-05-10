/* -*- C++ -*- */

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

#ifndef _options_
#define _options_

/** @file options.h */

#include <boost/program_options.hpp>
#include <string>
#include <vector>

#include "Model.h"
#include "Verbosity.h"

using namespace std;
using namespace boost::program_options;

/** namespace of program options */
namespace Options {

  /**
   * A class for parsing and storing command line options
   */
  class CommandLineOptions {

  public:

    /**
     * Constructor adds the desired command line options
     */
    CommandLineOptions();

    /**
     * Parses the command line options and stores them in the appropriate
     * member variables
     */
    int parseCommandLineOptions(Model & model, int argc, char * argv[]);

    /**
     * Returns the Tactics specified by the command line, once
     * parseCommandLineOptions has been called.
     */
    vector<Model::Action *> tactics() { return tactics_; }

    /**
     * Returns the boost::program_options::variables_map that
     * indicates the command line options.
     */
    const variables_map & options() { return varMap; }

    /**
     * Get the input file name
     */
    string & inputFile() { return inputFileName; }

    Verbosity verbosity() { return (Verbosity) verbosityLevel; }

  private:
    options_description visible;
    options_description hidden;
    options_description cmdline_options;
    positional_options_description posOpt;
    variables_map varMap;
    
    //Variables that reflect the command line options go here

    /**
     * Input File
     */
    string inputFileName;

    /**
     * Verbosity (integer value).
     */
    int verbosityLevel;

    /**
     * Tactic string and resulting Tactic vector.
     */
    vector<string> tacticSpec_;
    vector<Model::Action *> tactics_;

  };
}

#endif
