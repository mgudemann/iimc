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

#ifndef _Error_
#define _Error_

/** @file Error.h */

#include <iostream>
#include <string>

/**
 * Wrapper function for printing error/warning message.
 */
inline void Error(std::string msg) { std::cerr << msg << std::endl; }
/**
 * Wrapper function for printing normal message.
 */
inline void Print(std::string msg) { 
  if (msg != "") std::cout << msg << std::endl; 
}

class Exception {
public:
  Exception(const std::string msg) throw() : _msg(msg) {}
  Exception(const Exception& from) throw() : _msg(from._msg) {}
  std::string what() const { return _msg; }
protected:
  std::string _msg;
};

/** Exception class on input errors. */
class InputError : public Exception {
public: InputError(std::string msg) throw() : Exception(msg) {}
};
/** Exception class on time-out errors. */
class Timeout : public Exception {
public: Timeout(const std::string msg) throw() : Exception(msg) {}
};
/** Exception class on mem-out errors. */
class Memout : public Exception {
public: Memout(std::string msg) throw() : Exception(msg) {}
};
/** Exception class on fatal errors. */
class FatalError : public Exception {
public: FatalError(std::string msg) throw() : Exception(msg) {}
};

#endif // _Error_
