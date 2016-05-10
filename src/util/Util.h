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

#ifndef _Util_
#define _Util_

/** @file Util.h */

#include <string>
#if HAVE_CINTTYPES
#include <cinttypes>
#endif

#include <iostream>

/** Namespace of general utilities. */
namespace Util {
  std::string get_env_var(std::string const& key);
  std::string get_host_name();
  std::string get_os_name();
  std::string get_os_version();
  std::string get_machine();
  long int get_memory_page_size();
  long int get_physical_memory();
  long int get_available_physical_memory();
  long int get_clock_ticks_per_s();
  long int get_maximum_resident_size();
  long int get_major_page_faults();
  long int get_minor_page_faults();
  size_t get_soft_data_limit();
  size_t get_soft_as_limit();
  int64_t get_cpu_time(bool include_children_time = false);
  int64_t get_user_cpu_time(bool include_children_time = false);
  void printSystemInfo(std::ostream& os = std::cout);
  void printCpuTime(std::ostream& os = std::cout);
}

#endif // _Util_
