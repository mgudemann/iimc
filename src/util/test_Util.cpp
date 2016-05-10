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

#if HAVE_CONFIG_H
#include "config.h"
#endif

#include "Util.h"

#include <iostream>
#include <string>
#include <algorithm>
#include <iterator>
#if HAVE_CTIME
#include <ctime>
#endif

using namespace std;
using namespace Util;

int main(int argc, char **argv)
{
  clock_t start_time = clock();
  // Echo command line.
  copy(argv, argv+argc, ostream_iterator<string>(cout," "));
  cout << endl;
  // Test various functions.
  string evName("HOME");
  string evValue(get_env_var(evName));
  cout << evName + " = " + evValue << endl;
  evName = "srcdir";
  evValue = get_env_var(evName);
  cout << evName + " = " + evValue << endl;
  evName = "zazzarazzaz";
  evValue = get_env_var(evName);
  cout << evName + " = " + evValue << endl;
  cout << "Host name = " << get_host_name() << endl;
  cout << "OS name = " << get_os_name() << endl;
  cout << "OS version = " << get_os_version() << endl;
  cout << "Machine = " << get_machine() << endl;
  cout << "Page size = " << get_memory_page_size() << endl;
  cout << "Physical memory = " << get_physical_memory() << endl;
  cout << "Available memory = " << get_available_physical_memory() << endl;
  cout << "Soft datasize limit = " << get_soft_data_limit() << endl;
  cout << "Soft address space limit = " << get_soft_as_limit() << endl;
  cout << "Clock ticks per s = " << get_clock_ticks_per_s() << endl;
  cout << "Major page faults = " << get_major_page_faults() << endl;
  cout << "Minor page faults = " << get_minor_page_faults() << endl;
  // Print elapsed CPU time.
  cout << "CPU time (user) = " << get_user_cpu_time() << " us" << endl;
  cout << "CPU time (user + system) = " << get_cpu_time() << " us" << endl;
  cout << "CPU time (clock) = " 
       << ((double) (clock() - start_time)) / CLOCKS_PER_SEC << " s" << endl;
  return 0;
}
