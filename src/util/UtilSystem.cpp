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

#if HAVE_CONFIG_H
#include "config.h"
#endif

#include "Util.h"

#include <iostream>
#include <string>

#if HAVE_CSTDLIB
#include <cstdlib>
#endif

#if HAVE_UNISTD_H
#include <unistd.h>
#endif

#if HAVE_CTIME
#include <ctime>
#endif

#if HAVE_SYS_UTSNAME_H
#include <sys/utsname.h>
#endif

#if HAVE_SYS_RESOURCE_H
#include <sys/resource.h>
#endif

using namespace std;

namespace Util {

  /** 
   * Read an environment variable into a string.
   * Return the empty string if the variable is undefined or if the
   * query is not supported by the implementation.
   * @param key the name of the environment variable
   */
  string get_env_var(string const& key)
  {
    char* val = 0;
#if HAVE_GETENV && HAVE_CSTDLIB
    val = getenv(key.c_str());
#endif
    string retval = "";
    if (val != 0) {
      retval = val;
    }
    return retval;
  }

  /** 
   * Return host name as a string.
   * Return "unknown" if the query fails or is not supported by the
   * implementatation.
   */
  string get_host_name()
  {
    string retval = "unknown";
#if HAVE_UNAME && HAVE_SYS_UTSNAME_H
    struct utsname info;
    int status = uname(&info);
    if (status == 0) {
      retval = info.nodename;
    }
#elif HAVE_GETHOSTNAME && HAVE_UNISTD
    // If name is longer than length-1, it is truncated.
    const size_t length = 1024;
    char name_array[length];
    int status = gethostname(name_array,length);
    if (status == 0) {
      retval = name_array;
    }
#endif
    return retval;
  }

  /**
   * Return the operating system name.
   * Return "undefined" if the query fails or is not supported
   * by the implementation.
   * @see get_os_version
   */
  string get_os_name()
  {
    string retval = "undefined";
#if HAVE_UNAME && HAVE_SYS_UTSNAME_H
    struct utsname info;
    int status = uname(&info);
    if (status == 0) {
      retval = info.sysname;
    }
#endif
    return retval;
  }

  /**
   * Return the operating system version.
   * Return "undefined" if the query fails or is not supported
   * by the implementation.
   * @see get_os_name
   */
  string get_os_version()
  {
    string retval = "undefined";
#if HAVE_UNAME && HAVE_SYS_UTSNAME_H
    struct utsname info;
    int status = uname(&info);
    if (status == 0) {
      retval = info.version;
    }
#endif
    return retval;
  }

  /**
   * Return the hardware identifier.
   * Return "undefined" if the query fails or is not supported
   * by the implementation.  The hardware identifier is something
   * like "i686."
   */
  string get_machine()
  {
    string retval = "undefined";
#if HAVE_UNAME && HAVE_SYS_UTSNAME_H
    struct utsname info;
    int status = uname(&info);
    if (status == 0) {
      retval = info.machine;
    }
#endif
    return retval;
  }

  /**
   * Return memory page size in bytes.
   * Return 0 if the query is not supported by the implementation.
   */
  long int get_memory_page_size()
  {
#if HAVE_SYSCONF && HAVE_UNISTD_H
    return sysconf(_SC_PAGESIZE);
#else
    return 0;
#endif
  }

  /**
   * Return the amount of physical memory in bytes. 
   * Return 0 if the query is not supported by the implementation.
   */
  long int get_physical_memory()
  {
    long int ret = 0;
#if HAVE_SYSCONF && HAVE_UNISTD_H && HAVE_DECL__SC_PAGESIZE && HAVE_DECL__SC_PHYS_PAGES
    ret = sysconf(_SC_PHYS_PAGES);
    if (ret >= 0)
      ret *= sysconf(_SC_PAGESIZE);
#endif
    return ret;
  }

  /**
   * Return the amount of available physical memory in bytes.
   * Return 0 if the query is not supported by the implementation.
   */
  long int get_available_physical_memory()
  {
    long int ret = 0;
#if HAVE_SYSCONF && HAVE_UNISTD_H && HAVE_DECL__SC_PAGESIZE && HAVE_DECL__SC_AVPHYS_PAGES
    ret = sysconf(_SC_AVPHYS_PAGES);
    if (ret >= 0)
      ret *= sysconf(_SC_PAGESIZE);
#endif
    return ret;
  }

  /**
   * Return the number of clock ticks per second.
   * Return 0 if the query is not supported by the implementation.
   */
  long int get_clock_ticks_per_s()
  {
#if HAVE_CTIME
    return CLOCKS_PER_SEC;
#elif HAVE_SYSCONF && HAVE_UNISTD_H
    return sysconf(_SC_CLK_TCK);
#else
    return 0;
#endif
  }

  /**
   * Return maximum resident size of the process in bytes.
   */
  long int get_maximum_resident_size()
  {
#if HAVE_GETRUSAGE && HAVE_SYS_RESOURCE_H
    struct rusage usage;
    int status = getrusage(RUSAGE_SELF,&usage);
    if (status == 0) {
      return usage.ru_maxrss * 1024;
    }
#endif
    return -1;
  }

  /**
   * Return number of major page faults.
   * Return -1 if the query is not supported by the implementation.
   */
  long int get_major_page_faults()
  {
#if HAVE_GETRUSAGE && HAVE_SYS_RESOURCE_H
    struct rusage usage;
    int status = getrusage(RUSAGE_SELF,&usage);
    if (status == 0) {
      return usage.ru_majflt;
    }
#endif
    return -1;
  }

  /**
   * Return number of minor page faults.
   * Return -1 if the query is not supported by the implementation.
   */
  long int get_minor_page_faults()
  {
#if HAVE_GETRUSAGE && HAVE_SYS_RESOURCE_H
    struct rusage usage;
    int status = getrusage(RUSAGE_SELF,&usage);
    if (status == 0) {
      return usage.ru_minflt;
    }
#endif
    return -1;
  }

  /**
   * Return soft data limit.
   * Return 0 if the query is not supported by the implementation.
   */
  size_t get_soft_data_limit()
  {
#if HAVE_GETRLIMIT && HAVE_SYS_RESOURCE_H
    struct rlimit rlim;
    int status = getrlimit(RLIMIT_DATA,&rlim);
    if (status == 0 && rlim.rlim_cur != RLIM_INFINITY) {
      return rlim.rlim_cur;
    }
#endif
    return 0;
  }

  /**
   * Return soft address space limit.
   * Return 0 if the query is not supported by the implementation.
   */
  size_t get_soft_as_limit()
  {
#if HAVE_GETRLIMIT && HAVE_SYS_RESOURCE_H
    struct rlimit rlim;
    int status = getrlimit(RLIMIT_AS,&rlim);
    if (status == 0 && rlim.rlim_cur != RLIM_INFINITY) {
      return rlim.rlim_cur;
    }
#endif
    return 0;
  }

  /**
   * Return user and system CPU time for this process.
   * Return -1 in case of failure or if the implementation does
   * not support the query.  Time is measured in microseconds.
   * @param include_children_time include the time spent by the children processes that have terminated
   * @see get_user_cpu_time
   */
  int64_t get_cpu_time(bool include_children_time)
  {
#if HAVE_GETRUSAGE && HAVE_SYS_RESOURCE_H
    struct rusage ru;
    int status = getrusage(RUSAGE_SELF,&ru);
    if (status == 0) {
      int64_t cpu_time = (int64_t) ru.ru_utime.tv_sec * 1000000;
      cpu_time += (int64_t) ru.ru_utime.tv_usec;
      cpu_time += (int64_t) ru.ru_stime.tv_sec * 1000000;
      cpu_time += (int64_t) ru.ru_stime.tv_usec;
      if (include_children_time) {
        status = getrusage(RUSAGE_CHILDREN,&ru);
        if (status != 0) {
          return -1;
        }
        cpu_time += (int64_t) ru.ru_utime.tv_sec * 1000000;
        cpu_time += (int64_t) ru.ru_utime.tv_usec;
        cpu_time += (int64_t) ru.ru_stime.tv_sec * 1000000;
        cpu_time += (int64_t) ru.ru_stime.tv_usec;
      }
      return cpu_time;
    }
#endif
    return -1;
  }

  /**
   * Return user CPU time for this process.
   * Return -1 in case of failure or if the implementation does
   * not support the query.  Time is measured in microseconds.
   * @param include_children_time include the time spent by the children processes that have terminated
   * @see get_cpu_time
   */
  int64_t get_user_cpu_time(bool include_children_time)
  {
#if HAVE_GETRUSAGE && HAVE_SYS_RESOURCE_H
    struct rusage ru;
    int status = getrusage(RUSAGE_SELF,&ru);
    if (status == 0) {
      int64_t cpu_time = (int64_t) ru.ru_utime.tv_sec * 1000000;
      cpu_time += (int64_t) ru.ru_utime.tv_usec;
      if (include_children_time) {
        status = getrusage(RUSAGE_CHILDREN,&ru);
        if (status != 0) {
          return -1;
        }
        cpu_time += (int64_t) ru.ru_utime.tv_sec * 1000000;
        cpu_time += (int64_t) ru.ru_utime.tv_usec;
      }
      return cpu_time;
    }
#endif
    return -1;
  }

  /**
   * Print system information.
   */
  void printSystemInfo(ostream& os)
  {
    os << "Host name (machine type) = " << get_host_name() << " ("
       << get_machine() << ")" << endl;
    os << "OS = " << get_os_name() << " " << get_os_version() << endl;
    os << "Physical memory = " << get_physical_memory() << endl;
    os << "Maximum resident size = " << get_maximum_resident_size() << endl;
    os << "Soft datasize/address space limit = " << get_soft_data_limit() << "/"
       << get_soft_as_limit() << endl;
    os << "Page faults (major/minor) = " << get_major_page_faults() << "/"
       << get_minor_page_faults() << endl;
    os << "CPU time (user + system) = " << ((double) get_cpu_time()/1000000.0) 
       << " s" << endl;
  }

  /**
   * Print CPU time.
   */
  void printCpuTime(ostream& os)
  {
    os << "CPU time (user + system) = " << ((double) get_cpu_time()/1000000.0) 
       << " s" << endl;
  }

}
