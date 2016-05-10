/*
 * Revision Control Information
 *
 * $Id: cpu_stats.c,v 1.14 2009/04/18 01:08:05 fabio Exp $
 *
 */
/* LINTLIBRARY */

#include <stdio.h>
#include "util.h"


#include <sys/types.h>
#include <sys/time.h>
#ifdef HAVE_SYS_RESOURCE_H
#  include <sys/resource.h>
#endif

#if defined(_IBMR2)
#define etext _etext
#define edata _edata
#define end _end
#endif

#ifndef __CYGWIN32__
extern int end, etext, edata;
#endif

void
util_print_cpu_stats(FILE *fp)
{
#if HAVE_SYS_RESOURCE_H && !defined(__CYGWIN32__)
    struct rusage rusage;
#ifdef RLIMIT_DATA
    struct rlimit rlp;
    long vm_limit, vm_soft_limit;
#endif
    long text, data;
    double user, system, scale;
    char hostname[257];
#if !defined(__APPLE__)
    long vm_text, vm_init_data, vm_uninit_data, vm_sbrk_data;
#endif

    /* Get the hostname */
    (void) gethostname(hostname, 256);
    hostname[256] = '\0';		/* just in case */

#if !defined(__APPLE__)
    /* Get the virtual memory sizes */
    vm_text = (long) (((long) (&etext)) / 1024.0 + 0.5);
    vm_init_data = (long) (((&edata) - (&etext)) / 1024.0 + 0.5);
    vm_uninit_data = (long) (((&end) - (&edata)) / 1024.0 + 0.5);
    vm_sbrk_data = (long) ((sizeof(char) * ((char *) sbrk(0) - (char *) (&end))) / 1024.0 + 0.5);
#endif

    /* Get virtual memory limits */
#ifdef RLIMIT_DATA /* In HP-UX, with cc, this constant does not exist */
    (void) getrlimit(RLIMIT_DATA, &rlp);
    vm_limit = (long) (rlp.rlim_max / 1024.0 + 0.5);
    vm_soft_limit = (long) (rlp.rlim_cur / 1024.0 + 0.5);
#endif

    /* Get usage stats */
    (void) getrusage(RUSAGE_SELF, &rusage);
    user = rusage.ru_utime.tv_sec + rusage.ru_utime.tv_usec/1.0e6;
    system = rusage.ru_stime.tv_sec + rusage.ru_stime.tv_usec/1.0e6;
    scale = (user + system)*100.0;
    if (scale == 0.0) scale = 0.001;

    (void) fprintf(fp, "Runtime Statistics\n");
    (void) fprintf(fp, "------------------\n");
    (void) fprintf(fp, "Machine name: %s\n", hostname);
    (void) fprintf(fp, "User time   %6.1f seconds\n", user);
    (void) fprintf(fp, "System time %6.1f seconds\n\n", system);

    text = (long) (rusage.ru_ixrss / scale + 0.5);
    data = (long) ((rusage.ru_idrss + rusage.ru_isrss) / scale + 0.5);
    (void) fprintf(fp, "Average resident text size       = %5ldK\n", text);
    (void) fprintf(fp, "Average resident data+stack size = %5ldK\n", data);
    (void) fprintf(fp, "Maximum resident size            = %5ldK\n\n",
	rusage.ru_maxrss/2);
#if !defined(__APPLE__)
    (void) fprintf(fp, "Virtual text size                = %5ldK\n",
	vm_text);
    (void) fprintf(fp, "Virtual data size                = %5ldK\n",
	vm_init_data + vm_uninit_data + vm_sbrk_data);
    (void) fprintf(fp, "    data size initialized        = %5ldK\n",
	vm_init_data);
    (void) fprintf(fp, "    data size uninitialized      = %5ldK\n",
	vm_uninit_data);
    (void) fprintf(fp, "    data size sbrk               = %5ldK\n",
	vm_sbrk_data);
#endif
    /* In some platforms, this constant does not exist */
#ifdef RLIMIT_DATA
    (void) fprintf(fp, "Virtual memory limit             = %5ldK (%ldK)\n\n",
	vm_soft_limit, vm_limit);
#endif
    (void) fprintf(fp, "Major page faults = %ld\n", rusage.ru_majflt);
    (void) fprintf(fp, "Minor page faults = %ld\n", rusage.ru_minflt);
    (void) fprintf(fp, "Swaps = %ld\n", rusage.ru_nswap);
    (void) fprintf(fp, "Input blocks = %ld\n", rusage.ru_inblock);
    (void) fprintf(fp, "Output blocks = %ld\n", rusage.ru_oublock);
    (void) fprintf(fp, "Context switch (voluntary) = %ld\n", rusage.ru_nvcsw);
    (void) fprintf(fp, "Context switch (involuntary) = %ld\n", rusage.ru_nivcsw);
#else /* Do not have sys/resource.h */
    (void) fprintf(fp, "Usage statistics not available\n");
#endif
}
