/**CFile***********************************************************************

  FileName    [ cpu_time.c ]

  PackageName [ util ]

  Synopsis    [ System time calls ]

  Description [ The problem is that all unix systems have a different notion
		of how fast time goes (i.e., the units returned by).  This
		returns a consistent result. ]

  Author      [ Stephen Edwards <sedwards@eecs.berkeley.edu> and others ]

  Copyright   [Copyright (c) 1994-1996 The Regents of the Univ. of California.
  All rights reserved.

  Permission is hereby granted, without written agreement and without license
  or royalty fees, to use, copy, modify, and distribute this software and its
  documentation for any purpose, provided that the above copyright notice and
  the following two paragraphs appear in all copies of this software.

  IN NO EVENT SHALL THE UNIVERSITY OF CALIFORNIA BE LIABLE TO ANY PARTY FOR
  DIRECT, INDIRECT, SPECIAL, INCIDENTAL, OR CONSEQUENTIAL DAMAGES ARISING OUT
  OF THE USE OF THIS SOFTWARE AND ITS DOCUMENTATION, EVEN IF THE UNIVERSITY OF
  CALIFORNIA HAS BEEN ADVISED OF THE POSSIBILITY OF SUCH DAMAGE.

  THE UNIVERSITY OF CALIFORNIA SPECIFICALLY DISCLAIMS ANY WARRANTIES,
  INCLUDING, BUT NOT LIMITED TO, THE IMPLIED WARRANTIES OF MERCHANTABILITY AND
  FITNESS FOR A PARTICULAR PURPOSE.  THE SOFTWARE PROVIDED HEREUNDER IS ON AN
  "AS IS" BASIS, AND THE UNIVERSITY OF CALIFORNIA HAS NO OBLIGATION TO PROVIDE
  MAINTENANCE, SUPPORT, UPDATES, ENHANCEMENTS, OR MODIFICATIONS.]

******************************************************************************/

#include "util.h"

#if HAVE_SYS_TYPES_H
#  include<sys/types.h>
#endif

#if HAVE_SYS_TIMES_H
#  include<sys/times.h>
#endif

/**AutomaticStart*************************************************************/

/*---------------------------------------------------------------------------*/
/* Static function prototypes                                                */
/*---------------------------------------------------------------------------*/

/**AutomaticEnd***************************************************************/

/**Function********************************************************************

  Synopsis           [ Return elapsed time in milliseconds. ]

  Description        [ Return an unsigned long which represents the elapsed
                       time in milliseconds since some constant reference. ]

  SideEffects        [ none ]

******************************************************************************/
unsigned long 
util_cpu_time(void)
{
#if HAVE_SYSCONF == 1

    /* Code for POSIX systems */

    struct tms buffer;
    long nticks;                /* number of clock ticks per second */

    nticks = sysconf(_SC_CLK_TCK);
    times(&buffer);
    return (unsigned long) (buffer.tms_utime * (1000.0/nticks));

#else
    return 0UL;
#endif /* HAVE_SYSCONF == 1 */

}

/**Function********************************************************************

  Synopsis           [ Return elapsed time in milliseconds. It includes waited-
                       for terminated children. ]

  Description        [ Return a long which represents the elapsed time in
		       milliseconds since some constant reference. This time
                       includes the CPU time spent executing instructions of
		       the calling process and the time this process waited
		       for its children to be terminated. ]

  SideEffects        [ none ]

******************************************************************************/
unsigned long
util_cpu_ctime(void)
{
#if HAVE_SYSCONF == 1

    /* Code for POSIX systems */

    struct tms buffer;
    long nticks;                /* number of clock ticks per second */

    nticks = sysconf(_SC_CLK_TCK);
    times(&buffer);
    return (unsigned long) ((buffer.tms_utime + buffer.tms_cutime) * (1000.0/nticks));

#else
    return 0UL;
#endif /* HAVE_SYSCONF == 1 */

}
