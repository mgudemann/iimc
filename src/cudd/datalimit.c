/**CFile************************************************************************

  FileName    [datalimit.c]

  PackageName [util]

  Synopsis [Routine to obtain the maximum data size available to a program. The
  routine is based on "getrlimit". If the system does not have this function,
  the default value RLIMIT_DATA_DEFAULT is assumed. This function provides an
  informative value, it does not restrict the size of the program in any way.]

  Author      [Fabio Somenzi <fabio@colorado.edu>]

  Copyright   [This file was created at the University of Colorado at
  Boulder.  The University of Colorado at Boulder makes no warranty
  about the suitability of this software for any purpose.  It is
  presented on an AS IS basis.]

******************************************************************************/

#include "util.h"

static char rcsid[] UNUSED = "$Id: datalimit.c,v 1.6 2008/04/25 07:00:55 fabio Exp $";

#if HAVE_SYS_RESOURCE_H
#if HAVE_SYS_TIME_H
#include <sys/time.h>
#endif
#include <sys/resource.h>
#endif

/*---------------------------------------------------------------------------*/
/* Type declarations                                                         */
/*---------------------------------------------------------------------------*/

/*---------------------------------------------------------------------------*/
/* Structure declarations                                                    */
/*---------------------------------------------------------------------------*/

/*---------------------------------------------------------------------------*/
/* Macro declarations                                                        */
/*---------------------------------------------------------------------------*/

#ifndef RLIMIT_DATA_DEFAULT
#define RLIMIT_DATA_DEFAULT 268435456	/* assume 64MB by default */
#endif

/*---------------------------------------------------------------------------*/
/* Variable declarations                                                     */
/*---------------------------------------------------------------------------*/

/**AutomaticStart*************************************************************/

/*---------------------------------------------------------------------------*/
/* Static function prototypes                                                */
/*---------------------------------------------------------------------------*/

/**AutomaticEnd***************************************************************/

/*---------------------------------------------------------------------------*/
/* Definition of exported functions                                          */
/*---------------------------------------------------------------------------*/

/**Function********************************************************************

  Synopsis           [Function that computes the data limit of the process.]

  SideEffects        []

******************************************************************************/
unsigned long
getSoftDataLimit(void)
{
#if HAVE_SYS_RESOURCE_H && HAVE_GETRLIMIT && defined(RLIMIT_DATA)
    struct rlimit rl;
    int result;

    result = getrlimit(RLIMIT_DATA, &rl);
    if (result != 0 || rl.rlim_cur == RLIM_INFINITY)
	return((unsigned long) RLIMIT_DATA_DEFAULT);
    else
	return((unsigned long) rl.rlim_cur);
#else
    return((unsigned long) RLIMIT_DATA_DEFAULT);
#endif

} /* end of getSoftDataLimit */


/*---------------------------------------------------------------------------*/
/* Definition of internal functions                                          */
/*---------------------------------------------------------------------------*/

/*---------------------------------------------------------------------------*/
/* Definition of static functions                                            */
/*---------------------------------------------------------------------------*/
