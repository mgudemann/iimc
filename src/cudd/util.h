/**CHeaderFile*****************************************************************

  FileName    [ util.h ]

  PackageName [ util ]

  Synopsis    [ Very low-level utilities ]

  Description [ Includes file access, pipes, forks, time, and temporary file
		access. ]

  Author      [ Stephen Edwards <sedwards@eecs.berkeley.edu> and many others]

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

  Revision    [$Id: util.h,v 1.19 2009/04/11 02:04:46 fabio Exp $]

******************************************************************************/

#ifndef _UTIL
#define _UTIL

#include <stdio.h>
#include <ctype.h>
#include <math.h>

#if HAVE_UNISTD_H
#  include <unistd.h>
#endif

#if HAVE_SYS_TYPES_H
#  include <sys/types.h>
#endif

#if HAVE_VARARGS_H
#  include <varargs.h>
#endif

#if STDC_HEADERS
#  include <stdlib.h>
#  include <string.h>
#else
#  ifdef HAVE_STRCHR
char * strchr(const char *, int);
int strcmp(const char *, const char *);
#  else
#    define strchr index
#  endif
#  ifdef HAVE_GETENV
char * getenv(const char *);
#  endif
#endif /* STDC_HEADERS */

#if HAVE_ERRNO_H
#  include <errno.h>
#endif

/*
 * Ensure we have reasonable assert() and fail() functions
 */

#if HAVE_ASSERT_H
#  include <assert.h>
#else
#  ifdef NDEBUG
#    define assert(ex) ;
#  else
#    define assert(ex) {\
    if (! (ex)) {\
	(void) fprintf(stderr,\
	    "Assertion failed: file %s, line %d\n\"%s\"\n",\
	    __FILE__, __LINE__, "ex");\
	(void) fflush(stdout);\
	abort();\
    }\
}
#  endif
#endif

#define fail(why) {\
    (void) fprintf(stderr, "Fatal error: file %s, line %d\n%s\n",\
	__FILE__, __LINE__, why);\
    (void) fflush(stdout);\
    abort();\
}

/*
 * A little support for C++ compilers
 */

#ifdef __cplusplus
#  define EXTERN	extern "C"
#else
#  define EXTERN	extern
#endif

/*
 * Support to define unused varibles
 */
#if defined (__GNUC__)
#if (__GNUC__ >2 || __GNUC_MINOR__ >=7) && !defined(UNUSED)
#define UNUSED __attribute__ ((unused))
#else
#define UNUSED
#endif
#else
#define UNUSED
#endif

/*
 * A neater way to define zero pointers
 *
 * Usage:
 *  int * fred;
 *  fred = NIL(int);
 */

#define NIL(type)		((type *) 0)

/* #define USE_MM */

#ifdef USE_MM
/*
 *  assumes the memory manager is libmm.a (a deprecated (?) Octtools library)
 *	- allows malloc(0) or realloc(obj, 0)
 *	- catches out of memory (and calls MMout_of_memory())
 *	- catch free(0) and realloc(0, size) in the macros
 */
#  define ALLOC(type, num)	\
    ((type *) malloc(sizeof(type) * (num)))
#  define REALLOC(type, obj, num)	\
    (obj) ? ((type *) realloc((void *) obj, sizeof(type) * (num))) : \
	    ((type *) malloc(sizeof(type) * (num)))
#  define FREE(obj)		\
    ((obj) ? (free((void *) (obj)), (obj) = 0) : 0)
#else
/*
 *  enforce strict semantics on the memory allocator
 */
#  define ALLOC(type, num)	\
    ((type *) MMalloc(sizeof(type) * (unsigned long) (num)))
#  define REALLOC(type, obj, num)	\
    ((type *) MMrealloc((void *) (obj), sizeof(type) * (unsigned long) (num)))
#  define FREE(obj)		\
    ((obj) ? (free((void *) (obj)), (obj) = 0) : 0)
#endif

#ifndef ABS
#  define ABS(a)			((a) < 0 ? -(a) : (a))
#endif

#ifndef MAX
#  define MAX(a,b)		((a) > (b) ? (a) : (b))
#endif

#ifndef MIN
#  define MIN(a,b)		((a) < (b) ? (a) : (b))
#endif

#ifndef HUGE_VAL
#  ifndef HUGE
#    define HUGE  8.9884656743115790e+307
#  endif
#  define HUGE_VAL HUGE
#endif

#ifndef MAXINT
#  define MAXINT (1 << 30)
#endif

EXTERN void util_print_cpu_stats(FILE *);
EXTERN unsigned long util_cpu_time(void);
EXTERN unsigned long util_cpu_ctime(void);
EXTERN int util_check_file(char const *, char const *);
EXTERN char *util_path_search(char const *);
EXTERN char *util_file_search(char const *, char *, char const *);
EXTERN char *util_print_time(unsigned long);
EXTERN int util_save_image(char const *, char const *);
EXTERN char *util_strsav(char const *);
EXTERN char *util_inttostr(int);
EXTERN char *util_strcat3(char const *, char const *, char const *);
EXTERN char *util_strcat4(char const *, char const *, char const *, char const *);
EXTERN int util_do_nothing(void);
EXTERN char *util_tilde_expand(char const *);
EXTERN char *util_tempnam(char const *, char const *);
EXTERN FILE *util_tmpfile(void);
EXTERN void util_srandom(long);
EXTERN long util_random(void);
EXTERN unsigned long getSoftDataLimit(void);
EXTERN void MMout_of_memory(unsigned long);
EXTERN void *MMalloc(unsigned long);
EXTERN void *MMrealloc(void *, unsigned long);
EXTERN void MMfree(void *);

/**AutomaticStart*************************************************************/

/*---------------------------------------------------------------------------*/
/* Function prototypes                                                       */
/*---------------------------------------------------------------------------*/

/**AutomaticEnd***************************************************************/

#endif /* _UTIL */
