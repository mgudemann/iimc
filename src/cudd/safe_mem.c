/*
 * Revision Control Information
 *
 * $Id: safe_mem.c,v 1.7 2002/09/14 22:59:31 fabio Exp $
 *
 */
/* LINTLIBRARY */

#include "util.h"

/*
 *  These are interface routines to be placed between a program and the
 *  system memory allocator.  
 *
 *  It forces well-defined semantics for several 'borderline' cases:
 *
 *	malloc() of a 0 size object is guaranteed to return something
 *	    which is not 0, and can safely be freed (but not dereferenced)
 *	free() accepts (silently) an 0 pointer
 *	realloc of a 0 pointer is allowed, and is equiv. to malloc()
 *	For the IBM/PC it forces no object > 64K; note that the size argument
 *	    to malloc/realloc is a 'long' to catch this condition
 *
 *  The function pointer MMoutOfMemory() contains a vector to handle a
 *  'out-of-memory' error (which, by default, points at a simple wrap-up 
 *  and exit routine).
 */

void (*MMoutOfMemory)(unsigned long) = MMout_of_memory;


/* MMout_of_memory -- out of memory for lazy people, flush and exit */
void
MMout_of_memory(unsigned long size)
{
  (void) fflush(stdout);
  (void) fprintf(stderr, "\nout of memory allocating %lu bytes\n", size);
  exit(1);
}


void *
MMalloc(unsigned long size)
{
  void *p;

#ifdef IBMPC
  if (size > 65000L) {
    if (MMoutOfMemory != (void (*)(unsigned long)) 0) (*MMoutOfMemory)(size);
    return NIL(void);
  }
#endif
  if (size == 0) size = sizeof(long);
  if ((p = malloc(size)) == NIL(void)) {
    if (MMoutOfMemory != (void (*)(unsigned long)) 0) (*MMoutOfMemory)(size);
    return NIL(void);
  }
  return p;
}


void *
MMrealloc(void *obj, unsigned long size)
{
  void *p;

#ifdef IBMPC
  if (size > 65000L) {
    if (MMoutOfMemory != (void (*)(unsigned long)) 0) (*MMoutOfMemory)(size);
    return NIL(void);
  }
#endif
  if (obj == NIL(void)) return MMalloc(size);
  if (size <= 0) size = sizeof(long);
  if ((p = realloc(obj, size)) == NIL(void)) {
    if (MMoutOfMemory != (void (*)(unsigned long)) 0) (*MMoutOfMemory)(size);
    return NIL(void);
  }
  return p;
}


void
MMfree(void *obj)
{
  if (obj != 0) {
    free(obj);
  }
}
