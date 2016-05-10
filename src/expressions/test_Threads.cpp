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

#include "Expr.h"
#include "ExprUtil.h"

#ifdef HAVE_CONFIG_H
#include "config.h"
#endif

#include <ostream>
#include <pthread.h>
#include <sstream>

#define N 1024
#define T 16

using namespace std;
using namespace Expr;

static ID bigAnd(Manager::View * v, IDVector & ids, int lo, int hi) {
  assert (hi >= lo);
  if (lo == hi)
    return ids[lo];
  if (lo+1 == hi)
    return v->apply(And, ids[lo], ids[hi]);
  return v->apply(And,
                  bigAnd(v, ids, lo, (lo+hi)/2),
                  bigAnd(v, ids, 1+(lo+hi)/2, hi));
}

struct worker_args {
  Manager * man;
  ID * rv;
};

static void * worker(void * _args) {
  worker_args * args = (worker_args *) _args;
  Manager & man = *(args->man);
  ID & rv = *(args->rv);

  Manager::View * v = man.newView();

  IDVector ids;
  for (int i = 0; i < N; ++i) {
    ostringstream buf;
    buf << "v" << i;
    ids.push_back(v->newVar(buf.str()));
  }

  v->begin_local();
  ID ba = bigAnd(v, ids, 0, ids.size()-1);
  rv = v->global(ba);
  v->end_local();

  delete v;

  return NULL;
}

int main(int argc, const char * argv[]) {
#ifdef MTHREADS
  Manager * man = new Manager();

  ID orig;
  pthread_t t1;
  worker_args args;
  args.man = man;
  args.rv = &orig;
  pthread_create(&t1, NULL, worker, (void *) &args);
  pthread_join(t1, NULL);

  ID rvs[T];
  pthread_t threads[T];
  worker_args wargs[T];
  for (int i = 0; i < T; ++i) {
    wargs[i].man = man;
    wargs[i].rv = rvs+i;
    pthread_create(threads+i, NULL, worker, (void *) (wargs+i));
  }
  for (int i = 0; i < T; ++i) {
    pthread_join(threads[i], NULL);
    assert (orig == rvs[i]);
  }

  delete man;
#endif
}
