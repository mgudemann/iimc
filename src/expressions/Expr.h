/* -*- C++ -*- */

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

#ifndef EXPR_
#define EXPR_

/** @file Expr.h */

#include <string>
#include <vector>

#include "HashedStructure.h"
#include "ExprNode.h"

/** Namespace of expressions. */
namespace Expr {

  class Expr;

  /**
   * A context for DAG-compressed expressions.
   */
  class Manager : public HSManager<Expr> {
  public:
    class View;

    /**
     * A simple constructor.  Throws a [TODO] exception if it cannot be
     * created (global resources are exhausted).
     */
    Manager();

    /**
     * A view constructor.  A view object presents a combined global and
     * thread-local view of the expression context, allowing efficent
     * local expression creation as well as thread-safe/distributed-safe
     * global expression creation and referencing.
     *
     * Throws a [TODO] exception if a view cannot be created (global
     * resources are exhausted).
     */
    View * newView();

    /**
     * A thread-local view of a single expression context.
     */
    class View : public HSManager<Expr>::HSView {
      friend class Manager;
    public:

      virtual ~View();

      View * clone() const;

      Manager & manager();

      /**
       * Returns the constant "true".
       */
      ID btrue();

      /**
       * Returns the constant "false".
       */
      ID bfalse();

      /**
       * Returns the variable with name "name".
       */
      ID newVar(const std::string & name);
      
      /**
       * Returns whether the variable with name "name" exists.
       */
      bool varExists(const std::string & name);

      /**
       * Returns the simplified result of applying (unary) op to arg.
       */
      ID apply(Op op, ID arg);

      /**
       * Returns the simplified result of applying (binary) op to (arg0,
       * arg1).
       */
      ID apply(Op op, ID arg0, ID arg1);

      /**
       * Returns the simplified (if "simplify" == true) result of applying
       * (n-ary) op to args.  "op" may be 3-ary (Ite, Tite) or a binary
       * one (And, Or) applied to many formulas.  "args" can be modified.
       *
       * Simplifications (only applied if "simplify" == true and "op" is
       * And, Or) are local:
       *   1. Non-redundant args.
       *   2. No constants.
       *   3. No instances of l, ~l.
       *   4. Arguments ordered by ID for canonicity.
       */
      ID apply(Op op, std::vector<ID> & args, bool simplify = true);

      /**
       * Primes the variable represented by "id" once.
       */
      ID prime(ID id, int delta = 1);

      /**
       * Unprimes the variable represented by "id" once.
       */
      ID unprime(ID id, int delta = 1);

      /**
       * Sets the number of primes of the variable represented by "id" to
       * n.
       */
      ID primeTo(ID id, int n);

      /**
       * Returns the number of primes of the variable represented by "id".
       */
      int nprimes(ID id);

      /**
       * The operator of the expression represented by "id".
       */
      Op op(ID id);

      const std::string & varName(ID id);

      /**
       * Returns the arguments of the expression represented by "id".
       * On return, "*nArgs" contains the number of children, and the
       * return value is a constant pointer to a constant array of
       * "*nArgs" elements.
       */
      const ID * arguments(ID id, int * nArgs);

      /**
       * An interface for folding over DAG-compressed expressions.
       */
      class Folder {
      public:
        Folder(Manager::View & _v) : v(_v) {}
        virtual bool filter(ID) { return true; }
        virtual ID fold(ID id, int n, const ID * const args);
        Manager::View & view() { return v; }
      private:
        Manager::View & v;
      };

      /**
       * Applies a Folder to an expression.
       */
      ID fold(Folder & f, ID id);

      /**
       * Applies a Folder to a vector of expressions, returning the
       * results via the same vector.
       */
      void fold(Folder & f, std::vector<ID> & id);

      /**
       * Sorts a vector of IDs.  The resulting ordering is such that
       *  1. a variable and its negation are adjacent: v, !v;
       *  2. primed versions variables are close together.
       * For example, v, v(3), v(1), !v(3), !v would be sorted as
       * follows: v, !v, v(1), v(3), !v(3).
       */
      void sort(std::vector<ID>::iterator begin, std::vector<ID>::iterator end);

    protected:
      virtual ID replaceArguments(ID id, const Expr * const e, int n, const ID * const args);
      virtual ID hsID(ID id);
      virtual ID modifyID(ID id, ID by);

    private:
      ID childrenIDs1[1];
      View(Manager * man);
      Manager * man;

      class fold_fold : public HashedStructure<Expr>::Folder {
      public:
	fold_fold(Manager::View::Folder & fo) : f(fo) {}
	virtual bool filter(ID id, Expr *) {
	  return f.filter(id);
	}
	virtual ID fold(ID id, Expr *, int n, const ID * const args) {
	  return f.fold(id, n, args);
	}
      private:
	Manager::View::Folder & f;
      };

    };

  private:
    ID trueID, falseID;
  };

}

#endif
