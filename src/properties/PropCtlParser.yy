%skeleton "lalr1.cc"                          /*  -*- C++ -*- */
%require "3.0.2"
%defines
%define parser_class_name {ctl_parser}
%code requires {
#ifdef __clang__
#pragma clang diagnostic ignored "-Wdeprecated-register"
#pragma clang diagnostic ignored "-Wunneeded-internal-declaration"
#endif
#define yylex ctllex
#include <string>
#include "ExprUtil.h"
  class ctl_driver;
}
// The parsing context.
%parse-param { ctl_driver& driver }
%lex-param   { ctl_driver& driver }
%locations
%initial-action
{
  // Initialize the initial location.
  @$.begin.filename = @$.end.filename = &driver.file;
};
%debug
%error-verbose
// Symbols.
%union
{
  std::string *sval;
  ID ival;
};
%code {
#include "PropCtlWrapper.h"
}
%token        END      0 "end of file"
%token        EQUIV      "=="
%token        IMPLIES    "->"
%token        TRUE
%token        FALSE
%token        INVALID_CHAR
%token <sval> IDENTIFIER "identifier"
%type  <ival> formula
%printer    { debug_stream() << *$$; } "identifier"
%destructor { delete $$; } "identifier"
%printer    { debug_stream() << stringOf(*driver.ev,$$); } <ival>

%%
%start input;

%left '^' "==" "->";
%left '|';
%left '&';
%nonassoc '~' '!';
%left EX EF EG AX AF AG EQUANT AQUANT UNTIL RELEASES WEAK_UNTIL;

input: /* nothing */
| input formula { driver.eat->addCtlProperty($2); }
;

formula: '(' formula ')'            { $$ = $2; }
| TRUE                              { $$ = driver.ev->btrue(); }
| FALSE                             { $$ = driver.ev->bfalse(); }
| EX formula                        { $$ = driver.ev->apply(Expr::X, $2); }
| EF formula                        { $$ = driver.ev->apply(Expr::F, $2); }
| EG formula                        { $$ = driver.ev->apply(Expr::G, $2); }
| EQUANT formula UNTIL formula      { $$ = driver.ev->apply(Expr::U, $2, $4); }
| EQUANT formula RELEASES formula   { ID conj = driver.ev->apply(Expr::And, $2, $4);
                                      ID until = driver.ev->apply(Expr::U, $4, conj);
                                      ID eg = driver.ev->apply(Expr::G, $4);
                                      ID negu = driver.ev->apply(Expr::Not, until);
                                      ID nege = driver.ev->apply(Expr::Not, eg);
                                      ID conj2 = driver.ev->apply(Expr::And, negu, nege);
                                      $$ = driver.ev->apply(Expr::Not, conj2); }
| EQUANT formula WEAK_UNTIL formula { ID until = driver.ev->apply(Expr::U, $2, $4);
                                      ID eg = driver.ev->apply(Expr::G, $2);
                                      ID negu = driver.ev->apply(Expr::Not, until);
                                      ID nege = driver.ev->apply(Expr::Not, eg);
                                      ID conj = driver.ev->apply(Expr::And, negu, nege);
                                      $$ = driver.ev->apply(Expr::Not, conj); }
| AX formula                        { ID arg = driver.ev->apply(Expr::Not, $2);
                                      ID neg = driver.ev->apply(Expr::X, arg);
                                      $$ = driver.ev->apply(Expr::Not, neg); }
| AF formula                        { ID arg = driver.ev->apply(Expr::Not, $2);
                                      ID neg = driver.ev->apply(Expr::G, arg);
                                      $$ = driver.ev->apply(Expr::Not, neg); }
| AG formula                        { ID arg = driver.ev->apply(Expr::Not, $2);
                                      ID neg = driver.ev->apply(Expr::F, arg);
                                      $$ = driver.ev->apply(Expr::Not, neg); }
| AQUANT formula UNTIL formula      { ID arg2 = driver.ev->apply(Expr::Not, $2);
                                      ID arg4 = driver.ev->apply(Expr::Not, $4);
                                      ID conj = driver.ev->apply(Expr::And, arg2, arg4);
                                      ID until = driver.ev->apply(Expr::U, arg4, conj);
                                      ID eg = driver.ev->apply(Expr::G, arg4);
                                      ID negu = driver.ev->apply(Expr::Not, until);
                                      ID nege = driver.ev->apply(Expr::Not, eg);
                                      $$ = driver.ev->apply(Expr::And, negu, nege); }
| AQUANT formula RELEASES formula   { ID arg2 = driver.ev->apply(Expr::Not, $2);
                                      ID arg4 = driver.ev->apply(Expr::Not, $4);
                                      ID neg = driver.ev->apply(Expr::U, arg2, arg4);
                                      $$ = driver.ev->apply(Expr::Not, neg); }
| AQUANT formula WEAK_UNTIL formula { ID arg2 = driver.ev->apply(Expr::Not, $2);
                                      ID arg4 = driver.ev->apply(Expr::Not, $4);
                                      ID argc = driver.ev->apply(Expr::And, arg2, arg4);
                                      ID neg = driver.ev->apply(Expr::U, arg4, argc);
                                      $$ = driver.ev->apply(Expr::Not, neg); }
| formula '|' formula               { ID arg1 = driver.ev->apply(Expr::Not, $1);
                                      ID arg3 = driver.ev->apply(Expr::Not, $3);
                                      ID conj = driver.ev->apply(Expr::And, arg1, arg3);
                                      $$ = driver.ev->apply(Expr::Not, conj); }
| formula '&' formula               { $$ = driver.ev->apply(Expr::And, $1, $3); }
| formula '^' formula               { ID arg1 = driver.ev->apply(Expr::Not, $1);
                                      ID arg3 = driver.ev->apply(Expr::Not, $3);
                                      ID conj1 = driver.ev->apply(Expr::And, $1, $3);
                                      ID conj2 = driver.ev->apply(Expr::And, arg1, arg3);
                                      ID neg1 = driver.ev->apply(Expr::Not, conj1);
                                      ID neg2 = driver.ev->apply(Expr::Not, conj2);
                                      $$ = driver.ev->apply(Expr::And, neg1, neg2); }
| formula "==" formula              { ID arg1 = driver.ev->apply(Expr::Not, $1);
                                      ID arg3 = driver.ev->apply(Expr::Not, $3);
                                      ID conj1 = driver.ev->apply(Expr::And, $1, arg3);
                                      ID conj2 = driver.ev->apply(Expr::And, arg1, $3);
                                      ID neg1 = driver.ev->apply(Expr::Not, conj1);
                                      ID neg2 = driver.ev->apply(Expr::Not, conj2);
                                      $$ = driver.ev->apply(Expr::And, neg1, neg2); }
| formula "->" formula              { ID arg3 = driver.ev->apply(Expr::Not, $3);
                                      ID conj = driver.ev->apply(Expr::And, $1, arg3);
                                      $$ = driver.ev->apply(Expr::Not, conj); }
| '~' formula                       { $$ = driver.ev->apply(Expr::Not, $2); }
| '!' formula                       { $$ = driver.ev->apply(Expr::Not, $2); }
| "identifier"                      { if (driver.ev->varExists(*$1)) {
                                        $$ = driver.ev->newVar(*$1);
                                      } else {
                                        error(@$, std::string("unknown variable: ") + *$1);
                                        YYERROR;
                                      }
                                      delete $1;
                                    };
| INVALID_CHAR                      { YYERROR; }
%%

void
yy::ctl_parser::error(const yy::ctl_parser::location_type& l,
                      const std::string& m)
{
  driver.error(l, m);
}
