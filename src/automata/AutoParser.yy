%skeleton "lalr1.cc"                          /*  -*- C++ -*- */
%require "2.4.1"
%defines
%define parser_class_name "auto_parser"
%code requires {
#define autoparserlex autolex
#include <string>
#include <vector>
#include "Automaton.h"
#include "ExprUtil.h"
  class auto_driver;
}
// The parsing context.
%parse-param { auto_driver& driver }
%lex-param   { auto_driver& driver }
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
  Automaton *aut;
  Automaton::Transition *transition;
  std::vector<Automaton::State> *states;
  std::vector<Automaton::Transition> *transitions;
  std::string *sval;
  unsigned index;
  ID ival;
};
%code {
#include "AutoWrapper.h"
}
%token        END      0 "end of file"
%token        INIT       "=>"
%token        EQUIV      "=="
%token        IMPLIES    "->"
%token        TRUE
%token        FALSE
%token        STRUCTURE "Structure"
%token        FAIRNESS "Buechi Fairness"
%token        INVALID_CHAR
%token <sval> IDENTIFIER "identifier"
%token <index> STATE
%type  <aut> automaton
%type  <aut> structure_section
%type  <aut> structure
%type  <aut> state
%type  <aut> state_def
%type  <states> fairness_section
%type  <states> fairness
%type  <transitions> transitions
%type  <transition> transition
%type  <ival> expression
%printer    { debug_stream() << *$$; } "identifier"
%destructor { delete $$; } "identifier"
%printer    { debug_stream() << stringOf(*driver.ev,$$); } <ival>

%%
%start input;

%left '^' "==" "->";
%left '|';
%left '&';
%nonassoc '~' '!';

// Allow having multiple automata per file
input: /* nothing */
| input automaton { driver.eat->addAutomaton(*$2);
                    delete $2; }
;

automaton: structure_section fairness_section { $$ = $1;
                                                $$->badStates = *$2;
                                                delete $2; };

structure_section: "Structure" structure { $$ = $2; };

structure: state  { $$ = new Automaton; 
                    assert($1->states.size() == 1);
                    $$->states.push_back($1->states[0]);
                    $$->initialStates.insert($$->initialStates.end(), $1->initialStates.begin(), $1->initialStates.end());
                    $$->transitions.insert($$->transitions.end(),
                    $1->transitions.begin(), $1->transitions.end());
                    delete $1; }
| structure state { $$ = $1;
                    assert($2->states.size() == 1);
                    $$->states.push_back($2->states[0]);
                    $$->initialStates.insert($$->initialStates.end(), $2->initialStates.begin(), $2->initialStates.end());
                    $$->transitions.insert($$->transitions.end(),
                    $2->transitions.begin(), $2->transitions.end());
                    delete $2; }
;

state: "=>" state_def { $$ = $2;
                        $$->initialStates.push_back($2->states[0]); }
| state_def           { $$ = $1; }
;

state_def: STATE '{' transitions '}'   { $$ = new Automaton;
                                         $$->states.push_back($1);
                                         for(unsigned i = 0; i < $3->size(); ++i)
                                           (*$3)[i].source = $1;
                                         $$->transitions = *$3;
                                         delete $3; }
;

transitions: transition              { $$ = new std::vector<Automaton::Transition>;
                                       $$->push_back(*$1);
                                       delete $1; }
| transition ',' transitions         { $$ = $3;
                                       $$->push_back(*$1);
                                       delete $1; }
;

transition: '[' expression ']' STATE { $$ = new Automaton::Transition;
                                       $$->destination = $4;
                                       $$->label = $2; };
          
fairness_section: "Buechi Fairness"  fairness { $$ = $2; };

fairness: STATE                     { $$ = new std::vector<Automaton::State>;
                                      $$->push_back($1); }
| fairness STATE                    { $$ = $1;
                                      $$->push_back($2); }
;

expression: '(' expression ')'      { $$ = $2; }
| TRUE                              { $$ = driver.ev->btrue(); }
| FALSE                             { $$ = driver.ev->bfalse(); }
| expression '|' expression         { $$ = driver.ev->apply(Expr::Or, $1, $3); }
| expression '&' expression         { $$ = driver.ev->apply(Expr::And, $1, $3); }
| expression '^' expression         { $$ = driver.ev->apply(Expr::Not, driver.ev->apply(Expr::Equiv, $1, $3)); }
| expression "==" expression        { $$ = driver.ev->apply(Expr::Equiv, $1, $3); }
| expression "->" expression        { $$ = driver.ev->apply(Expr::Implies, $1, $3); }
| '~' expression                    { $$ = driver.ev->apply(Expr::Not, $2); }
| '!' expression                    { $$ = driver.ev->apply(Expr::Not, $2); }
| "identifier"                      { if (driver.ev->varExists(*$1)) {
                                        $$ = driver.ev->newVar(*$1);
                                        if (driver.eat->isOutput($$))
                                          $$ = driver.eat->outputFnOf($$);
                                      } else {
                                        error(yylloc, std::string("unknown variable: ") + *$1);
                                        YYERROR;
                                      }
                                      delete $1;
                                    };

%%

void
autoparser::auto_parser::error(const autoparser::auto_parser::location_type& l,
                      const std::string& m)
{
  driver.error(l, m);
}
