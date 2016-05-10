/* A Bison parser, made by GNU Bison 2.5.  */

/* Skeleton implementation for Bison LALR(1) parsers in C++
   
      Copyright (C) 2002-2011 Free Software Foundation, Inc.
   
   This program is free software: you can redistribute it and/or modify
   it under the terms of the GNU General Public License as published by
   the Free Software Foundation, either version 3 of the License, or
   (at your option) any later version.
   
   This program is distributed in the hope that it will be useful,
   but WITHOUT ANY WARRANTY; without even the implied warranty of
   MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the
   GNU General Public License for more details.
   
   You should have received a copy of the GNU General Public License
   along with this program.  If not, see <http://www.gnu.org/licenses/>.  */

/* As a special exception, you may create a larger work that contains
   part or all of the Bison parser skeleton and distribute that work
   under terms of your choice, so long as that work isn't itself a
   parser generator using the skeleton or a modified version thereof
   as a parser skeleton.  Alternatively, if you modify or redistribute
   the parser skeleton itself, you may (at your option) remove this
   special exception, which will cause the skeleton and the resulting
   Bison output files to be licensed under the GNU General Public
   License without this special exception.
   
   This special exception was added by the Free Software Foundation in
   version 2.2 of Bison.  */

// Take the name prefix into account.
#define yylex   autoparserlex

/* First part of user declarations.  */


/* Line 293 of lalr1.cc  */
#line 41 "src/automata/AutoParser.cc"


#include "AutoParser.hh"

/* User implementation prologue.  */


/* Line 299 of lalr1.cc  */
#line 50 "src/automata/AutoParser.cc"
/* Unqualified %code blocks.  */

/* Line 300 of lalr1.cc  */
#line 35 "../iimc/src/automata/AutoParser.yy"

#include "AutoWrapper.h"



/* Line 300 of lalr1.cc  */
#line 61 "src/automata/AutoParser.cc"

#ifndef YY_
# if defined YYENABLE_NLS && YYENABLE_NLS
#  if ENABLE_NLS
#   include <libintl.h> /* FIXME: INFRINGES ON USER NAME SPACE */
#   define YY_(msgid) dgettext ("bison-runtime", msgid)
#  endif
# endif
# ifndef YY_
#  define YY_(msgid) msgid
# endif
#endif

/* YYLLOC_DEFAULT -- Set CURRENT to span from RHS[1] to RHS[N].
   If N is 0, then set CURRENT to the empty location which ends
   the previous symbol: RHS[0] (always defined).  */

#define YYRHSLOC(Rhs, K) ((Rhs)[K])
#ifndef YYLLOC_DEFAULT
# define YYLLOC_DEFAULT(Current, Rhs, N)                               \
 do                                                                    \
   if (N)                                                              \
     {                                                                 \
       (Current).begin = YYRHSLOC (Rhs, 1).begin;                      \
       (Current).end   = YYRHSLOC (Rhs, N).end;                        \
     }                                                                 \
   else                                                                \
     {                                                                 \
       (Current).begin = (Current).end = YYRHSLOC (Rhs, 0).end;        \
     }                                                                 \
 while (false)
#endif

/* Suppress unused-variable warnings by "using" E.  */
#define YYUSE(e) ((void) (e))

/* Enable debugging if requested.  */
#if YYDEBUG

/* A pseudo ostream that takes yydebug_ into account.  */
# define YYCDEBUG if (yydebug_) (*yycdebug_)

# define YY_SYMBOL_PRINT(Title, Type, Value, Location)	\
do {							\
  if (yydebug_)						\
    {							\
      *yycdebug_ << Title << ' ';			\
      yy_symbol_print_ ((Type), (Value), (Location));	\
      *yycdebug_ << std::endl;				\
    }							\
} while (false)

# define YY_REDUCE_PRINT(Rule)		\
do {					\
  if (yydebug_)				\
    yy_reduce_print_ (Rule);		\
} while (false)

# define YY_STACK_PRINT()		\
do {					\
  if (yydebug_)				\
    yystack_print_ ();			\
} while (false)

#else /* !YYDEBUG */

# define YYCDEBUG if (false) std::cerr
# define YY_SYMBOL_PRINT(Title, Type, Value, Location)
# define YY_REDUCE_PRINT(Rule)
# define YY_STACK_PRINT()

#endif /* !YYDEBUG */

#define yyerrok		(yyerrstatus_ = 0)
#define yyclearin	(yychar = yyempty_)

#define YYACCEPT	goto yyacceptlab
#define YYABORT		goto yyabortlab
#define YYERROR		goto yyerrorlab
#define YYRECOVERING()  (!!yyerrstatus_)


namespace autoparser {

/* Line 382 of lalr1.cc  */
#line 147 "src/automata/AutoParser.cc"

  /* Return YYSTR after stripping away unnecessary quotes and
     backslashes, so that it's suitable for yyerror.  The heuristic is
     that double-quoting is unnecessary unless the string contains an
     apostrophe, a comma, or backslash (other than backslash-backslash).
     YYSTR is taken from yytname.  */
  std::string
  auto_parser::yytnamerr_ (const char *yystr)
  {
    if (*yystr == '"')
      {
        std::string yyr = "";
        char const *yyp = yystr;

        for (;;)
          switch (*++yyp)
            {
            case '\'':
            case ',':
              goto do_not_strip_quotes;

            case '\\':
              if (*++yyp != '\\')
                goto do_not_strip_quotes;
              /* Fall through.  */
            default:
              yyr += *yyp;
              break;

            case '"':
              return yyr;
            }
      do_not_strip_quotes: ;
      }

    return yystr;
  }


  /// Build a parser object.
  auto_parser::auto_parser (auto_driver& driver_yyarg)
    :
#if YYDEBUG
      yydebug_ (false),
      yycdebug_ (&std::cerr),
#endif
      driver (driver_yyarg)
  {
  }

  auto_parser::~auto_parser ()
  {
  }

#if YYDEBUG
  /*--------------------------------.
  | Print this symbol on YYOUTPUT.  |
  `--------------------------------*/

  inline void
  auto_parser::yy_symbol_value_print_ (int yytype,
			   const semantic_type* yyvaluep, const location_type* yylocationp)
  {
    YYUSE (yylocationp);
    YYUSE (yyvaluep);
    switch (yytype)
      {
        case 11: /* "\"identifier\"" */

/* Line 449 of lalr1.cc  */
#line 59 "../iimc/src/automata/AutoParser.yy"
	{ debug_stream() << *(yyvaluep->sval); };

/* Line 449 of lalr1.cc  */
#line 222 "src/automata/AutoParser.cc"
	break;
      case 36: /* "expression" */

/* Line 449 of lalr1.cc  */
#line 61 "../iimc/src/automata/AutoParser.yy"
	{ debug_stream() << stringOf(*driver.ev,(yyvaluep->ival)); };

/* Line 449 of lalr1.cc  */
#line 231 "src/automata/AutoParser.cc"
	break;
       default:
	  break;
      }
  }


  void
  auto_parser::yy_symbol_print_ (int yytype,
			   const semantic_type* yyvaluep, const location_type* yylocationp)
  {
    *yycdebug_ << (yytype < yyntokens_ ? "token" : "nterm")
	       << ' ' << yytname_[yytype] << " ("
	       << *yylocationp << ": ";
    yy_symbol_value_print_ (yytype, yyvaluep, yylocationp);
    *yycdebug_ << ')';
  }
#endif

  void
  auto_parser::yydestruct_ (const char* yymsg,
			   int yytype, semantic_type* yyvaluep, location_type* yylocationp)
  {
    YYUSE (yylocationp);
    YYUSE (yymsg);
    YYUSE (yyvaluep);

    YY_SYMBOL_PRINT (yymsg, yytype, yyvaluep, yylocationp);

    switch (yytype)
      {
        case 11: /* "\"identifier\"" */

/* Line 480 of lalr1.cc  */
#line 60 "../iimc/src/automata/AutoParser.yy"
	{ delete (yyvaluep->sval); };

/* Line 480 of lalr1.cc  */
#line 270 "src/automata/AutoParser.cc"
	break;

	default:
	  break;
      }
  }

  void
  auto_parser::yypop_ (unsigned int n)
  {
    yystate_stack_.pop (n);
    yysemantic_stack_.pop (n);
    yylocation_stack_.pop (n);
  }

#if YYDEBUG
  std::ostream&
  auto_parser::debug_stream () const
  {
    return *yycdebug_;
  }

  void
  auto_parser::set_debug_stream (std::ostream& o)
  {
    yycdebug_ = &o;
  }


  auto_parser::debug_level_type
  auto_parser::debug_level () const
  {
    return yydebug_;
  }

  void
  auto_parser::set_debug_level (debug_level_type l)
  {
    yydebug_ = l;
  }
#endif

  inline bool
  auto_parser::yy_pact_value_is_default_ (int yyvalue)
  {
    return yyvalue == yypact_ninf_;
  }

  inline bool
  auto_parser::yy_table_value_is_error_ (int yyvalue)
  {
    return yyvalue == yytable_ninf_;
  }

  int
  auto_parser::parse ()
  {
    /// Lookahead and lookahead in internal form.
    int yychar = yyempty_;
    int yytoken = 0;

    /* State.  */
    int yyn;
    int yylen = 0;
    int yystate = 0;

    /* Error handling.  */
    int yynerrs_ = 0;
    int yyerrstatus_ = 0;

    /// Semantic value of the lookahead.
    semantic_type yylval;
    /// Location of the lookahead.
    location_type yylloc;
    /// The locations where the error started and ended.
    location_type yyerror_range[3];

    /// $$.
    semantic_type yyval;
    /// @$.
    location_type yyloc;

    int yyresult;

    YYCDEBUG << "Starting parse" << std::endl;


    /* User initialization code.  */
    
/* Line 565 of lalr1.cc  */
#line 18 "../iimc/src/automata/AutoParser.yy"
{
  // Initialize the initial location.
  yylloc.begin.filename = yylloc.end.filename = &driver.file;
}

/* Line 565 of lalr1.cc  */
#line 368 "src/automata/AutoParser.cc"

    /* Initialize the stacks.  The initial state will be pushed in
       yynewstate, since the latter expects the semantical and the
       location values to have been already stored, initialize these
       stacks with a primary value.  */
    yystate_stack_ = state_stack_type (0);
    yysemantic_stack_ = semantic_stack_type (0);
    yylocation_stack_ = location_stack_type (0);
    yysemantic_stack_.push (yylval);
    yylocation_stack_.push (yylloc);

    /* New state.  */
  yynewstate:
    yystate_stack_.push (yystate);
    YYCDEBUG << "Entering state " << yystate << std::endl;

    /* Accept?  */
    if (yystate == yyfinal_)
      goto yyacceptlab;

    goto yybackup;

    /* Backup.  */
  yybackup:

    /* Try to take a decision without lookahead.  */
    yyn = yypact_[yystate];
    if (yy_pact_value_is_default_ (yyn))
      goto yydefault;

    /* Read a lookahead token.  */
    if (yychar == yyempty_)
      {
	YYCDEBUG << "Reading a token: ";
	yychar = yylex (&yylval, &yylloc, driver);
      }


    /* Convert token to internal form.  */
    if (yychar <= yyeof_)
      {
	yychar = yytoken = yyeof_;
	YYCDEBUG << "Now at end of input." << std::endl;
      }
    else
      {
	yytoken = yytranslate_ (yychar);
	YY_SYMBOL_PRINT ("Next token is", yytoken, &yylval, &yylloc);
      }

    /* If the proper action on seeing token YYTOKEN is to reduce or to
       detect an error, take that action.  */
    yyn += yytoken;
    if (yyn < 0 || yylast_ < yyn || yycheck_[yyn] != yytoken)
      goto yydefault;

    /* Reduce or error.  */
    yyn = yytable_[yyn];
    if (yyn <= 0)
      {
	if (yy_table_value_is_error_ (yyn))
	  goto yyerrlab;
	yyn = -yyn;
	goto yyreduce;
      }

    /* Shift the lookahead token.  */
    YY_SYMBOL_PRINT ("Shifting", yytoken, &yylval, &yylloc);

    /* Discard the token being shifted.  */
    yychar = yyempty_;

    yysemantic_stack_.push (yylval);
    yylocation_stack_.push (yylloc);

    /* Count tokens shifted since error; after three, turn off error
       status.  */
    if (yyerrstatus_)
      --yyerrstatus_;

    yystate = yyn;
    goto yynewstate;

  /*-----------------------------------------------------------.
  | yydefault -- do the default action for the current state.  |
  `-----------------------------------------------------------*/
  yydefault:
    yyn = yydefact_[yystate];
    if (yyn == 0)
      goto yyerrlab;
    goto yyreduce;

  /*-----------------------------.
  | yyreduce -- Do a reduction.  |
  `-----------------------------*/
  yyreduce:
    yylen = yyr2_[yyn];
    /* If YYLEN is nonzero, implement the default value of the action:
       `$$ = $1'.  Otherwise, use the top of the stack.

       Otherwise, the following line sets YYVAL to garbage.
       This behavior is undocumented and Bison
       users should not rely upon it.  */
    if (yylen)
      yyval = yysemantic_stack_[yylen - 1];
    else
      yyval = yysemantic_stack_[0];

    {
      slice<location_type, location_stack_type> slice (yylocation_stack_, yylen);
      YYLLOC_DEFAULT (yyloc, slice, yylen);
    }
    YY_REDUCE_PRINT (yyn);
    switch (yyn)
      {
	  case 3:

/* Line 690 of lalr1.cc  */
#line 73 "../iimc/src/automata/AutoParser.yy"
    { driver.eat->addAutomaton(*(yysemantic_stack_[(2) - (2)].aut));
                    delete (yysemantic_stack_[(2) - (2)].aut); }
    break;

  case 4:

/* Line 690 of lalr1.cc  */
#line 77 "../iimc/src/automata/AutoParser.yy"
    { (yyval.aut) = (yysemantic_stack_[(2) - (1)].aut);
                                                (yyval.aut)->badStates = *(yysemantic_stack_[(2) - (2)].states);
                                                delete (yysemantic_stack_[(2) - (2)].states); }
    break;

  case 5:

/* Line 690 of lalr1.cc  */
#line 81 "../iimc/src/automata/AutoParser.yy"
    { (yyval.aut) = (yysemantic_stack_[(2) - (2)].aut); }
    break;

  case 6:

/* Line 690 of lalr1.cc  */
#line 83 "../iimc/src/automata/AutoParser.yy"
    { (yyval.aut) = new Automaton; 
                    assert((yysemantic_stack_[(1) - (1)].aut)->states.size() == 1);
                    (yyval.aut)->states.push_back((yysemantic_stack_[(1) - (1)].aut)->states[0]);
                    (yyval.aut)->initialStates.insert((yyval.aut)->initialStates.end(), (yysemantic_stack_[(1) - (1)].aut)->initialStates.begin(), (yysemantic_stack_[(1) - (1)].aut)->initialStates.end());
                    (yyval.aut)->transitions.insert((yyval.aut)->transitions.end(),
                    (yysemantic_stack_[(1) - (1)].aut)->transitions.begin(), (yysemantic_stack_[(1) - (1)].aut)->transitions.end());
                    delete (yysemantic_stack_[(1) - (1)].aut); }
    break;

  case 7:

/* Line 690 of lalr1.cc  */
#line 90 "../iimc/src/automata/AutoParser.yy"
    { (yyval.aut) = (yysemantic_stack_[(2) - (1)].aut);
                    assert((yysemantic_stack_[(2) - (2)].aut)->states.size() == 1);
                    (yyval.aut)->states.push_back((yysemantic_stack_[(2) - (2)].aut)->states[0]);
                    (yyval.aut)->initialStates.insert((yyval.aut)->initialStates.end(), (yysemantic_stack_[(2) - (2)].aut)->initialStates.begin(), (yysemantic_stack_[(2) - (2)].aut)->initialStates.end());
                    (yyval.aut)->transitions.insert((yyval.aut)->transitions.end(),
                    (yysemantic_stack_[(2) - (2)].aut)->transitions.begin(), (yysemantic_stack_[(2) - (2)].aut)->transitions.end());
                    delete (yysemantic_stack_[(2) - (2)].aut); }
    break;

  case 8:

/* Line 690 of lalr1.cc  */
#line 99 "../iimc/src/automata/AutoParser.yy"
    { (yyval.aut) = (yysemantic_stack_[(2) - (2)].aut);
                        (yyval.aut)->initialStates.push_back((yysemantic_stack_[(2) - (2)].aut)->states[0]); }
    break;

  case 9:

/* Line 690 of lalr1.cc  */
#line 101 "../iimc/src/automata/AutoParser.yy"
    { (yyval.aut) = (yysemantic_stack_[(1) - (1)].aut); }
    break;

  case 10:

/* Line 690 of lalr1.cc  */
#line 104 "../iimc/src/automata/AutoParser.yy"
    { (yyval.aut) = new Automaton;
                                         (yyval.aut)->states.push_back((yysemantic_stack_[(4) - (1)].index));
                                         for(unsigned i = 0; i < (yysemantic_stack_[(4) - (3)].transitions)->size(); ++i)
                                           (*(yysemantic_stack_[(4) - (3)].transitions))[i].source = (yysemantic_stack_[(4) - (1)].index);
                                         (yyval.aut)->transitions = *(yysemantic_stack_[(4) - (3)].transitions);
                                         delete (yysemantic_stack_[(4) - (3)].transitions); }
    break;

  case 11:

/* Line 690 of lalr1.cc  */
#line 112 "../iimc/src/automata/AutoParser.yy"
    { (yyval.transitions) = new std::vector<Automaton::Transition>;
                                       (yyval.transitions)->push_back(*(yysemantic_stack_[(1) - (1)].transition));
                                       delete (yysemantic_stack_[(1) - (1)].transition); }
    break;

  case 12:

/* Line 690 of lalr1.cc  */
#line 115 "../iimc/src/automata/AutoParser.yy"
    { (yyval.transitions) = (yysemantic_stack_[(3) - (3)].transitions);
                                       (yyval.transitions)->push_back(*(yysemantic_stack_[(3) - (1)].transition));
                                       delete (yysemantic_stack_[(3) - (1)].transition); }
    break;

  case 13:

/* Line 690 of lalr1.cc  */
#line 120 "../iimc/src/automata/AutoParser.yy"
    { (yyval.transition) = new Automaton::Transition;
                                       (yyval.transition)->destination = (yysemantic_stack_[(4) - (4)].index);
                                       (yyval.transition)->label = (yysemantic_stack_[(4) - (2)].ival); }
    break;

  case 14:

/* Line 690 of lalr1.cc  */
#line 124 "../iimc/src/automata/AutoParser.yy"
    { (yyval.states) = (yysemantic_stack_[(2) - (2)].states); }
    break;

  case 15:

/* Line 690 of lalr1.cc  */
#line 126 "../iimc/src/automata/AutoParser.yy"
    { (yyval.states) = new std::vector<Automaton::State>;
                                      (yyval.states)->push_back((yysemantic_stack_[(1) - (1)].index)); }
    break;

  case 16:

/* Line 690 of lalr1.cc  */
#line 128 "../iimc/src/automata/AutoParser.yy"
    { (yyval.states) = (yysemantic_stack_[(2) - (1)].states);
                                      (yyval.states)->push_back((yysemantic_stack_[(2) - (2)].index)); }
    break;

  case 17:

/* Line 690 of lalr1.cc  */
#line 132 "../iimc/src/automata/AutoParser.yy"
    { (yyval.ival) = (yysemantic_stack_[(3) - (2)].ival); }
    break;

  case 18:

/* Line 690 of lalr1.cc  */
#line 133 "../iimc/src/automata/AutoParser.yy"
    { (yyval.ival) = driver.ev->btrue(); }
    break;

  case 19:

/* Line 690 of lalr1.cc  */
#line 134 "../iimc/src/automata/AutoParser.yy"
    { (yyval.ival) = driver.ev->bfalse(); }
    break;

  case 20:

/* Line 690 of lalr1.cc  */
#line 135 "../iimc/src/automata/AutoParser.yy"
    { (yyval.ival) = driver.ev->apply(Expr::Or, (yysemantic_stack_[(3) - (1)].ival), (yysemantic_stack_[(3) - (3)].ival)); }
    break;

  case 21:

/* Line 690 of lalr1.cc  */
#line 136 "../iimc/src/automata/AutoParser.yy"
    { (yyval.ival) = driver.ev->apply(Expr::And, (yysemantic_stack_[(3) - (1)].ival), (yysemantic_stack_[(3) - (3)].ival)); }
    break;

  case 22:

/* Line 690 of lalr1.cc  */
#line 137 "../iimc/src/automata/AutoParser.yy"
    { (yyval.ival) = driver.ev->apply(Expr::Not, driver.ev->apply(Expr::Equiv, (yysemantic_stack_[(3) - (1)].ival), (yysemantic_stack_[(3) - (3)].ival))); }
    break;

  case 23:

/* Line 690 of lalr1.cc  */
#line 138 "../iimc/src/automata/AutoParser.yy"
    { (yyval.ival) = driver.ev->apply(Expr::Equiv, (yysemantic_stack_[(3) - (1)].ival), (yysemantic_stack_[(3) - (3)].ival)); }
    break;

  case 24:

/* Line 690 of lalr1.cc  */
#line 139 "../iimc/src/automata/AutoParser.yy"
    { (yyval.ival) = driver.ev->apply(Expr::Implies, (yysemantic_stack_[(3) - (1)].ival), (yysemantic_stack_[(3) - (3)].ival)); }
    break;

  case 25:

/* Line 690 of lalr1.cc  */
#line 140 "../iimc/src/automata/AutoParser.yy"
    { (yyval.ival) = driver.ev->apply(Expr::Not, (yysemantic_stack_[(2) - (2)].ival)); }
    break;

  case 26:

/* Line 690 of lalr1.cc  */
#line 141 "../iimc/src/automata/AutoParser.yy"
    { (yyval.ival) = driver.ev->apply(Expr::Not, (yysemantic_stack_[(2) - (2)].ival)); }
    break;

  case 27:

/* Line 690 of lalr1.cc  */
#line 142 "../iimc/src/automata/AutoParser.yy"
    { if (driver.ev->varExists(*(yysemantic_stack_[(1) - (1)].sval))) {
                                        (yyval.ival) = driver.ev->newVar(*(yysemantic_stack_[(1) - (1)].sval));
                                        if (driver.eat->isOutput((yyval.ival)))
                                          (yyval.ival) = driver.eat->outputFnOf((yyval.ival));
                                      } else {
                                        error(yylloc, std::string("unknown variable: ") + *(yysemantic_stack_[(1) - (1)].sval));
                                        YYERROR;
                                      }
                                      delete (yysemantic_stack_[(1) - (1)].sval);
                                    }
    break;



/* Line 690 of lalr1.cc  */
#line 700 "src/automata/AutoParser.cc"
	default:
          break;
      }
    /* User semantic actions sometimes alter yychar, and that requires
       that yytoken be updated with the new translation.  We take the
       approach of translating immediately before every use of yytoken.
       One alternative is translating here after every semantic action,
       but that translation would be missed if the semantic action
       invokes YYABORT, YYACCEPT, or YYERROR immediately after altering
       yychar.  In the case of YYABORT or YYACCEPT, an incorrect
       destructor might then be invoked immediately.  In the case of
       YYERROR, subsequent parser actions might lead to an incorrect
       destructor call or verbose syntax error message before the
       lookahead is translated.  */
    YY_SYMBOL_PRINT ("-> $$ =", yyr1_[yyn], &yyval, &yyloc);

    yypop_ (yylen);
    yylen = 0;
    YY_STACK_PRINT ();

    yysemantic_stack_.push (yyval);
    yylocation_stack_.push (yyloc);

    /* Shift the result of the reduction.  */
    yyn = yyr1_[yyn];
    yystate = yypgoto_[yyn - yyntokens_] + yystate_stack_[0];
    if (0 <= yystate && yystate <= yylast_
	&& yycheck_[yystate] == yystate_stack_[0])
      yystate = yytable_[yystate];
    else
      yystate = yydefgoto_[yyn - yyntokens_];
    goto yynewstate;

  /*------------------------------------.
  | yyerrlab -- here on detecting error |
  `------------------------------------*/
  yyerrlab:
    /* Make sure we have latest lookahead translation.  See comments at
       user semantic actions for why this is necessary.  */
    yytoken = yytranslate_ (yychar);

    /* If not already recovering from an error, report this error.  */
    if (!yyerrstatus_)
      {
	++yynerrs_;
	if (yychar == yyempty_)
	  yytoken = yyempty_;
	error (yylloc, yysyntax_error_ (yystate, yytoken));
      }

    yyerror_range[1] = yylloc;
    if (yyerrstatus_ == 3)
      {
	/* If just tried and failed to reuse lookahead token after an
	 error, discard it.  */

	if (yychar <= yyeof_)
	  {
	  /* Return failure if at end of input.  */
	  if (yychar == yyeof_)
	    YYABORT;
	  }
	else
	  {
	    yydestruct_ ("Error: discarding", yytoken, &yylval, &yylloc);
	    yychar = yyempty_;
	  }
      }

    /* Else will try to reuse lookahead token after shifting the error
       token.  */
    goto yyerrlab1;


  /*---------------------------------------------------.
  | yyerrorlab -- error raised explicitly by YYERROR.  |
  `---------------------------------------------------*/
  yyerrorlab:

    /* Pacify compilers like GCC when the user code never invokes
       YYERROR and the label yyerrorlab therefore never appears in user
       code.  */
    if (false)
      goto yyerrorlab;

    yyerror_range[1] = yylocation_stack_[yylen - 1];
    /* Do not reclaim the symbols of the rule which action triggered
       this YYERROR.  */
    yypop_ (yylen);
    yylen = 0;
    yystate = yystate_stack_[0];
    goto yyerrlab1;

  /*-------------------------------------------------------------.
  | yyerrlab1 -- common code for both syntax error and YYERROR.  |
  `-------------------------------------------------------------*/
  yyerrlab1:
    yyerrstatus_ = 3;	/* Each real token shifted decrements this.  */

    for (;;)
      {
	yyn = yypact_[yystate];
	if (!yy_pact_value_is_default_ (yyn))
	{
	  yyn += yyterror_;
	  if (0 <= yyn && yyn <= yylast_ && yycheck_[yyn] == yyterror_)
	    {
	      yyn = yytable_[yyn];
	      if (0 < yyn)
		break;
	    }
	}

	/* Pop the current state because it cannot handle the error token.  */
	if (yystate_stack_.height () == 1)
	YYABORT;

	yyerror_range[1] = yylocation_stack_[0];
	yydestruct_ ("Error: popping",
		     yystos_[yystate],
		     &yysemantic_stack_[0], &yylocation_stack_[0]);
	yypop_ ();
	yystate = yystate_stack_[0];
	YY_STACK_PRINT ();
      }

    yyerror_range[2] = yylloc;
    // Using YYLLOC is tempting, but would change the location of
    // the lookahead.  YYLOC is available though.
    YYLLOC_DEFAULT (yyloc, yyerror_range, 2);
    yysemantic_stack_.push (yylval);
    yylocation_stack_.push (yyloc);

    /* Shift the error token.  */
    YY_SYMBOL_PRINT ("Shifting", yystos_[yyn],
		     &yysemantic_stack_[0], &yylocation_stack_[0]);

    yystate = yyn;
    goto yynewstate;

    /* Accept.  */
  yyacceptlab:
    yyresult = 0;
    goto yyreturn;

    /* Abort.  */
  yyabortlab:
    yyresult = 1;
    goto yyreturn;

  yyreturn:
    if (yychar != yyempty_)
      {
        /* Make sure we have latest lookahead translation.  See comments
           at user semantic actions for why this is necessary.  */
        yytoken = yytranslate_ (yychar);
        yydestruct_ ("Cleanup: discarding lookahead", yytoken, &yylval,
                     &yylloc);
      }

    /* Do not reclaim the symbols of the rule which action triggered
       this YYABORT or YYACCEPT.  */
    yypop_ (yylen);
    while (yystate_stack_.height () != 1)
      {
	yydestruct_ ("Cleanup: popping",
		   yystos_[yystate_stack_[0]],
		   &yysemantic_stack_[0],
		   &yylocation_stack_[0]);
	yypop_ ();
      }

    return yyresult;
  }

  // Generate an error message.
  std::string
  auto_parser::yysyntax_error_ (int yystate, int yytoken)
  {
    std::string yyres;
    // Number of reported tokens (one for the "unexpected", one per
    // "expected").
    size_t yycount = 0;
    // Its maximum.
    enum { YYERROR_VERBOSE_ARGS_MAXIMUM = 5 };
    // Arguments of yyformat.
    char const *yyarg[YYERROR_VERBOSE_ARGS_MAXIMUM];

    /* There are many possibilities here to consider:
       - If this state is a consistent state with a default action, then
         the only way this function was invoked is if the default action
         is an error action.  In that case, don't check for expected
         tokens because there are none.
       - The only way there can be no lookahead present (in yytoken) is
         if this state is a consistent state with a default action.
         Thus, detecting the absence of a lookahead is sufficient to
         determine that there is no unexpected or expected token to
         report.  In that case, just report a simple "syntax error".
       - Don't assume there isn't a lookahead just because this state is
         a consistent state with a default action.  There might have
         been a previous inconsistent state, consistent state with a
         non-default action, or user semantic action that manipulated
         yychar.
       - Of course, the expected token list depends on states to have
         correct lookahead information, and it depends on the parser not
         to perform extra reductions after fetching a lookahead from the
         scanner and before detecting a syntax error.  Thus, state
         merging (from LALR or IELR) and default reductions corrupt the
         expected token list.  However, the list is correct for
         canonical LR with one exception: it will still contain any
         token that will not be accepted due to an error action in a
         later state.
    */
    if (yytoken != yyempty_)
      {
        yyarg[yycount++] = yytname_[yytoken];
        int yyn = yypact_[yystate];
        if (!yy_pact_value_is_default_ (yyn))
          {
            /* Start YYX at -YYN if negative to avoid negative indexes in
               YYCHECK.  In other words, skip the first -YYN actions for
               this state because they are default actions.  */
            int yyxbegin = yyn < 0 ? -yyn : 0;
            /* Stay within bounds of both yycheck and yytname.  */
            int yychecklim = yylast_ - yyn + 1;
            int yyxend = yychecklim < yyntokens_ ? yychecklim : yyntokens_;
            for (int yyx = yyxbegin; yyx < yyxend; ++yyx)
              if (yycheck_[yyx + yyn] == yyx && yyx != yyterror_
                  && !yy_table_value_is_error_ (yytable_[yyx + yyn]))
                {
                  if (yycount == YYERROR_VERBOSE_ARGS_MAXIMUM)
                    {
                      yycount = 1;
                      break;
                    }
                  else
                    yyarg[yycount++] = yytname_[yyx];
                }
          }
      }

    char const* yyformat = 0;
    switch (yycount)
      {
#define YYCASE_(N, S)                         \
        case N:                               \
          yyformat = S;                       \
        break
        YYCASE_(0, YY_("syntax error"));
        YYCASE_(1, YY_("syntax error, unexpected %s"));
        YYCASE_(2, YY_("syntax error, unexpected %s, expecting %s"));
        YYCASE_(3, YY_("syntax error, unexpected %s, expecting %s or %s"));
        YYCASE_(4, YY_("syntax error, unexpected %s, expecting %s or %s or %s"));
        YYCASE_(5, YY_("syntax error, unexpected %s, expecting %s or %s or %s or %s"));
#undef YYCASE_
      }

    // Argument number.
    size_t yyi = 0;
    for (char const* yyp = yyformat; *yyp; ++yyp)
      if (yyp[0] == '%' && yyp[1] == 's' && yyi < yycount)
        {
          yyres += yytnamerr_ (yyarg[yyi++]);
          ++yyp;
        }
      else
        yyres += *yyp;
    return yyres;
  }


  /* YYPACT[STATE-NUM] -- Index in YYTABLE of the portion describing
     STATE-NUM.  */
  const signed char auto_parser::yypact_ninf_ = -14;
  const signed char
  auto_parser::yypact_[] =
  {
       -14,     8,   -14,     3,   -14,    -7,    -5,   -13,     3,   -14,
     -14,     7,   -14,   -14,     5,   -14,   -14,    13,    11,    14,
      12,   -14,   -14,   -14,   -14,    11,    11,    11,    -1,   -14,
       5,   -14,   -14,    -4,    11,    11,    11,    11,    11,    23,
     -14,   -14,     9,     9,     9,    21,   -14,   -14
  };

  /* YYDEFACT[S] -- default reduction number in state S.  Performed when
     YYTABLE doesn't specify something else to do.  Zero means the
     default is an error.  */
  const unsigned char
  auto_parser::yydefact_[] =
  {
         2,     0,     1,     0,     3,     0,     0,     0,     5,     6,
       9,     0,     4,     8,     0,     7,    15,    14,     0,     0,
      11,    16,    18,    19,    27,     0,     0,     0,     0,    10,
       0,    25,    26,     0,     0,     0,     0,     0,     0,     0,
      12,    17,    23,    24,    22,    20,    21,    13
  };

  /* YYPGOTO[NTERM-NUM].  */
  const signed char
  auto_parser::yypgoto_[] =
  {
       -14,   -14,   -14,   -14,   -14,    29,    37,    15,   -14,   -14,
     -14,     4
  };

  /* YYDEFGOTO[NTERM-NUM].  */
  const signed char
  auto_parser::yydefgoto_[] =
  {
        -1,     1,     4,     5,     8,     9,    10,    19,    20,    12,
      17,    28
  };

  /* YYTABLE[YYPACT[STATE-NUM]].  What to do in state STATE-NUM.  If
     positive, shift that token.  If negative, reduce the rule which
     number is the opposite.  If YYTABLE_NINF_, syntax error.  */
  const signed char auto_parser::yytable_ninf_ = -1;
  const unsigned char
  auto_parser::yytable_[] =
  {
        34,    35,    11,    34,    35,    14,     6,     7,     2,    36,
      37,    38,    36,    37,    38,     7,     3,    22,    23,    16,
      41,    39,    24,    37,    38,    21,    18,    25,    26,    31,
      32,    33,    30,    29,    27,    47,    38,    15,    42,    43,
      44,    45,    46,    13,     0,    40
  };

  /* YYCHECK.  */
  const signed char
  auto_parser::yycheck_[] =
  {
         4,     5,     9,     4,     5,    18,     3,    12,     0,    13,
      14,    15,    13,    14,    15,    12,     8,     6,     7,    12,
      24,    22,    11,    14,    15,    12,    21,    16,    17,    25,
      26,    27,    20,    19,    23,    12,    15,     8,    34,    35,
      36,    37,    38,     6,    -1,    30
  };

  /* STOS_[STATE-NUM] -- The (internal number of the) accessing
     symbol of state STATE-NUM.  */
  const unsigned char
  auto_parser::yystos_[] =
  {
         0,    26,     0,     8,    27,    28,     3,    12,    29,    30,
      31,     9,    34,    31,    18,    30,    12,    35,    21,    32,
      33,    12,     6,     7,    11,    16,    17,    23,    36,    19,
      20,    36,    36,    36,     4,     5,    13,    14,    15,    22,
      32,    24,    36,    36,    36,    36,    36,    12
  };

#if YYDEBUG
  /* TOKEN_NUMBER_[YYLEX-NUM] -- Internal symbol number corresponding
     to YYLEX-NUM.  */
  const unsigned short int
  auto_parser::yytoken_number_[] =
  {
         0,   256,   257,   258,   259,   260,   261,   262,   263,   264,
     265,   266,   267,    94,   124,    38,   126,    33,   123,   125,
      44,    91,    93,    40,    41
  };
#endif

  /* YYR1[YYN] -- Symbol number of symbol that rule YYN derives.  */
  const unsigned char
  auto_parser::yyr1_[] =
  {
         0,    25,    26,    26,    27,    28,    29,    29,    30,    30,
      31,    32,    32,    33,    34,    35,    35,    36,    36,    36,
      36,    36,    36,    36,    36,    36,    36,    36
  };

  /* YYR2[YYN] -- Number of symbols composing right hand side of rule YYN.  */
  const unsigned char
  auto_parser::yyr2_[] =
  {
         0,     2,     0,     2,     2,     2,     1,     2,     2,     1,
       4,     1,     3,     4,     2,     1,     2,     3,     1,     1,
       3,     3,     3,     3,     3,     2,     2,     1
  };

#if YYDEBUG || YYERROR_VERBOSE || YYTOKEN_TABLE
  /* YYTNAME[SYMBOL-NUM] -- String name of the symbol SYMBOL-NUM.
     First, the terminals, then, starting at \a yyntokens_, nonterminals.  */
  const char*
  const auto_parser::yytname_[] =
  {
    "\"end of file\"", "error", "$undefined", "\"=>\"", "\"==\"", "\"->\"",
  "TRUE", "FALSE", "\"Structure\"", "\"Buechi Fairness\"", "INVALID_CHAR",
  "\"identifier\"", "STATE", "'^'", "'|'", "'&'", "'~'", "'!'", "'{'",
  "'}'", "','", "'['", "']'", "'('", "')'", "$accept", "input",
  "automaton", "structure_section", "structure", "state", "state_def",
  "transitions", "transition", "fairness_section", "fairness",
  "expression", 0
  };
#endif

#if YYDEBUG
  /* YYRHS -- A `-1'-separated list of the rules' RHS.  */
  const auto_parser::rhs_number_type
  auto_parser::yyrhs_[] =
  {
        26,     0,    -1,    -1,    26,    27,    -1,    28,    34,    -1,
       8,    29,    -1,    30,    -1,    29,    30,    -1,     3,    31,
      -1,    31,    -1,    12,    18,    32,    19,    -1,    33,    -1,
      33,    20,    32,    -1,    21,    36,    22,    12,    -1,     9,
      35,    -1,    12,    -1,    35,    12,    -1,    23,    36,    24,
      -1,     6,    -1,     7,    -1,    36,    14,    36,    -1,    36,
      15,    36,    -1,    36,    13,    36,    -1,    36,     4,    36,
      -1,    36,     5,    36,    -1,    16,    36,    -1,    17,    36,
      -1,    11,    -1
  };

  /* YYPRHS[YYN] -- Index of the first RHS symbol of rule number YYN in
     YYRHS.  */
  const unsigned char
  auto_parser::yyprhs_[] =
  {
         0,     0,     3,     4,     7,    10,    13,    15,    18,    21,
      23,    28,    30,    34,    39,    42,    44,    47,    51,    53,
      55,    59,    63,    67,    71,    75,    78,    81
  };

  /* YYRLINE[YYN] -- Source line where rule number YYN was defined.  */
  const unsigned char
  auto_parser::yyrline_[] =
  {
         0,    72,    72,    73,    77,    81,    83,    90,    99,   101,
     104,   112,   115,   120,   124,   126,   128,   132,   133,   134,
     135,   136,   137,   138,   139,   140,   141,   142
  };

  // Print the state stack on the debug stream.
  void
  auto_parser::yystack_print_ ()
  {
    *yycdebug_ << "Stack now";
    for (state_stack_type::const_iterator i = yystate_stack_.begin ();
	 i != yystate_stack_.end (); ++i)
      *yycdebug_ << ' ' << *i;
    *yycdebug_ << std::endl;
  }

  // Report on the debug stream that the rule \a yyrule is going to be reduced.
  void
  auto_parser::yy_reduce_print_ (int yyrule)
  {
    unsigned int yylno = yyrline_[yyrule];
    int yynrhs = yyr2_[yyrule];
    /* Print the symbols being reduced, and their result.  */
    *yycdebug_ << "Reducing stack by rule " << yyrule - 1
	       << " (line " << yylno << "):" << std::endl;
    /* The symbols being reduced.  */
    for (int yyi = 0; yyi < yynrhs; yyi++)
      YY_SYMBOL_PRINT ("   $" << yyi + 1 << " =",
		       yyrhs_[yyprhs_[yyrule] + yyi],
		       &(yysemantic_stack_[(yynrhs) - (yyi + 1)]),
		       &(yylocation_stack_[(yynrhs) - (yyi + 1)]));
  }
#endif // YYDEBUG

  /* YYTRANSLATE(YYLEX) -- Bison symbol number corresponding to YYLEX.  */
  auto_parser::token_number_type
  auto_parser::yytranslate_ (int t)
  {
    static
    const token_number_type
    translate_table[] =
    {
           0,     2,     2,     2,     2,     2,     2,     2,     2,     2,
       2,     2,     2,     2,     2,     2,     2,     2,     2,     2,
       2,     2,     2,     2,     2,     2,     2,     2,     2,     2,
       2,     2,     2,    17,     2,     2,     2,     2,    15,     2,
      23,    24,     2,     2,    20,     2,     2,     2,     2,     2,
       2,     2,     2,     2,     2,     2,     2,     2,     2,     2,
       2,     2,     2,     2,     2,     2,     2,     2,     2,     2,
       2,     2,     2,     2,     2,     2,     2,     2,     2,     2,
       2,     2,     2,     2,     2,     2,     2,     2,     2,     2,
       2,    21,     2,    22,    13,     2,     2,     2,     2,     2,
       2,     2,     2,     2,     2,     2,     2,     2,     2,     2,
       2,     2,     2,     2,     2,     2,     2,     2,     2,     2,
       2,     2,     2,    18,    14,    19,    16,     2,     2,     2,
       2,     2,     2,     2,     2,     2,     2,     2,     2,     2,
       2,     2,     2,     2,     2,     2,     2,     2,     2,     2,
       2,     2,     2,     2,     2,     2,     2,     2,     2,     2,
       2,     2,     2,     2,     2,     2,     2,     2,     2,     2,
       2,     2,     2,     2,     2,     2,     2,     2,     2,     2,
       2,     2,     2,     2,     2,     2,     2,     2,     2,     2,
       2,     2,     2,     2,     2,     2,     2,     2,     2,     2,
       2,     2,     2,     2,     2,     2,     2,     2,     2,     2,
       2,     2,     2,     2,     2,     2,     2,     2,     2,     2,
       2,     2,     2,     2,     2,     2,     2,     2,     2,     2,
       2,     2,     2,     2,     2,     2,     2,     2,     2,     2,
       2,     2,     2,     2,     2,     2,     2,     2,     2,     2,
       2,     2,     2,     2,     2,     2,     1,     2,     3,     4,
       5,     6,     7,     8,     9,    10,    11,    12
    };
    if ((unsigned int) t <= yyuser_token_number_max_)
      return translate_table[t];
    else
      return yyundef_token_;
  }

  const int auto_parser::yyeof_ = 0;
  const int auto_parser::yylast_ = 45;
  const int auto_parser::yynnts_ = 12;
  const int auto_parser::yyempty_ = -2;
  const int auto_parser::yyfinal_ = 2;
  const int auto_parser::yyterror_ = 1;
  const int auto_parser::yyerrcode_ = 256;
  const int auto_parser::yyntokens_ = 25;

  const unsigned int auto_parser::yyuser_token_number_max_ = 267;
  const auto_parser::token_number_type auto_parser::yyundef_token_ = 2;


} // autoparser

/* Line 1136 of lalr1.cc  */
#line 1219 "src/automata/AutoParser.cc"


/* Line 1138 of lalr1.cc  */
#line 153 "../iimc/src/automata/AutoParser.yy"


void
autoparser::auto_parser::error(const autoparser::auto_parser::location_type& l,
                      const std::string& m)
{
  driver.error(l, m);
}

