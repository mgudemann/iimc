%{                                            /* -*- C++ -*- */
# include <cstdlib>
# include <cerrno>
# include <climits>
# include <string>
# include "PropCtlWrapper.h"
# include "PropCtlParser.hh"

/* Work around an incompatibility in flex (at least versions
   2.5.31 through 2.5.33): it generates code that does
   not conform to C89.  See Debian bug 333231
   <http://bugs.debian.org/cgi-bin/bugreport.cgi?bug=333231>.  */
# undef yywrap
# define yywrap() 1

/* By default yylex returns int, we use token_type.
   Unfortunately yyterminate by default returns 0, which is
   not of token_type.  */
#define yyterminate() return token::END
%}

/* the never-interactive option is a hack for cygwin
 * compilation with g++ 4.3.4 and 4.5.3.  It is hoped that
 * it will soon become unnecessary. */
%option noyywrap nounput prefix="ctl" batch debug never-interactive

id    [a-zA-Z][a-zA-Z_0-9\.\*<>]*
blank [ \t;]
cmnt  #.*

%{
# define YY_USER_ACTION  yylloc->columns(yyleng);
%}
%%
%{
  yylloc->step();
%}
{blank}+   yylloc->step();
[\n]+      yylloc->lines(yyleng); yylloc->step();
{cmnt}     yylloc->step();

%{
  typedef yy::ctl_parser::token token;
%}
        /* Convert ints to the actual type of tokens.  */
[&|~!^()]  return yy::ctl_parser::token_type(yytext[0]);
"=="       return token::EQUIV;
"->"       return token::IMPLIES;
EX         return token::EX;
EF         return token::EF;
EG         return token::EG;
AX         return token::AX;
AF         return token::AF;
AG         return token::AG;
E          return token::EQUANT;
A          return token::AQUANT;
U          return token::UNTIL;
R          return token::RELEASES;
W          return token::WEAK_UNTIL;
true       return token::TRUE;
false      return token::FALSE;
{id}       yylval->sval = new std::string(yytext); return token::IDENTIFIER;
.          { driver.error(*yylloc, std::string("invalid character: ") + yytext[0]);
             return token::INVALID_CHAR; }
%%

void
ctl_driver::scan_begin()
{
  yy_flex_debug = trace_scanning;
  if (file == "-")
    yyin = stdin;
  else if (!(yyin = fopen(file.c_str(), "r")))
    {
      error(std::string("cannot open ") + file);
      exit(1);
    }
}

void
ctl_driver::scan_end()
{
  fclose(yyin);
}
