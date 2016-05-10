%{                                            /* -*- C++ -*- */
# include <cstdlib>
# include <cerrno>
# include <climits>
# include <string>
# include "AutoWrapper.h"
# include "AutoParser.hh"

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
%option noyywrap nounput prefix="auto" batch debug never-interactive

num   [0-9]+
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
  typedef autoparser::auto_parser::token token;
%}
        /* Convert ints to the actual type of tokens.  */
[&|~!^(){},\[\]]  return autoparser::auto_parser::token_type(yytext[0]);
"=>"       return token::INIT;
"=="       return token::EQUIV;
"->"       return token::IMPLIES;
true       return token::TRUE;
false      return token::FALSE;
"Structure"  return token::STRUCTURE;
"Buechi Fairness" return token::FAIRNESS;
{id}       yylval->sval = new std::string(yytext); return token::IDENTIFIER;
{num}      { std::stringstream ss(yytext); ss >> yylval->index;
             return token::STATE; }
.          { driver.error(*yylloc, std::string("invalid character: ") + yytext[0]);
             return token::INVALID_CHAR; }
%%

void
auto_driver::scan_begin()
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
auto_driver::scan_end()
{
  fclose(yyin);
}
