(* Standard lex file format, again borrowed 
	from ml-yacc/examples/calc/calc.lex and 
	modified as per requirement*)

structure Tokens = Tokens

type pos = int
type svalue = Tokens.svalue
type ('a,'b) token = ('a,'b) Tokens.token
type lexresult= (svalue,pos) token


val pos = ref 0
fun init () = ()
fun eof () = Tokens.EOF(!pos,!pos)
fun error (e,l : int,_) = TextIO.output (TextIO.stdOut, String.concat[
	"line ", (Int.toString l), ": ", e, "\n"])

%%
%header (functor LcsLexFun(structure Tokens: Lcs_TOKENS));
str = [A-Za-z0-9];
ws  = [\ \t];

%%
\n 		=> (pos := (!pos) + 1; lex());
{ws}	=> (lex());
{ws}+	=> (Tokens.SPACEVAL(yytext,!pos,!pos));

"IFF"{ws}*	=> (Tokens.IFFVAL(!pos,!pos));
"IF"{ws}*	=> (Tokens.IFVAL(!pos,!pos));
"THEN"{ws}*	=> (Tokens.THENVAL(!pos,!pos));
"ELSE"{ws}*	=> (Tokens.ELSEVAL(!pos,!pos));
"AND"{ws}*	=> (Tokens.ANDVAL(!pos,!pos));
"OR"{ws}*	=> (Tokens.ORVAL(!pos,!pos));
"NOT"{ws}*	=> (Tokens.NOTVAL(!pos,!pos));
"("{ws}*		=> (Tokens.LEFTP(!pos,!pos));
")"{ws}*		=> (Tokens.RIGHTP(!pos,!pos));
"TRUE"{ws}*	=> (Tokens.TRUEVAL(!pos,!pos));
"FALSE"{ws}*	=> (Tokens.FALSEVAL(!pos,!pos));
{str}+	=> (Tokens.ATOMVAL(yytext,!pos,!pos));
.		=> (error ("ignoring bad character "^yytext,!pos,!pos);
			lex());
