structure Tokens = Tokens

type pos = int
type svalue = Tokens.svalue
type ('a,'b) token = ('a,'b) Tokens.token
type lexresult= (svalue,pos) token

val pos = ref 1;
fun eof () = Tokens.EOF(!pos,!pos);
val cstring = ref "";
val temporary = ref "";
%%
%header (functor ObjectTypeLexFun(structure Tokens: ObjectType_TOKENS));
%reject 
capital=[A-Z];
lowercase=[a-z];
letter=[a-zA-Z];
alnum=[A-Za-z0-9];
digit=[0-9];
ws=[\ \t];
%s IN_CSTRING;

%%
<INITIAL> --(\n|[^-\n]([^-\n]|-[^-\n])*(\n|-(-|\n)))	=> 
			(pos := (!pos + Useful.numberofnl yytext) ;lex());
<INITIAL> \n				=> (pos := (!pos) + 1 ; lex());
<INITIAL> {ws}+				=> (lex());
<INITIAL> \{				=> (Tokens.LBRACE(!pos,!pos));
<INITIAL> }				=> (Tokens.RBRACE(!pos,!pos));
<INITIAL> ::\=				=> (Tokens.LETITBE(!pos,!pos));
<INITIAL> \.\.				=> (Tokens.DOUBLEDOT(!pos,!pos));
<INITIAL> \(				=> (Tokens.LPAREN(!pos,!pos));
<INITIAL> \)				=> (Tokens.RPAREN(!pos,!pos));
<INITIAL> ,				=> (Tokens.COMMA(!pos,!pos));
<INITIAL> 0|[1-9]{digit}*		=> 
		(Tokens.NUMBER(valOf(Int.fromString yytext),!pos,!pos));
<INITIAL> {capital}({letter}|-{letter})+ 
=> (case yytext of "ACCESS"		=> Tokens.ACCESS(!pos,!pos) 
		| "ACCESS"		=> Tokens.ACCESS(!pos,!pos)
		| "BEGIN"		=> Tokens.BEGIN(!pos,!pos)
		| "Counter"		=> Tokens.COUNTER(!pos,!pos)
		| "DEFINITIONS"		=> Tokens.DEFINITIONS(!pos,!pos)
		| "DESCRIPTION"		=> Tokens.DESCRIPTION(!pos,!pos)
		| "DisplayString"	=> Tokens.DISPLAYSTRING(!pos,!pos)
		| "END"			=> Tokens.END(!pos,!pos)
		| "Gauge"		=> Tokens.GAUGE(!pos,!pos)
		| "IDENTIFIER"		=> Tokens.IDENTIFIER(!pos,!pos)
		| "INDEX"		=> Tokens.INDEX(!pos,!pos)
		| "INTEGER"		=> Tokens.INTEGER(!pos,!pos)
		| "IpAddress"		=> Tokens.IPADDRESS(!pos,!pos)
		| "NetworkAddress"	=> Tokens.NETWORKADDRESS(!pos,!pos) 
		| "NULL"		=> Tokens.NULL (!pos,!pos)
		| "OF"			=> Tokens.OF(!pos,!pos)
		| "OBJECT"		=> Tokens.OBJECT(!pos,!pos)
		| "OBJECT-TYPE"		=> Tokens.OBJECT_TYPE(!pos,!pos)
		| "PhysAddress"		=> Tokens.PHYSADDRESS(!pos,!pos)
		| "SEQUENCE"		=> Tokens.SEQUENCE(!pos,!pos)
		| "SIZE"		=> Tokens.SIZE(!pos,!pos)
		| "STATUS"		=> Tokens.STATUS(!pos,!pos)
		| "SYNTAX"		=> Tokens.SYNTAX(!pos,!pos)
		| "TimeTicks"		=> Tokens.TIMETICKS(!pos,!pos)
		| _ 			=> REJECT()	);
<INITIAL> {capital}({alnum}|-{alnum})*	=> (Tokens.REFERENCE(yytext,!pos,!pos));
<INITIAL> {lowercase}({alnum}|-{alnum})*	
=> (case yytext of "read-only"		=> Tokens.READONLY_(!pos,!pos)
		|  "read-write"		=> Tokens.READWRITE_(!pos,!pos)
		|  "write-only"		=> Tokens.WRITEONLY_(!pos,!pos)
		|  "not-accessible"	=> Tokens.NOTACCESSIBLE_(!pos,!pos)
		|  "mandatory"		=> Tokens.MANDATORY_(!pos,!pos)
		|  "optional"		=> Tokens.OPTIONAL_(!pos,!pos)
		|  "obsolete"		=> Tokens.OBSOLETE_(!pos,!pos)
		|  "deprecated"		=> Tokens.DEPRECATED_(!pos,!pos)
		|  _			=> REJECT()	);
<INITIAL> {lowercase}({alnum}|-{alnum})* => (Tokens.ID(yytext,!pos,!pos));
<INITIAL> \" 				=> (YYBEGIN IN_CSTRING;lex());
<IN_CSTRING> \"\"			=> (cstring := (!cstring) ^ "\"";
						lex());
<IN_CSTRING> [^\"]+			=> (cstring := (!cstring) ^ yytext;
						lex());
<IN_CSTRING> \"		=> (temporary := Useful.onespace(!cstring);
				pos := (!pos) + Useful.numberofnl(!cstring);
				cstring := "";
				YYBEGIN INITIAL;
				Tokens.CSTRING(!temporary,!pos,!pos) );
<INITIAL> . => (Useful.error("ignoring bad character" ^ yytext,!pos); lex());
