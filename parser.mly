%token PLUS MINUS TIMES EQUAL /* these are the binary symbols */
%token FORALL CROSS BLAME
%token INT BOOL
%token LANGLE RANGLE LBRACKET RBRACKET LBRACE RBRACE LPAREN RPAREN
%token DOT COMMA COLON ARROW CAST
%token LAMBDA BIGLAMBDA IF THEN ELSE LET IN PI1 PI2
%token<string> A_IDENTIFIER OTHER_IDENTIFIER CAP_IDENTIFIER
%token TRUE FALSE
%token<int> INTEGER
%token EOF

%left EQUAL
%left PLUS MINUS
%left TIMES

/*
%start<Ftal.F.t> f_type_eof
*/
%start<Ftal.Lang.exp> expression_eof

%{ open Ftal
  open Lang
%}


%%

/*
memory_eof: m=memory EOF { m }
instruction_sequence_eof: i=instruction_sequence EOF { i }
heap_fragment_eof: h=heap_fragment EOF { h }
word_value_eof: w=word_value EOF { w }
small_value_eof: u=small_value EOF { u }
type_env_eof: delta=type_env EOF { delta }
f_type_eof: tau=f_type EOF { tau }
*/

expression_eof: e=expression EOF { e }

conv_lbl:
| PLUS a=type_name { PosConvLbl a }
| MINUS a=type_name { NegConvLbl a }

simple_typ:
| INT { IntTy }
| BOOL { BoolTy }
| TIMES { AnyTy }
| x=type_variable { VarTy x }
| LANGLE t1=typ COMMA t2=typ RANGLE { PairTy (t1,t2) }
| LPAREN t=typ RPAREN { t }

typ:
/* TODO: enable removing parens where possible */
| t1=simple_typ ARROW t2=typ { FunTy (t1, t2) }
| FORALL x=identifier DOT t=typ { ForallTy (x, t) }
| t=simple_typ { t }

simple_expression:
| x=term_variable { VarExp x }
| n=nat { IntExp n }
| b=TRUE { BoolExp true }
| b=FALSE { BoolExp false }
| LANGLE e1=expression COMMA e2=expression RANGLE { PairExp (e1,e2) }
| PI1 e=simple_expression { Proj1Exp e }
| PI2 e=simple_expression { Proj2Exp e }
/*TODO: add code positions */
| BLAME COLON t=parened(typ) {BlameExp (PosCompLbl (CodeLoc(-1,-1)), t)}
| LPAREN e=expression RPAREN { e }

app_expression:
| e=app_expression t=bracketed(typ) { InstExp(e,t) }
| e=app_expression arg=simple_expression { AppExp (e, arg) }
| e=simple_expression { e }

arith_expression:
| MINUS n=nat { IntExp (-n) }
| e1=arith_expression op=infixop e2=arith_expression { OpExp (op, e1, e2) }
| e=app_expression { e }

cast_expression:
| e=cast_expression COLON t1=typ a=conv_lbl CAST t2=typ
  { ConvExp (e, t1, a, t2) }
| e=cast_expression COLON t1=typ CAST t2=typ
  { CastExp (e, t1, PosCompLbl (CodeLoc (-1,-1)), t2) (* TODO: label *) }
| e=arith_expression { e }

expression:
| IF p=simple_expression THEN e1=simple_expression ELSE e2=simple_expression
  { IfExp (p, e1, e2) }
| LAMBDA LPAREN x=term_variable COLON t=typ RPAREN DOT body=expression
  { LamExp (x, t, body) }
| LET x=term_variable COLON t=typ EQUAL rhs=expression IN body=expression
  { AppExp (LamExp (x, t, body), rhs) }
| BIGLAMBDA x=identifier DOT body=expression { AbstrExp (x,body)}
| e=cast_expression { e }

  term_variable: x=identifier { x }

  %inline infixop:
  | PLUS { Plus }
  | MINUS { Minus }
  | TIMES { Times }
  | EQUAL { Equal }

/*type_env: li=bracketed(simple_type_env) { li }
simple_type_env: li=separated_list(COMMA, type_env_elem) { li }

  type_env_elem:
  | alpha=type_variable { DAlpha alpha }*/


  binding(variable, value):
  | x=variable ARROW v=value { (x, v) }

  decl(variable,spec):
  | x=variable COLON s=spec { (x, s) }

/*
stack: ws=list(w=word_value DOUBLECOLON {w}) NIL { ws }
*/

type_variable:
| x=CAP_IDENTIFIER { x }

type_name:
| alpha=A_IDENTIFIER { alpha }

location:
| l=identifier { l }

identifier:
| id=A_IDENTIFIER { id }
| id=OTHER_IDENTIFIER { id }
| id=CAP_IDENTIFIER { id } /*TODO: temp*/

nat:
| n=INTEGER { n }

tuple(elem):
| LANGLE elems=separated_list(COMMA, elem) RANGLE { elems }

%inline mayparened(elem):
| x=elem { x }
| x=parened(elem) { x }

%inline braced(elem):
| LBRACE x=elem RBRACE {x}

%inline bracketed(elem):
| LBRACKET x=elem RBRACKET {x}

%inline parened(elem):
| LPAREN x=elem RPAREN {x}

%inline angled(elem):
| LANGLE x=elem RANGLE {x}
