%token PACK AS UNPACK FOLD UNFOLD
%token PLUS MINUS TIMES /* these are the binary symbols */
%token FORALL EXISTS MU
%token UNIT INT
%token LANGLE RANGLE LBRACKET RBRACKET LBRACE RBRACE LPAREN RPAREN
%token DOT COMMA COLON SEMICOLON DOUBLECOLON ARROW QUESTION CAST
%token LAMBDA IF0 PI
%token<string> A_IDENTIFIER Z_IDENTIFIER E_IDENTIFIER OTHER_IDENTIFIER
%token<int> INTEGER
%token<string> REGISTER
%token EOF

%left PLUS MINUS
%left TIMES

/*
%start<Ftal.F.t> f_type_eof
*/
%start<Ftal.F.exp> f_expression_eof

%{ open Ftal
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
f_expression_eof: e=f_expression EOF { e }

conv_lbl:
| PLUS a=type_name { () }
| MINUS a=type_name { () }

f_type:
| alpha=f_type_variable { F.TVar alpha }
| UNIT { F.TUnit }
| INT { F.TInt }
| LPAREN taus=separated_list(COMMA,f_type) RPAREN ARROW tau=f_type
  { F.TArrow (taus, tau) }
| mu=f_mu_type { let (alpha, tau) = mu in F.TRec (alpha, tau) }
| taus=tuple(f_type) { F.TTuple taus }
| TIMES { F.TUnit }

  f_type_variable: alpha=identifier { alpha }
  f_mu_type: MU alpha=f_type_variable DOT tau=f_type { (alpha, tau) }

f_simple_expression:
| x=f_term_variable { F.EVar (cpos $startpos, x) }
| LPAREN RPAREN { F.EUnit (cpos $startpos)}
| n=nat { F.EInt (cpos $startpos, n) }
| es=tuple(f_expression) { F.ETuple (cpos $startpos, es) }
| PI n=nat LPAREN e=f_expression RPAREN { F.EPi (cpos $startpos, n, e) }
| LPAREN e=f_expression RPAREN { e }
| LPAREN e=f_expression COLON t1=f_type a=conv_lbl CAST t2 = f_type RPAREN { e }
| LPAREN e=f_expression COLON t1=f_type CAST t2 = f_type RPAREN { e }

f_app_expression:
| e=f_simple_expression { e }
| e=f_simple_expression args=nonempty_list(f_simple_expression) { F.EApp (cpos $startpos, e, args) }

f_arith_expression:
| MINUS n=nat { F.EInt (cpos $startpos,(-n)) }
| e1=f_arith_expression op=infixop e2=f_arith_expression { F.EBinop (cpos $startpos, e1, op, e2) }
| e=f_app_expression { e }

f_expression:
| IF0 p=f_simple_expression e1=f_simple_expression e2=f_simple_expression
  { F.EIf0 (cpos $startpos, p, e1, e2) }
| LAMBDA args=f_telescope DOT body=f_expression
  { F.ELam (cpos $startpos, args, body) }
| FOLD mu=mayparened(f_mu_type) e=f_expression
  { let (alpha, tau) = mu in F.EFold (cpos $startpos, alpha, tau, e) }
| UNFOLD e=f_expression { F.EUnfold (cpos $startpos, e) }
| e=f_arith_expression { e }

  f_term_variable: x=identifier { x }

  f_telescope:
  | LPAREN args=separated_list(COMMA, decl(f_term_variable, f_type)) RPAREN
  { args }

  %inline infixop:
  | PLUS { F.BPlus }
  | MINUS { F.BMinus }
  | TIMES { F.BTimes }


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
| alpha=A_IDENTIFIER { alpha }

type_name:
| alpha=A_IDENTIFIER { alpha }

location:
| l=identifier { l }

identifier:
| id=A_IDENTIFIER { id }
| id=OTHER_IDENTIFIER { id }

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
