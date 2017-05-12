%token PACK AS UNPACK FOLD UNFOLD
%token PLUS MINUS TIMES /* these are the binary symbols */
%token FORALL EXISTS MU
%token UNIT INT
%token LANGLE RANGLE LBRACKET RBRACKET LBRACE RBRACE LPAREN RPAREN
%token DOT COMMA COLON SEMICOLON DOUBLECOLON ARROW QUESTION
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
   open TAL

   (* NOTE(gasche 2017-02-19): see #5. We merged the syntactic categories of word
      values and small values, as having both created a lot of conflicts
      in the grammar. Whenever we want to parse a word value (a small value
      without registers), we parse a small value then call the [lower_value]
      function below, which partially projects into word values. *)
   exception LowerValueError of u
   let rec lower_value : u -> w = function
     | UW (_,w) -> w
     | UR (_,_) as u -> raise (LowerValueError u)
     | UPack (l, t, u, s, t') -> WPack (l, t, lower_value u, s, t')
     | UFold (l, s, t, u) -> WFold (l, s, t, lower_value u)
     | UApp (l, u, omegas) -> WApp (l, lower_value u, omegas)
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

f_type:
| alpha=f_type_variable { F.TVar alpha }
| UNIT { F.TUnit }
| INT { F.TInt }
| LPAREN taus=separated_list(COMMA,f_type) RPAREN ARROW tau=f_type
  { F.TArrow (taus, tau) }
| LPAREN taus=separated_list(COMMA,f_type) RPAREN
  LBRACKET sin=stack_prefix RBRACKET
  ARROW
  LBRACKET sout=stack_prefix RBRACKET
  tau=f_type
  { F.TArrowMod (taus, sin, sout, tau) }
| mu=f_mu_type { let (alpha, tau) = mu in F.TRec (alpha, tau) }
| taus=tuple(f_type) { F.TTuple taus }

  f_type_variable: alpha=identifier { alpha }
  f_mu_type: MU alpha=f_type_variable DOT tau=f_type { (alpha, tau) }

f_simple_expression:
| x=f_term_variable { F.EVar (cpos $startpos, x) }
| LPAREN RPAREN { F.EUnit (cpos $startpos)}
| n=nat { F.EInt (cpos $startpos, n) }
| es=tuple(f_expression) { F.ETuple (cpos $startpos, es) }
| PI n=nat LPAREN e=f_expression RPAREN { F.EPi (cpos $startpos, n, e) }
| LPAREN e=f_expression RPAREN { e }

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
| LAMBDA
  LBRACKET sin=stack_prefix RBRACKET
  LBRACKET sout=stack_prefix RBRACKET
  args=f_telescope DOT body=f_expression
  { F.ELamMod (cpos $startpos, args, sin, sout, body) }
| FOLD mu=mayparened(f_mu_type) e=f_expression
  { let (alpha, tau) = mu in F.EFold (cpos $startpos, alpha, tau, e) }
| UNFOLD e=f_expression { F.EUnfold (cpos $startpos, e) }
| e=f_arith_expression { e }

  stack_typing_annot:
  | QUESTION { None }
  | sigma=stack_typing { Some sigma }

  f_term_variable: x=identifier { x }

  f_telescope:
  | LPAREN args=separated_list(COMMA, decl(f_term_variable, f_type)) RPAREN
  { args }

  %inline infixop:
  | PLUS { F.BPlus }
  | MINUS { F.BMinus }
  | TIMES { F.BTimes }

value_type:
| alpha=type_variable { TVar alpha }
| UNIT { TUnit }
| INT { TInt }
| ex=existential_type { let (alpha, tau) = ex in TExists (alpha, tau) }
| mu=mu_type { let (alpha, tau) = mu in TRec (alpha, tau) }

  existential_type:
  | EXISTS alpha=type_variable DOT tau=value_type { (alpha, tau) }
  mu_type:
  | MU alpha=type_variable DOT tau=value_type { (alpha, tau) }

register:
| r=REGISTER { r }

word_value: w=small_value { lower_value w }

simple_small_value:
| LPAREN u=small_value RPAREN { u }
| LPAREN RPAREN { UW (cpos $startpos, WUnit (cpos $startpos)) }
| n=nat { UW (cpos $startpos, WInt (cpos $startpos, n)) }
| l=location { UW (cpos $startpos, WLoc (cpos $startpos, l)) }
| r=register { UR (cpos $startpos, r) }
| p=pack(small_value)
  { let (tau, u, alpha, tau') = p in UPack (cpos $startpos, tau, u, alpha, tau') }

small_value:
| MINUS n=nat { UW (cpos $startpos, WInt (cpos $startpos, (-n))) }
| u=simple_small_value { u }
| f=fold(small_value)
  { let (alpha, tau, u) = f in UFold (cpos $startpos, alpha, tau, u) }
| a=app(simple_small_value)
  { let (u, omega) = a in UApp (cpos $startpos, u, omega) }

  fold(value):
  | FOLD mu=mayparened(mu_type) v=value
    { let (alpha, tau) = mu in (alpha, tau, v) }

  pack(value):
  | PACK LANGLE tau=value_type COMMA v=value RANGLE
    AS goal=mayparened(existential_type)
    { let (alpha,tau') = goal in (tau, v, alpha, tau') }

  app(value):
  | v=value LBRACKET omegas=separated_list(COMMA,type_instantiation) RBRACKET
    { (v, omegas) }

type_instantiation:
| tau=value_type { OT tau }
| sigma=stack_typing { OS sigma }

/*
register_typing: li=bracketed(simple_register_typing) { li }
*/
simple_register_typing: li=separated_list(COMMA, decl(register, value_type)) { li }

stack_prefix:
  | DOUBLECOLON { [] }
  | tau=value_type taus=rest_stack_prefix { tau :: taus }

  rest_stack_prefix:
  | DOUBLECOLON { [] }
  | DOUBLECOLON tau=value_type taus=rest_stack_prefix { tau :: taus }

stack_typing:
| prefix=list(tau=value_type DOUBLECOLON {tau}) finish=stack_typing_end
  { finish prefix }

  stack_typing_end:
  | zeta=stack_typing_variable
    { (fun prefix -> SAbstract (prefix, zeta)) }
  | bigdot
    { (fun prefix -> SConcrete prefix) }


type_env: li=bracketed(simple_type_env) { li }
simple_type_env: li=separated_list(COMMA, type_env_elem) { li }

  type_env_elem:
  | alpha=type_variable { DAlpha alpha }
  | zeta=stack_typing_variable { DZeta zeta }
  | epsilon=return_marker_variable { DEpsilon epsilon }

/*
memory:
| LPAREN h=heap_fragment SEMICOLON r=register_file SEMICOLON s=stack RPAREN
  { (h, r, s) }

register_file: li=bracketed(simple_register_file) { li }
simple_register_file: li=separated_list(COMMA, binding(register, word_value)) { li }
*/

  binding(variable, value):
  | x=variable ARROW v=value { (x, v) }

  decl(variable,spec):
  | x=variable COLON s=spec { (x, s) }

/*
stack: ws=list(w=word_value DOUBLECOLON {w}) NIL { ws }
*/

type_variable:
| alpha=A_IDENTIFIER { alpha }

return_marker_variable:
| epsilon=E_IDENTIFIER { epsilon }

stack_typing_variable:
| zeta=Z_IDENTIFIER { zeta }

location:
| l=identifier { l }

identifier:
| id=A_IDENTIFIER { id }
| id=E_IDENTIFIER { id }
| id=Z_IDENTIFIER { id }
| id=OTHER_IDENTIFIER { id }

bigdot: TIMES { () }

nat:
| n=INTEGER { n }

bracereg: LBRACE r=register RBRACE { r }
bracketpos: LBRACKET i=nat RBRACKET { i }

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
