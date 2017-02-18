%token JMP CALL RET HALT
%token BNZ LD ST RALLOC BALLOC MV SALLOC SFREE SLD SST PACK AS UNPACK FOLD UNFOLD
%token CODE END NIL
%token ADD MUL SUB
%token FORALL EXISTS MU
%token UNIT INT REF BOX
%token LANGLE RANGLE LBRACKET RBRACKET LBRACE RBRACE LPAREN RPAREN
%token DOT BIGDOT COMMA COLON SEMICOLON DOUBLECOLON ARROW EMPTY
%token<string> IDENTIFIER
%token<string> TYPE_VARIABLE RETURN_MARKER_VARIABLE STACK_TYPING_VARIABLE
%token<int> INTEGER
%token<string> REGISTER
%token EOF

%start<Ftal.TAL.component> component_eof
%start<Ftal.TAL.mem> memory_eof
%start<Ftal.TAL.instr list> instruction_sequence_eof
%start<Ftal.TAL.w> word_value_eof
%start<Ftal.TAL.u> small_value_eof
%start<Ftal.TAL.delta> type_env_eof

%{ open Ftal.TAL

%}


%%

component_eof: c=component EOF { c }
memory_eof: m=memory EOF { m }
instruction_sequence_eof: i=instruction_sequence EOF { i }
word_value_eof: w=word_value EOF { w }
small_value_eof: u=small_value EOF { u }
type_env_eof: delta=type_env EOF { delta }

value_type:
| alpha=type_variable { TVar alpha }
| UNIT { TUnit }
| INT { TInt }
| ex=existential_type { let (alpha, tau) = ex in TExists (alpha, tau) }
| mu=mu_type { let (alpha, tau) = mu in TRec (alpha, tau) }
| REF taus=tuple(value_type) { TTupleRef taus }
| BOX psi=heap_value_type { TBox psi }

  existential_type:
  | EXISTS alpha=type_variable DOT tau=value_type { (alpha, tau) }
  mu_type:
  | MU alpha=type_variable DOT tau=value_type { (alpha, tau) }

simple_word_value:
| LPAREN RPAREN { WUnit }
| n=int { WInt n }
| l=location { WLoc l }
| p=pack(word_value)
  { let (tau, w, alpha, tau') = p in WPack (tau, w, alpha, tau') }

word_value:
| w=simple_word_value { w }
| f=fold(word_value)
  { let (alpha,tau,w) = f in WFold (alpha, tau, w) }
| a=app(simple_word_value)
  { let (w, omega) = a in WApp (w, omega) }

  fold(value):
  | FOLD mu=mu_type v=value
    { let (alpha, tau) = mu in (alpha, tau, v) }

  pack(value):
  | PACK LANGLE tau=value_type COMMA v=value RANGLE AS goal=existential_type
    { let (alpha,tau') = goal in (tau, v, alpha, tau') }

  app(value):
  | v=value LBRACKET omegas=separated_list(COMMA,type_instantiation) RBRACKET
    { (v, omegas) }

register:
| r=REGISTER { r }

simple_small_value:
| r=register { UR r }
| p=pack(small_value)
  { let (tau, u, alpha, tau') = p in UPack (tau, u, alpha, tau') }

small_value:
| w=word_value { UW w }
| f=fold(small_value)
  { let (alpha, tau, u) = f in UFold (alpha, tau, u) }
| a=app(simple_small_value)
  { let (u, omega) = a in UApp (u, omega) }

type_instantiation:
| tau=value_type { OT tau }
| sigma=stack_typing { OS sigma }
| q=return_marker { OQ q }

heap_value_type:
| FORALL LBRACKET delta=type_env RBRACKET DOT
  LBRACE chi=register_typing SEMICOLON sigma=stack_typing RBRACE q=return_marker
  { PBlock (delta, chi, sigma, q) }
| taus=tuple(value_type) { PTuple taus }

heap_value:
| CODE
  LBRACKET delta=type_env RBRACKET
  LBRACE chi=register_typing SEMICOLON sigma=stack_typing RBRACE q=return_marker
  DOT i=instruction_sequence
  { HCode (delta, chi, sigma, q, i) }
| ws=tuple(word_value) { HTuple ws }

register_typing: elems=left_empty_list(register_typing_elem) { elems }

  register_typing_elem: r=register COLON tau=value_type { (r, tau) }

stack_typing:
| prefix=list(tau=value_type DOUBLECOLON {tau}) finish=stack_typing_end
  { finish prefix }

  stack_typing_end:
  | zeta=stack_typing_variable
    { (fun prefix -> SAbstract (prefix, zeta)) }
  | BIGDOT
    { (fun prefix -> SConcrete prefix) }

return_marker:
| r=register { QR r }
| i=int { QI i }
| epsilon=return_marker_variable { QEpsilon epsilon }
| END LBRACE tau=value_type SEMICOLON sigma=stack_typing RBRACE
  { QEnd (tau, sigma) }
/* qout missing for now */

type_env: elems=left_empty_list(type_env_elem) { elems }

  type_env_elem:
  | alpha=type_variable { DAlpha alpha }
  | zeta=stack_typing_variable { DZeta zeta }
  | epsilon=return_marker_variable { DEpsilon epsilon }

memory:
| LPAREN h=heap_fragment SEMICOLON r=register_file SEMICOLON s=stack RPAREN
  { (h, r, s) }

heap_fragment:
| h=left_empty_list(binding(location,heap_value))
  { h }

register_file:
| h=left_empty_list(binding(register, word_value))
  { h }

  binding(variable, value):
  | x=variable ARROW v=value { (x, v) }

stack: ws=list(w=word_value DOUBLECOLON {w}) NIL { ws }

instruction_sequence:
| i=single_instruction SEMICOLON seq=instruction_sequence
  { i :: seq }
| JMP u=small_value
  { [Ijmp u] }
| CALL u=small_value LBRACE sigma=stack_typing COMMA q=return_marker RBRACE
  { [Icall (u, sigma, q)] }
| RET r=register rr=bracereg
  { [Iret (r, rr)] }
| HALT tau=value_type COMMA sigma=stack_typing rr=bracereg
  { [Ihalt (tau, sigma, rr)] }

single_instruction:
| op=aop rd=register COMMA rs=register COMMA u=small_value
  { Iaop (op, rd, rs, u) }
| BNZ r=register COMMA u=small_value
  { Ibnz (r, u) }
| LD rd=register COMMA rs=register i=bracketpos
  { Ild (rd, rs, i) }
| ST rd=register i=bracketpos COMMA rs=register
  { Ist (rd, i, rs) }
| RALLOC rd=register COMMA n=int
  { Iralloc (rd, n) }
| BALLOC rd=register COMMA n=int
  { Iballoc (rd, n) }
| MV rd=register COMMA u=small_value
  { Imv (rd, u) }
| SALLOC n=int
  { Isalloc n }
| SFREE n=int
  { Isfree n }
| SLD rd=register COMMA i=int
  { Isld (rd, i) }
| SST i=int COMMA rs=register
  { Isst (i, rs) }
| UNPACK LANGLE alpha=type_variable COMMA rd=register RANGLE u=small_value
  { Iunpack (alpha, rd, u) }
| UNFOLD rd=register COMMA u=small_value
  { Iunfold (rd, u) }

  aop:
  | ADD { Add }
  | SUB { Sub }
  | MUL { Mult }

component:
| LPAREN i=instruction_sequence SEMICOLON h=heap_fragment RPAREN
  { (i, h, []) (* TODO(dbp 2017-02-16): Parse heap typing! *)}


  type_variable:
  | alpha=TYPE_VARIABLE { alpha }

  return_marker_variable:
  | epsilon=RETURN_MARKER_VARIABLE { epsilon }

  stack_typing_variable:
  | zeta=STACK_TYPING_VARIABLE { zeta }

  location:
  | l=IDENTIFIER { l }

  int: n=INTEGER { n }
  bracereg: LBRACE r=register RBRACE { r }
  bracketpos: LBRACKET i=int RBRACKET { i }

  tuple(elem):
  | LANGLE elems=separated_list(COMMA, elem) RANGLE { elems }

  left_empty_list(elem):
  | EMPTY { [] }
  | EMPTY COMMA elems=separated_list(COMMA, elem) { elems }
