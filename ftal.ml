open Utils

type l = { line : int; col : int }
         [@@deriving show]
let cpos {Lexing.pos_fname; pos_lnum; pos_cnum; pos_bol} =
  let line = pos_lnum in
  let col = pos_cnum - pos_bol in
  {line = line; col = col}

let dummy_loc = { line = -1; col = -1 }

module FTAL = struct
  exception TypeError of string * int * int (* TODO: put in the right place *)
 end

module Lang = struct
  open PPrint
  (* Symbols *)
  let gensym =
    let count = ref 0 in
    fun ?(pref="g") () -> let v = !count in count := v + 1; String.concat "!" [pref; string_of_int v]

  (* Primitive Language Elements *)
  type tyname = string
  type codeloc = CodeLoc of int * int
  type tyvar = string
  type expvar = string

  (* Language Syntax *)
  type convlbl = PosConvLbl of tyname
               | NegConvLbl of tyname
  type complbl = PosCompLbl of codeloc | NegCompLbl of codeloc


  type ty = IntTy | BoolTy
          | FunTy of ty * ty 
          | ForallTy of tyvar * ty
          | PairTy of ty * ty
          | VarTy of tyvar
          | NameTy of tyname
          | AnyTy

  let isBaseTy typ = match typ with
    | IntTy -> true
    | BoolTy -> true
    | _ -> false

  let isGroundTy typ = match typ with
    | IntTy -> true
    | BoolTy -> true
    | FunTy (AnyTy, AnyTy) -> true
    | NameTy _ -> true
    | _ -> false 

  type op = Plus | Minus | Times | Equal

  type exp = IntExp of int 
            | BoolExp of bool 
            | IfExp of exp * exp * exp
            | OpExp of op * exp * exp
            | VarExp of expvar
            | LamExp of expvar * ty * exp
            | AppExp of exp * exp
            | AbstrExp of tyvar * exp (* exp should be value *)
            | InstExp of exp * ty
            | PairExp of exp * exp
            | Proj1Exp of exp
            | Proj2Exp of exp
            | ConvExp of exp * ty * convlbl * ty
            | CastExp of exp * ty * complbl * ty
            | BlameExp of complbl * ty

  let rec isValue expr = match expr with
    | IntExp _ -> true
    | BoolExp _ -> true
    | LamExp _ -> true
    | AbstrExp (_, e) -> isValue e (* Is a value iff syntactically wf *)
    | PairExp _ -> true
    | ConvExp (e, FunTy _, _, FunTy _) -> isValue e
    | ConvExp (e, ForallTy _, _, ForallTy _) -> isValue e
    | ConvExp (e, _, NegConvLbl a,  NameTy b) -> a = b && isValue e
    | CastExp (e, FunTy _, _, FunTy _) -> isValue e
    | CastExp (e, _, _, ForallTy _) -> isValue e
    | CastExp (e, t, _, AnyTy) -> isGroundTy t && isValue e
    | _ -> false

  let isBlame expr = match expr with BlameExp _ -> true | _ -> false 

  type namestore = (tyname * ty) list
  type tyenv = tyvar list
  type env = (expvar * ty) list
  
  type evalctx = CtxHole
              | IfCtx of evalctx * exp * exp
              | OpCtx1 of op * evalctx * exp
              | OpCtx2 of op * exp * evalctx
              | LamCtx of expvar * ty * evalctx
              | AppCtx1 of evalctx * exp
              | AppCtx2 of exp * evalctx
              | AbstrCtx of tyvar * evalctx (* evalctx should be value context *)
              | InstCtx of evalctx * ty
              | PairCtx1 of evalctx * exp
              | PairCtx2 of exp * evalctx
              | Proj1Ctx of evalctx
              | Proj2Ctx of evalctx
              | ConvCtx of evalctx * ty * convlbl * ty
              | CastCtx of evalctx * ty * complbl * ty
  
  (* Printer *)
  let r d =
    let b = Buffer.create 100 in
    PPrint.ToBuffer.pretty 0.8 80 b d;
    Buffer.contents b

  let rec p_ty (t : ty) : document =
    match t with
    | VarTy s -> !^s
    | IntTy -> !^"int"
    | BoolTy -> !^"bool"
    | NameTy n -> !^n
    | PairTy (t1,t2) -> nest 2 (angles (p_ty t1 ^^ !^"," ^^ p_ty t2))
    | FunTy (t1,t2) -> nest 2 (parens (p_ty t1 ^^ !^" -> " ^^ p_ty t2))
    | ForallTy(x, t) -> !^"forall " ^^ !^x ^^ !^"." ^/^ p_ty t
    | AnyTy -> !^"*"

  let p_lbl = function
    | PosConvLbl a -> !^"+" ^^ !^a
    | NegConvLbl a -> !^"-" ^^ !^a

  let rec p_simple_exp (e : exp) : document = match e with
    | VarExp e -> !^e
    | IntExp n -> !^(string_of_int n)
    | BoolExp true -> !^"true"
    | BoolExp false -> !^"false"
    | PairExp (e1,e2) -> langle ^^ (p_exp e1) ^^ comma ^/^ (p_exp e2) ^^ rangle
    | Proj1Exp e -> !^"pi1" ^^ space ^^ p_simple_exp e
    | Proj2Exp e -> !^"pi2" ^^ space ^^ p_simple_exp e
    | BlameExp (_, t) -> !^"blame" ^/^ colon ^^ space ^^ p_ty t
    | e -> group (lparen ^^ p_exp e ^^ rparen)

  and p_app_exp = function
    | AppExp (e1, e2) -> p_simple_exp e1 ^/^ p_simple_exp e2
    | InstExp (e, t) -> p_app_exp e ^/^ brackets (p_ty t)
    | e -> p_simple_exp e

  and p_mul_exp = function
    | OpExp ((Times as op), e1, e2) -> p_simple_exp e1 ^^ p_binop op ^^ p_simple_exp e2
    | e -> p_app_exp e

  and p_sum_exp = function
    | OpExp ((Plus as op), e1, e2) -> p_sum_exp e1 ^^ p_binop op ^^ p_sum_exp e2
    | OpExp ((Minus as op), e1, e2) -> p_sum_exp e1 ^^ p_binop op ^^ p_mul_exp e2
    | OpExp ((Equal as op), e1, e2) -> p_sum_exp e1 ^^ p_binop op ^^ p_mul_exp e2
    | e -> p_mul_exp e

  and p_arith_exp e = p_sum_exp e

  and p_cast_exp = function
    | ConvExp (e, t1, lbl, t2) -> p_cast_exp e ^/^ colon ^^ space
      ^^ p_ty t1 ^/^ p_lbl lbl ^^ !^"=>" ^^ space ^^ p_ty t2
    | CastExp (e, t1, lbl, t2) -> p_cast_exp e ^/^ colon ^^ space
      ^^ p_ty t1 ^/^ !^"=>" ^^ space ^^ p_ty t2 (* TODO: lbl *)
      | e -> p_arith_exp e

  and p_exp (e : exp) : document =
    group @@ nest 2 (match e with
    | IfExp(et,e1,e2) ->
      !^"if" ^^ space ^^ p_simple_exp et
      ^/^ !^"then" ^^space^^ p_simple_exp e1
      ^/^ !^"else" ^^space^^ p_simple_exp e2
    | LamExp(x, t, e) ->
      !^"lam " ^^ parens (!^x ^^ colon ^^ p_ty t) ^^ !^"." ^/^ p_exp e
    | AbstrExp(x, e) ->
    !^"Lam " ^^ !^x ^^ !^"." ^/^ p_exp e
    | e -> p_cast_exp e
  )

  and p_binop (b : op) : document =
    match b with
    | Plus -> !^"+"
    | Equal -> !^"="
    | Minus -> !^"-"
    | Times -> !^"*"


  let rec p_cast_ctx (c : evalctx) : document = match c with
    | ConvCtx (c, t1, lbl, t2) -> p_cast_ctx c ^/^ colon ^^ space
      ^^ p_ty t1 ^/^ p_lbl lbl ^^ !^"=>" ^^ space ^^ p_ty t2
    | CastCtx (c, t1, lbl, t2) -> p_cast_ctx c ^/^ colon ^^ space
      ^^ p_ty t1 ^/^ !^"=>" ^^ space ^^ p_ty t2 (* TODO: lbl *)
    | e -> p_ctx e (* TODO: p_arith_ctx *)
  
  and p_ctx (c : evalctx) : document = (* TODO: split like exp printer *)
    nest 2 (match c with
    | CtxHole -> !^"[.]"
    | OpCtx1 (o,c,e) -> p_ctx c ^^ space ^^ p_binop o ^^ space ^^ p_exp e
    | OpCtx2 (o,e,c) -> p_exp e ^^ space ^^ p_binop o ^^ space ^^ p_ctx c
    | IfCtx (c,e1,e2) ->
      !^"if " ^^ p_ctx c ^^ space
      ^^ lparen ^^ p_exp e1 ^^ rparen ^^ space
      ^^ lparen ^^ p_exp e2 ^^ rparen
    | AppCtx1 (c, e2) -> lparen ^^ p_ctx c ^^ space ^^ p_exp e2 ^^ rparen
    | AppCtx2 (e1, c) -> lparen ^^ p_exp e1 ^^ space ^^ p_ctx c ^^ rparen
    | PairCtx1 (c,e2) -> langle ^^ p_ctx c ^^ comma ^/^ p_exp e2 ^^ rangle
    | PairCtx2 (e1,c) -> langle ^^ p_exp e1 ^^ comma ^/^ p_ctx c ^^ rangle
    | Proj1Ctx c -> !^"pi1" ^^ p_ctx c (* TODO: make simple_Exp *)
    | Proj2Ctx c -> !^"pi2" ^^ p_ctx c (* TODO: make simple_Exp *)
    | LamCtx(x, t, c) ->
      !^"lam " ^^ parens (!^x ^^ colon ^^ p_ty t) ^^ !^"." ^/^ p_ctx c
    | AbstrCtx(x, cv) ->
      !^"Lam " ^^ !^x ^^ !^"." ^/^ p_ctx cv
    | _ -> parens (p_cast_ctx c)
    (* | CPi (_,n, c) -> !^"pi." ^^ !^(string_of_int n) ^^ lparen ^^ p_ctx c ^^ rparen *)
    )

  let rec p_store = function
    | [] -> !^"" (* TODO: should this stay empty?*)
    | (a,t)::[] -> !^a ^^ !^":=" ^^ p_ty t
    | (a,t)::tl -> group (!^a ^^ !^":=" ^^ p_ty t ^^ !^"," ^^ break 1) ^^ p_store tl

  let show_exp e = (r (p_exp e))
  let show_ctx c = (r (p_ctx c))
  let show_store s = (r (p_store s))
  (* End Printer *)
  
  
  let lblName lbl = match lbl with
    | PosConvLbl a -> a
    | NegConvLbl a -> a

  let nameInLbl a lbl = a = lblName lbl
  
  let nameInStore a s = List.exists (function (b, _) -> b = a) s

  let negateConvLbl lbl = match lbl with
    | PosConvLbl b -> NegConvLbl b
    | NegConvLbl b -> PosConvLbl b
    
  let negateCompLbl lbl = match lbl with
    | PosCompLbl b -> NegCompLbl b
    | NegCompLbl b -> PosCompLbl b

  let rec envLookup env x = match env with
    | [] -> None
    | (y,a)::tl -> if x = y then Some a else envLookup tl x

  let rec plug ctx e = match ctx with
    | CtxHole -> e
    | IfCtx (ctx', e1, e2) -> IfExp (plug ctx' e, e1, e2)
    | OpCtx1 (op, ctx', e2) -> OpExp (op, plug ctx' e, e2)
    | OpCtx2 (op, e1, ctx') -> OpExp (op, e1, plug ctx' e)
    | LamCtx (x, t, ctx') -> LamExp (x, t, plug ctx' e)
    | AppCtx1 (ctx', e2) -> AppExp (plug ctx' e, e2)
    | AppCtx2 (e1, ctx') -> AppExp (e1, plug ctx' e)
    | AbstrCtx (x, vctx) -> AbstrExp (x, plug vctx e)
    | InstCtx (ctx', a) -> InstExp (plug ctx' e, a)
    | PairCtx1 (ctx', e2) -> PairExp (plug ctx' e, e2)
    | PairCtx2 (e1, ctx') -> PairExp (e1, plug ctx' e)
    | Proj1Ctx ctx' -> Proj1Exp (plug ctx' e)
    | Proj2Ctx ctx' -> Proj2Exp (plug ctx' e)
    | ConvCtx (ctx', t1, lbl, t2) -> ConvExp (plug ctx' e, t1, lbl, t2)
    | CastCtx (ctx', t1, lbl, t2) -> CastExp (plug ctx' e, t1, lbl, t2)

  (* Substitutions *)
  type subst = RenameTyVar of tyvar * tyvar
            | RenameExpVar of expvar * expvar
            | SubstTyVar of ty * tyvar * bool
            | SubstExpVar of exp * expvar * bool


  let getRenameTyVar sub = match sub with
    | RenameTyVar (_, x) -> Some x
    | _ -> None

  let getRenameExpVar sub = match sub with
    | RenameExpVar (_, x) -> Some x
    | _ -> None
  
  let closedSubst sub = match sub with
    | RenameTyVar _ -> false
    | RenameExpVar _ -> false
    | SubstTyVar (_, _, b) -> b
    | SubstExpVar (_, _, b) -> b

  (* perform a substitution on a type *)
  let rec substTy typ sub = match typ with
    | IntTy -> IntTy
    | BoolTy -> BoolTy
    | FunTy (b, c) -> FunTy (substTy b sub, substTy c sub)
    | ForallTy (x, b) -> 
      (* Avoid renaming when possible for ease-of-use/efficiency. 
        Cases where we avoid renaming: 
        - If the substition is closed
        - If the substitution is a renaming *)
      if closedSubst sub then ForallTy (x, substTy b sub) else
      (match getRenameTyVar sub with
        | Some y when y = x -> ForallTy (x, b) 
        | Some y -> ForallTy (x, substTy b sub)
        | None -> let y = gensym ~pref:"X" () in
                ForallTy (y, substTy (substTy b (RenameTyVar (y, x))) sub))
    | PairTy (b, c) -> PairTy (substTy b sub, substTy c sub)
    | VarTy y -> (match sub with
      | RenameTyVar (z, x) when x = y -> VarTy z
      | SubstTyVar (a, x, _) when x = y -> a
      | _ -> VarTy y)
    | NameTy n -> NameTy n
    | AnyTy -> AnyTy
  

  let rec substExp e sub = match e with
    | IntExp _ -> e
    | BoolExp _ -> e
    | IfExp (c, e1, e2) -> IfExp (substExp c sub,
                                substExp e1 sub,
                                substExp e2 sub)
    | OpExp (op, e1, e2) -> OpExp (op, substExp e1 sub, substExp e2 sub)
    | VarExp y -> (match sub with
      | RenameExpVar (z, x) when x = y -> VarExp z
      | SubstExpVar (e', x, _) when x = y -> e'
      | _ -> VarExp y)
    | LamExp (y, a, b) -> 
      (* Avoid renaming when possible for ease-of-use/efficiency. 
        Cases where we avoid renaming: 
        - If the substition is closed
        - If the substitution is a renaming *)
      (*
      This is broken because it doesn't consider when y is in the domain 
      of the substitution. -Jeremy

      if closedSubst sub then LamExp (y, substTy a sub, substExp b sub) else
      *)
      (match getRenameExpVar sub with
        | Some x  when y = x -> LamExp (y, a, b) 
        | Some x -> LamExp (y, substTy a sub, substExp b sub)
        | None -> let x = gensym ~pref:"x" () in
          LamExp (x, substTy a sub, substExp (substExp b (RenameExpVar (x, y))) sub))
    | AppExp (e1, e2) -> AppExp (substExp e1 sub, substExp e2 sub)
    | AbstrExp (x, v) -> 
      (* Avoid renaming when possible for ease-of-use/efficiency. 
        Cases where we avoid renaming: 
        - If the substition is closed
        - If the substitution is a renaming *)
      if closedSubst sub then AbstrExp (x, substExp v sub) else
      (match getRenameTyVar sub with
        | Some y when y = x -> AbstrExp (x, v) 
        | Some y -> AbstrExp (x, substExp v sub)
        | None -> let y = gensym ~pref:"X" () in
                AbstrExp (y, substExp (substExp v (RenameTyVar (y, x))) sub))
    | InstExp (e1, a) -> InstExp (substExp e1 sub, substTy a sub)
    | PairExp (e1, e2) -> PairExp (substExp e1 sub, substExp e2 sub)
    | Proj1Exp e1 -> Proj1Exp (substExp e1 sub)
    | Proj2Exp e1 -> Proj2Exp (substExp e1 sub)
    | ConvExp (e1, t1, lbl, t2) -> ConvExp (substExp e1 sub, substTy t1 sub, lbl, substTy t2 sub)
    | CastExp (e1, t1, lbl, t2) -> CastExp (substExp e1 sub, substTy t1 sub, lbl, substTy t2 sub)
    | BlameExp _ -> e

  let rec ty_eq t1 t2 = match (t1, t2) with
    | (IntTy, IntTy) -> true
    | (BoolTy, BoolTy) -> true
    | (FunTy (a1, b1), FunTy (a2, b2)) -> ty_eq a1 a2 && ty_eq b1 b2
    | (ForallTy (x, t1'), ForallTy (y, t2')) -> ty_eq t1' (substTy t2' (RenameTyVar (x, y)))
    | (PairTy (a1, b1), PairTy (a2, b2)) -> ty_eq a1 a2 && ty_eq b1 b2
    | (VarTy x1, VarTy x2) -> x1 = x2
    | (NameTy n1, NameTy n2) -> n1 = n2
    | (AnyTy, AnyTy) -> true
    | _ -> false

  let rec bindingInStore (n, a) s = match s with
    | [] -> false
    | ((n',a')::tl) -> (n = n' && ty_eq a a') || bindingInStore (n, a) s

  let rec storeWf s = match s with
    | [] -> true
    | (a,t)::tl -> (not (nameInStore a tl)) && typeWf tl [] t
  and typeWf s te typ = match typ with
    | VarTy x -> storeWf s && List.mem te x
    | NameTy n -> storeWf s && nameInStore n s
    | IntTy -> storeWf s
    | BoolTy -> storeWf s
    | AnyTy -> storeWf s
    | FunTy (a, b) -> typeWf s te a && typeWf s te b
    | ForallTy (x, a) -> typeWf s (x::te) a
    | PairTy (a, b) -> typeWf s te a && typeWf s te b

  let rec convertible s te t1 lbl t2 = match (t1, lbl, t2) with
    | (IntTy, _, IntTy) -> storeWf s && nameInStore (lblName lbl) s
    | (BoolTy, _, BoolTy) -> storeWf s && nameInStore (lblName lbl) s
    | (FunTy (a1, b1), _, FunTy (a2, b2)) -> 
      convertible s te a2 (negateConvLbl lbl) a1 &&
      convertible s te b1 lbl b2
    | (ForallTy (x1, a1), _, ForallTy (x2, a2)) ->
      convertible s (x1::te) a1 lbl (substTy a2 (RenameTyVar (x1, x2)))
    | (PairTy (a1, b1), _, PairTy (a2, b2)) -> 
      convertible s te a1 lbl a2 && convertible s te b1 lbl b2
    | (NameTy n, _, NameTy m) when n = m -> 
      storeWf s && 
      (not (n = (lblName lbl))) && 
      nameInStore n s
    | (NameTy n, PosConvLbl n', a) -> (storeWf s && bindingInStore (n,a) s)
    | (a, NegConvLbl n', NameTy n) -> (storeWf s && bindingInStore (n,a) s)
    | (VarTy x, _, VarTy y) -> x = y && storeWf s && List.mem te x
    | (AnyTy, _, AnyTy) -> storeWf s && nameInStore (lblName lbl) s
    | _ -> false
   
  let rec compatible s te t1 t2 = match (t1, t2) with
    | (IntTy, IntTy) -> storeWf s
    | (BoolTy, BoolTy) -> storeWf s
    | (FunTy (a1, b1), FunTy (a2, b2)) -> 
      compatible s te a2 a1 && compatible s te b1 b2
      (* NOTE: order of the next 2 cases is important! *)
    | (ForallTy (x, a1), a2) -> compatible s te (substTy a1 (SubstTyVar (AnyTy, x, true))) a2
    | (a1, ForallTy (x, a2)) -> compatible s (x::te) a1 a2
    | (PairTy (a1, b1), PairTy (a2, b2)) -> 
      compatible s te a1 a2 && compatible s te b1 b2
    | (NameTy n, NameTy m) -> n = m && storeWf s && nameInStore n s
    | (VarTy x, VarTy y) -> x = y && storeWf s && List.mem te x
    | (AnyTy, a) -> typeWf s te a
    | (a, AnyTy) -> typeWf s te a
    | _ -> false

  let rec envWf s te env = match env with
    | [] -> storeWf s
    | (x,a)::tl -> typeWf s te a && envWf s te tl

  let rec expType s te env e = match e with
    | BoolExp _ -> if envWf s te env then Ok BoolTy 
      else Error (!^"Environment for expression" ^/^ p_exp e ^/^ !^"was malformed") (* TODO: get err from env*)
    | IfExp (c, e1, e2) -> 
      (match expWf s te env c BoolTy with 
        | Ok () ->
          let to1 = expType s te env e1 in
          let to2 = expType s te env e2 in
          (match (to1,to2) with
          | (Ok t1, Ok t2) -> if ty_eq t1 t2 then Ok t1 
            else Error (!^"The two branches of the 'if' statement have types" ^/^
              p_ty t1 ^^space^^ !^"and" ^/^
              p_ty t2 ^^ !^", but should have the same type.")
          | (Error s, _) -> Error s
          | (_, Error s) -> Error s)
        | Error s -> Error s)
    | IntExp _ -> if envWf s te env then Ok IntTy 
      else Error (!^"Environment for expression" ^/^ p_exp e ^/^ !^"was malformed") (* TODO: get err from env*)
    | OpExp (opr, e, e') -> 
      (match (opr, expWf s te env e IntTy, expWf s te env e' IntTy) with
        | (Equal, Ok (), Ok ()) -> Ok BoolTy
        | (_, Ok (), Ok ()) -> Ok IntTy
        | (_, Error s, _) -> Error s
        | (_, _, Error s) -> Error s)
    | VarExp x -> (match envLookup env x with
      | Some a -> if envWf s te env then Ok a 
        else Error (!^"Environment for expression" ^/^ p_exp e ^/^ !^"was malformed") (* TODO: get err from env*)
      | None -> Error (!^"Variable" ^^ space ^^ !^x ^/^ !^"not found in environment."))
    | LamExp (x, a, e) -> (match expType s te ((x,a)::env) e with
      | Ok b -> Ok (FunTy (a,b))
      | Error s -> Error s)
    | AppExp (e1, e2) -> 
      let to1 = expType s te env e1 in
      let to2 = expType s te env e2 in
      (match (to1 , to2) with
      | (Ok (FunTy (t1, t2)), Ok t1') -> if ty_eq t1 t1' then Ok t2
        else Error (!^"Function" ^^ space ^^ p_exp e1 ^/^ !^"has type" ^^ space ^^ p_ty (FunTy (t1, t2)) 
          ^/^ !^"but its argument" ^^ space ^^ p_exp e2 ^/^ !^"has type" ^^ space ^^ p_ty t1' ^^ !^".")
      | (Ok t1, Ok t2) -> Error (!^"Expression" ^^ space ^^ p_exp e1 ^/^ 
        !^"should be a function, but has type" ^^space^^ p_ty t1 ^^ !^".")
      | (Error s, _) -> Error s
      | (_, Error s) -> Error s)
    | AbstrExp (x, v) -> (match expType s (x::te) env v with
      | Ok t -> if isValue v then Ok (ForallTy (x,t)) 
        else Error (!^"Expression" ^^ space ^^ p_exp v ^/^ !^"must be a value.")
      | Error s -> Error s)
    | InstExp (e', b) -> (match expType s te env e' with
      | Ok (ForallTy (x, a)) -> if typeWf s te b 
          then Ok (substTy a (SubstTyVar (b, x, List.length te = 0)))
          else Error (!^"Type" ^^space^^ p_ty b ^/^ !^"is not well-formed.")
      | Ok t -> Error (!^"Expression" ^^ space ^^ p_exp e' ^/^ !^"is not a type abstraction.")
      | Error s -> Error s)
    | PairExp (e1, e2) ->
      let to1 = expType s te env e1 in
      let to2 = expType s te env e2 in
      (match (to1,to2) with
        | (Ok t1, Ok t2) -> Ok (PairTy (t1, t2))
        | (Error s, _) -> Error s
        |  (_, Error s) -> Error s)
    | Proj1Exp e' -> (match expType s te env e' with
      | Ok (PairTy (a, b)) -> Ok a 
      | Error s -> Error s)
    | Proj2Exp e' -> (match expType s te env e' with
      | Ok (PairTy (a, b)) -> Ok b
      | Error s -> Error s)
    | ConvExp (e', t1, lbl, t2) -> 
      (match expWf s te env e' t1 with
        | Ok t ->  if convertible s te t1 lbl t2 then Ok t2 
          else Error (!^"Type" ^^space^^ p_ty t1 ^/^ group (!^"is not convertible to" ^^space^^ p_ty t2
            ^/^ !^"by label" ^^space^^ p_lbl lbl))
        | Error s -> Error s)
    | CastExp (e', t1, lbl, t2) -> 
      (match expWf s te env e' t1 with
        | Ok t ->  if compatible s te t1 t2 then Ok t2 
          else Error (!^"Type" ^^space^^ p_ty t1 ^/^ !^"is not compatible with" ^^space^^ p_ty t2)
        | Error s -> Error s)
    | BlameExp (lbl,ty) -> if typeWf s te ty then Ok ty 
      else Error (!^"Type" ^^space ^^ p_ty ty ^/^ !^"assigned to blame is malformed.")
  and expWf s te env e typ = match expType s te env e with
    | Ok t -> if ty_eq t typ then Ok () else Error (!^"Expected type" ^^ space ^^ p_ty typ
      ^/^ group (!^"but" ^^ space ^^ p_exp e ^/^ !^"is of type" ^^space^^ p_ty t ^^ !^"."))
    | Error s -> Error s

  (* Assumption: expType [] [] [] p = Some t *)
  (* Invariant: if decompose p = (p', f)
      then decompose p' = (p', id) *)
  let rec decompose p = match p with
    | OpExp (op, e1, e2) -> (match (isValue e1, isValue e2) with
      | (false, _) -> let (e1', ctx) = decompose e1 in
        (e1', OpCtx1 (op, ctx, e2))
      | (true, false) -> let (e2', ctx) = decompose e2 in
        (e2', OpCtx2 (op, e1, ctx))
      | (true, true) -> (p, CtxHole))
    | IfExp (c, e1, e2) -> if isValue c
      then (p, CtxHole)
      else let (c', ctx) = decompose c in
        (c, IfCtx (ctx, e1, e2))
    | AppExp (e1, e2) -> (match (isValue e1, isValue e2) with
      | (false, _) ->
        let (e1', ctx) = decompose e1 in
        (e1', AppCtx1 (ctx, e2))
      | (true, false) -> 
        let (e2', ctx) = decompose e2 in
        (e2', AppCtx2 (e1, ctx))
      | (true, true) -> (p, CtxHole))
    | InstExp (e, a) -> if isValue e
      then (p, CtxHole)
      else let (e', ctx) = decompose e in
        (e', InstCtx (ctx, a))
    | PairExp (e1, e2) -> (match (isValue e1, isValue e2) with
      | (false, _) ->
        let (e1', ctx) = decompose e1 in
        (e1', PairCtx1 (ctx, e2))
      | (true, false) -> 
        let (e2', ctx) = decompose e2 in
        (e2', PairCtx2 (e1, ctx))
      | (true, true) -> (p, CtxHole))
    | Proj1Exp e -> if isValue e
      then (p, CtxHole)
      else let (e', ctx) = decompose e in
        (e', Proj1Ctx ctx)
    | Proj2Exp e -> if isValue e
      then (p, CtxHole)
      else let (e', ctx) = decompose e in
        (e', Proj2Ctx ctx)
    | ConvExp (e, t1, lbl, t2) -> if isValue e
      then (p, CtxHole)
      else let (e', ctx) = decompose e in
        (e', ConvCtx (ctx, t1, lbl, t2))
    | CastExp (e, t1, lbl, t2) -> if isValue e
      then (p, CtxHole)
      else let (e', ctx) = decompose e in
        (e', CastCtx (ctx, t1, lbl, t2))
    | _ -> (p, CtxHole) (* the program is a value or blame *)


  (* Assumptions: 
      - expType s [] [] p = Some t
      - decompose p = (p, fun x -> x)
  *)
  let stepRedex p = match p with
    | OpExp (Plus, IntExp i1, IntExp i2) -> Some (IntExp (i1 + i2))
    | OpExp (Minus, IntExp i1, IntExp i2) -> Some (IntExp (i1 - i2))
    | OpExp (Times, IntExp i1, IntExp i2) -> Some (IntExp (i1 * i2))
    | OpExp (Equal, IntExp i1, IntExp i2) -> Some (BoolExp (i1 = i2))
    | IfExp (BoolExp true, e1, e2) -> Some e1
    | IfExp (BoolExp false, e1, e2) -> Some e2
    | AppExp (LamExp (x,a,b), v) -> Some (substExp b (SubstExpVar (v, x, true)))
    | Proj1Exp (PairExp (v1, v2)) -> Some v1
    | Proj2Exp (PairExp (v1, v2)) -> Some v2
    | ConvExp (v, IntTy, lbl, IntTy) -> Some v
    | ConvExp (v, BoolTy, lbl, BoolTy) -> Some v
    | ConvExp (PairExp (v1,v2), PairTy (a, b), lbl, PairTy (a', b')) ->
      Some (PairExp (ConvExp (v1, a, lbl, a'), ConvExp (v2, b, lbl, b')))
    | AppExp (ConvExp (v, FunTy (a, b), lbl, FunTy (a', b')), v') ->
      Some (ConvExp (AppExp (v, ConvExp (v', a', negateConvLbl lbl, a)), 
                                              b, lbl, b'))
    | ConvExp (ConvExp (v, a, lbl, b), 
                      NameTy n, PosConvLbl m, a') -> if n = m 
      then Some v (* If the term is well-typed and n = m, 
        then the term is of the form ((v : A =-a=> a) : a =+a=> A)*)
      else Some (ConvExp (v, a, lbl, b)) (* if the term is well-typed,
         then a' = NameTy n*)
    | ConvExp (v, NameTy a, lbl, NameTy a') -> Some v (*Note: overlaps with above*)
    | ConvExp (v, AnyTy, lbl, AnyTy) -> Some v
    | CastExp (v, IntTy, lbl, IntTy) -> Some v
    | CastExp (v, BoolTy, lbl, BoolTy) -> Some v
    | CastExp (PairExp (v1,v2), PairTy (a, b), lbl, PairTy (a', b')) ->
      Some (PairExp (CastExp (v1, a, lbl, a'), CastExp (v2, b, lbl, b')))
    | AppExp (CastExp (v, FunTy (a, b), lbl, FunTy (a', b')), v') ->
      Some (CastExp (AppExp (v, CastExp (v', a', negateCompLbl lbl, a)), b, lbl, b'))
    | CastExp (v, ForallTy (x,a), lbl, b) -> (* Note: assumes b /= forall *)
      Some (CastExp (InstExp (v, AnyTy), substTy a (SubstTyVar (AnyTy, x, true)), lbl, b))
    | CastExp (v, NameTy a, lbl, NameTy b) -> Some v (*a = b if well-typed *)
    | CastExp (v, AnyTy, lbl, AnyTy) -> Some v
    | CastExp (CastExp (v, IntTy, lbl1, AnyTy), AnyTy, lbl2, IntTy)
    | CastExp (CastExp (v, BoolTy, lbl1, AnyTy), AnyTy, lbl2, BoolTy)
    | CastExp (CastExp (v, FunTy (AnyTy, AnyTy), lbl1, AnyTy), 
                          AnyTy, lbl2, FunTy (AnyTy, AnyTy)) -> Some v
    | CastExp (CastExp (v, NameTy a, lbl1, AnyTy), AnyTy, lbl2, NameTy a') ->
      if a = a' then Some v else Some (BlameExp (lbl2, NameTy a'))
    | CastExp (CastExp (v, _, lbl1, AnyTy), AnyTy, lbl2, b) -> Some (BlameExp (lbl2, b))
    | CastExp (v, FunTy (AnyTy, AnyTy), lbl, AnyTy) -> None
    | CastExp (v, FunTy (a, b), lbl, AnyTy) -> 
      Some (CastExp (CastExp (v, AnyTy, lbl, FunTy (AnyTy, AnyTy)),
                          FunTy (AnyTy, AnyTy), lbl, FunTy (a, b)))
    | CastExp (v, AnyTy, lbl, FunTy (AnyTy, AnyTy)) -> None
    | CastExp (v, AnyTy, lbl, FunTy (a, b)) -> 
      Some (CastExp (CastExp (v, FunTy (a, b), lbl, FunTy (AnyTy, AnyTy)),
                          FunTy (AnyTy, AnyTy), lbl, AnyTy))
    | _ -> None (* TODO: check this! *)
     
    (* Assumptions: 
        - expType s [] [] p = Some t
        - decompose p = (p, fun x -> x)
    *)
  let storeStepRedex (s,p) = match p with
    | BlameExp _ -> None
    | InstExp (AbstrExp (x,v), b) -> 
      let a = gensym ~pref:"a" () in
      (match expType s [x] [] v with
        | Ok (t) -> Some ((a,b)::s, 
            ConvExp (substExp v (SubstTyVar (NameTy a, x, true)),  
              substTy t (SubstTyVar (NameTy a, x, true)), PosConvLbl a, 
              substTy t (SubstTyVar (b, x, true))))
        | Error _ -> None (* TODO: report error! *))
    | InstExp (CastExp (v, t1, lbl, ForallTy (x, t2)), b) ->
      let a = gensym ~pref:"a" () in
      let t2ax = substTy t2 (SubstTyVar (NameTy a, x, true)) in
      let t2bx = substTy t2 (SubstTyVar (b, x, true)) in
      Some ((a,b)::s, ConvExp (CastExp (v, t1, lbl, t2ax),
                      t2ax, PosConvLbl a, t2bx))
    | InstExp (ConvExp (v, ForallTy (x, t1), lbl, ForallTy (x', t2)), b) ->
      let a = gensym ~pref:"a" () in
      let t1ax = substTy t1 (SubstTyVar (NameTy a, x, true)) in
      let t2ax = substTy t2 (SubstTyVar (NameTy a, x, true)) in
      let t2bx = substTy t2 (SubstTyVar (b, x, true)) in
      Some ((a,b)::s, ConvExp (ConvExp (InstExp (v, NameTy a),
                              t1ax, lbl, t2ax),
                      t2ax, PosConvLbl a, t2bx))
    | _ -> (match stepRedex p with
      | Some p' -> Some (s, p')
      | None -> None)
      
  let step (s,p) = 
    if isBlame p then None else (* Blame does not step *)
      let (p', evl) = decompose p in
      match p' with
        | BlameExp (lbl, _) -> let Ok(t) = expType s [] [] p in (* TODO: capture errors! *)
          Some (s, BlameExp (lbl, t)) (* However blame in a context does *)
        | _ -> (match storeStepRedex (s,p') with
          | Some (s',p'') -> Some (s', plug evl p'')
          | None -> None)
  
  let rec stepn n (s,p) = 
    if n <= 0 then (s,p) else (match step (s,p) with
      | Some res -> stepn (n - 1) res
      | None -> (s,p))
  
  let rec run (s, p) = 
    (* TODO: check for a value before, make None an error *)
    if isValue p then (s,p)
    else
      match step (s,p) with
	| Some (s',p') -> run (s', p')
	| None -> (s,p)

end
