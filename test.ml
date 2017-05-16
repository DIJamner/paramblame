open OUnit2;;
open Ftal;;
open Examples;;

let roundtrip ?source comp =
  let orig, roundtrip =
    Filename.temp_file ~temp_dir:"." "orig" ".ftal",
    Filename.temp_file ~temp_dir:"." "roundtrip" ".ftal" in
  let write_source () =
    match source with
      | None -> ()
      | Some str ->
        let chan = open_out orig in
        output_string chan str;
        flush chan;
        close_out chan;
  in
  let write_result () =
    let doc = Lang.p_exp comp in
    let chan = open_out roundtrip in
    PPrintEngine.ToChannel.pretty 0.8 80 chan doc;
    flush chan;
    close_out chan;
  in
  write_source ();
  write_result ();
  match Parse.parse_file Parse.expression_eof roundtrip with
  | exception exn ->
    Printf.eprintf "%!\nRountrip failure %S %S%!\n" orig roundtrip;
    comp
  | roundtripped_comp ->
    Sys.remove orig; Sys.remove roundtrip;
    roundtripped_comp

let empty = ([],[],[])

let assert_eint e n =
  match e with
  | Lang.IntExp x -> assert_equal x n
  | _ -> assert_failure "not equal"


  (* TODO: rename *)
let lang_assert_eint e n =
  match e with
  | Lang.IntExp x -> assert_equal x n
  | _ -> assert_failure "not equal"

let lang_assert_blame e =
  match e with
  | Lang.BlameExp (l, t) -> ()
  | _ -> assert_failure "error, expected blame"

let check_and_run p r =
   assert_equal (Lang.expType [] [] [] p) (Ok Lang.IntTy);
   lang_assert_eint (snd (Lang.run ([], p))) r

let check_and_blame p =
   assert_equal (Lang.expType [] [] [] p) (Ok Lang.IntTy);
   lang_assert_blame (snd (Lang.run ([], p)))

let test1 _ =
    check_and_run (expr "1 + 1") 2

let test_app _ =
    check_and_run (expr "(lam (x:int). x + x) 1") 2

let test_factorial _ =
  lang_assert_eint
    (snd (Lang.run ([], Lang.(AppExp (Examples.factorial, IntExp 3)))))
    6

let test_let _ =
  assert_eint
    (snd (Lang.run ([], expr "let x : int = 3 in 2 + x")))
    5

let test_equal_true _ =
  check_and_run (expr "if (2 = 2) then 0 else 1") 0

let test_equal_false _ =
  check_and_run (expr "if (1 = 2) then 0 else 1") 1

let test_paper1 _ =
  check_and_run (expr {|let p : <int,<int->int,int->bool>>  =  <0, <lam (x : int). 1 - x, lam (x : int). x = 0>> 
                        in (pi1 (pi2 p)) (pi1 p)|}) 1

let test_paper2 _ =
  check_and_run Examples.swap_int_bool 1

let test_paper3 _ =
  check_and_run Examples.swap_bool_int 1

let test_paper4a _ =
  check_and_run (expr {|
    let inc : * = (lam (x : *). (x : * => int) + 1 : int => *) : *->* => * in
    let once : * = (lam (f : *). (lam (x : *). (f : * => *->*) x) : *->* => *) : *->* => * in
    ((((once : * => *->*) inc) : * => *->*) (0 : int => *)) : * => int
    |}) 1

let test_paper4 _ =
  check_and_run (expr {|
    let inc : * = (lam (x : *). (x : * => int) + 1 : int => *) : *->* => * in
    let two : * = (lam (f : *). (lam (x : *). (f : * => *->*) ((f : * => *->*) x)) : *->* => *) : *->* => * in
    ((((two : * => *->*) inc) : * => *->*) (0 : int => *)) : * => int
    |}) 2

let test_paper5a _ =
  check_and_run (expr {|
    let inc : * = (lam (x : *). (x : * => int) + 1 : int => *) : *->* => * in
    let two : * = (Lam X.lam(f:X->X).lam(x:X). f (f x)) : forall X. (X->X)->X->X => * in
    ((((two : * => *->*) inc) : * => *->*) (0 : int => *)) : * => int
    |}) 2

let test_paper5b _ =
  check_and_blame (expr {|
    let inc : * = (lam (x : *). (x : * => int) + 1 : int => *) : *->* => * in
    let two : * = (Lam X.lam(f:X->X).lam(x:X). f (f x)) : forall X. (X->X)->X->X => * in
    ((((two : * => *->*) (0 : int => *)) : * => *->*) inc) : * => int
    |}) 

let test_paper5c _ =
  check_and_run (expr {|
    let inc : int->int = (lam (x : int). x + 1) in
    let twos : * = (lam (f : *). (lam (x : *). (f : * => *->*) ((f : * => *->*) x)) : *->* => *) : *->* => * in
    let two : forall X. (X->X)->X->X = (twos : * => forall X. (X->X)->X->X) in
    two [int] inc 0
    |}) 2

let test_paper5d _ =
  check_and_blame (expr {|
    let inc : int->int = (lam (x : int). x + 1) in
    let twos : * = (lam (f : *). (lam (x : *). 2 : int => *) : *->* => *) : *->* => * in
    let two : forall X. (X->X)->X->X = (twos : * => forall X. (X->X)->X->X) in
    two [int] inc 0
    |})

let test_paper6 _ =
  check_and_run (expr "2 : int => * : * => int") 2

let test_paper7 _ =
  check_and_blame (expr "2 : int => * : * => int->int : int->int => * : * => int")

let test_paper8 _ =
  check_and_run (expr "((lam(x:*). (x:*=>int)+1 : int=>*) : *->* => * : * => int->int) 2") 3

let test_paper9 _ =
  check_and_blame (expr "pi1 (((lam(x:*).x) : *->* => * : * => forall X. forall Y. <X,Y> -> <Y,X>) [int] [int] <1,2>)")

let test_paper10a _ =
  check_and_run (expr {|
    let Ks : * = (lam(x:*). (lam(y:*). x) : *->* => *) : *->* => * in
    let K : forall X. forall Y. X->Y->X = Ks : * => forall X. forall Y. X->Y->X in
    K [int] [bool] 42 false
    |}) 42

let test_paper10b _ =
  check_and_blame (expr {|
    let Ks : * = (lam(x:*). (lam(y:*). y) : *->* => *) : *->* => * in
    let K : forall X. forall Y. X->Y->X = Ks : * => forall X. forall Y. X->Y->X in
    K [int] [bool] 42 false
    |}) 

let test_subst1 _ =
  check_and_run (expr "(Lam X. lam (x:X). Lam X. lam (x:X). x) [bool] true [int] 0 ") 0

let test_subst2 _ =
  check_and_run (expr "(Lam X. lam (f:forall X. X -> X). f [int] 42) [bool] (Lam Y. lam(y:Y). y)") 42

let test_function_cast _ =
  check_and_run (expr {|
    let id : * -> * = lam (x: * ).x in
    (id : * -> * => * : * => int -> int) 4
  |}) 4

let assert_raises_typeerror (f : unit -> 'a) : unit =
  FTAL.(try (f (); assert_failure "didn't raise an exception")
        with TypeError _  -> ())


let test_factorial_ty _ =
  assert_equal
    (Lang.expType [] [] [] factorial)
    (Ok Lang.IntTy)


let test_examples _ =
  let assert_roundtrip expr =
    let reparsed = Parse.parse_string Parse.expression_eof (Ftal.Lang.show_exp expr) in
    let rereparsed = Parse.parse_string Parse.expression_eof (Ftal.Lang.show_exp reparsed) in
    assert_equal reparsed rereparsed in
  assert_roundtrip Examples.factorial;
  ()

let suite = "Polymorphic Blame Calculus evaluations" >:::
            [
              "1 + 1 = 2 : int" >:: test1;
              "(lam x. x + x) 1 = 2" >:: test_app;
              (* "parse (5)" >:: test_parse5; TODO: should be removed? *)
              (*"fact 3 = 6" >:: test_factorial;*)
	      "(fact 4) : int " >:: test_factorial_ty;
	      "let x : int = 3 in 2 + x" >:: test_let;
	      "2 = 2" >:: test_equal_true;
              "1 = 2" >:: test_equal_false;
              "paper #1" >:: test_paper1;
              "paper #2" >:: test_paper2;
              "paper #3" >:: test_paper3;
              "paper #4a" >:: test_paper4a;
              "paper #4" >:: test_paper4;
              "paper #5(a)" >:: test_paper5a;
              "paper #5(b)" >:: test_paper5b;
              "paper #5(c)" >:: test_paper5c;
              "paper #5(d)" >:: test_paper5d;
              "paper #6" >:: test_paper6;
              "paper #7" >:: test_paper7;
              "paper #8" >:: test_paper8;
              "paper #9" >:: test_paper9;
              "paper #10(a)" >:: test_paper10a;
              "paper #10(b)" >:: test_paper10b;
              "subst #1" >:: test_subst1;
              "subst #2" >:: test_subst2;
              "function cast" >:: test_function_cast;
              "Example roundtrips" >:: test_examples;
            ]


let () =
  run_test_tt_main suite
