open OUnit2;;
open Ftal;;
open Examples;;
let expr str = Parse.parse_string Parse.expression_eof str

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

let test1 _ = assert_eint
    (snd (Lang.stepn 10 ([], expr "1 + 1")))
    2

let test1_ty _ = assert_equal
    (Lang.expType [] [] [] (expr "1 + 1"))
    (Ok Lang.IntTy);;

let test_app _ =
  assert_eint
    (snd (Lang.stepn 10 ([], expr "(lam (x:int). x + x) 1")))
    2

let test_factorial_f _ =
  lang_assert_eint
    (snd (Lang.stepn 300 ([], Lang.(AppExp (Examples.factorial_f, IntExp 3)))))
    6


let assert_raises_typeerror (f : unit -> 'a) : unit =
  FTAL.(try (f (); assert_failure "didn't raise an exception")
        with TypeError _  -> ())


let test_factorial_f_ty _ =
  assert_equal
    (Lang.expType [] [] [] factorial_f)
    (Ok Lang.(FunTy (IntTy, IntTy)))


let test_examples _ =
  let assert_roundtrip expr =
    let reparsed = Parse.parse_string Parse.expression_eof (Ftal.Lang.show_exp expr) in
    let rereparsed = Parse.parse_string Parse.expression_eof (Ftal.Lang.show_exp reparsed) in
    assert_equal reparsed rereparsed in
  assert_roundtrip Examples.factorial_f;
  ()

let suite = "FTAL evaluations" >:::
            [
              "F: 1 + 1 = 2" >:: test1;
              "F: 1 + 1 : int" >:: test1_ty;
              "F: (lam x. x + x) 1 = 2" >:: test_app;
              (* "parse (5)" >:: test_parse5; TODO: should be removed? *)
              "F: fact 3 = 6" >:: test_factorial_f;
              "F: fact : int -> int" >:: test_factorial_f_ty;
              "Example roundtrips" >:: test_examples;
            ]


let () =
  run_test_tt_main suite
