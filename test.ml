open OUnit2;;
open Ftal;;
open Examples;;
let f_expr str = Parse.parse_string Parse.f_expression_eof str

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
    let doc = TALP.p_component comp in
    let chan = open_out roundtrip in
    PPrintEngine.ToChannel.pretty 0.8 80 chan doc;
    flush chan;
    close_out chan;
  in
  write_source ();
  write_result ();
  match Parse.parse_file Parse.component_eof roundtrip with
  | exception exn ->
    Printf.eprintf "%!\nRountrip failure %S %S%!\n" orig roundtrip;
    comp
  | roundtripped_comp ->
    Sys.remove orig; Sys.remove roundtrip;
    roundtripped_comp

let tal_comp str =
  roundtrip ~source:str (Parse.parse_string Parse.component_eof str)

let empty = ([],[],[])

let assert_eint e n =
  match e with
  | F.EInt (_, x) -> assert_equal x n
  | _ -> assert_failure "not equal"


let test1 _ = assert_eint
    (snd (F.stepn 10 (empty, f_expr "1 + 1")))
    2

let test1_ty _ = assert_equal
    (FTAL.tc
       FTAL.default_context
       (FTAL.FC (f_expr "1 + 1")))
    (FTAL.FT F.TInt, TAL.SConcrete []);;

let test_f_app _ =
  assert_eint
    (snd (F.stepn 10 (empty, f_expr "(lam (x:int). x + x) 1")))
    2

let test_factorial_f _ =
  assert_eint
    (snd (F.stepn 300 (empty, F.EApp (dummy_loc, factorial_f, [F.EInt (dummy_loc, 3)]))))
    6


let assert_raises_typeerror (f : unit -> 'a) : unit =
  FTAL.(try (f (); assert_failure "didn't raise an exception")
        with TypeError _  -> ())

let call_st_exc2 =
   F.EBoundary (dummy_loc, F.TInt, None,
    tal_comp
      "([mv ra, lh;
         call l {*, end{int; *}}],
        [l -> box code [z, e]
               {ra: box forall[]. {r1:int; z} e; z} ra.
               [salloc 1;
                sst 0, ra;
                mv ra, l1h;
                call l1 {box forall[]. {r1:int; z} e :: *, 0}],
         l1 -> box code [z, e]
               {ra: box forall[]. {r1:int; z} e, r1: int; z} ra.
               [mv r1, 0;
                ret ra {r1}],
         l1h -> box code [] {r1:int; box forall[]. {r1:int; *} e :: *} 0. [sld ra, 0; sfree 1; ret ra {r1}],
         lh -> box code [] {r1:int; *} end{int; *}. [halt int, * {r1}]])")


let test_call_st_ty_exc2 _ =
  assert_raises_typeerror
    (fun _ -> FTAL.tc
       FTAL.default_context
       (FTAL.FC call_st_exc2))

let call_st_exc3 =
  F.EBoundary (dummy_loc, F.TInt, None,
    tal_comp
      "([mv ra, lh;
         call l {*, end{int; *}}],
        [l -> box code [z, e]
               {ra: box forall[]. {r1:int; z} e; z} ra.
               [salloc 1;
                sst 0, ra;
                mv ra, l1h;
                call l1 {*, 0}],
         l1 -> box code [z, e]
               {ra: box forall[]. {r1:int; z} e; z} ra.
               [mv r1, 0;
                ret ra {r1}],
         l1h -> box code [] {r1:int; box forall[]. {r1:int; *} e :: *} 0. [sld ra, 0; sfree 1; ret ra {r1}],
         lh -> box code [] {r1:int; *} end{int; *}. [halt int, * {r1}]])")

let test_call_st_ty_exc3 _ =
  assert_raises_typeerror
    (fun _ -> FTAL.tc
       FTAL.default_context
       (FTAL.FC call_st_exc3))


let test_factorial_f_ty _ =
  assert_equal
    (FTAL.tc
       FTAL.default_context
       (FTAL.FC factorial_f))
    (FTAL.FT (F.TArrow ([F.TInt], F.TInt)), TAL.SConcrete [])


let test_examples _ =
  let assert_roundtrip_f fexpr =
    let reparsed = Parse.parse_string Parse.f_expression_eof (Ftal.F.show_exp fexpr) in
    let rereparsed = Parse.parse_string Parse.f_expression_eof (Ftal.F.show_exp reparsed) in
    assert_equal reparsed rereparsed in
  let assert_roundtrip_c comp =
    let show_comp comp =
      let doc = Ftal.TALP.p_component comp in
      let buf = Buffer.create 123 in
      PPrintEngine.ToBuffer.pretty 0.8 80 buf doc;
      Buffer.contents buf in
    let reparsed = Parse.parse_string Parse.component_eof (show_comp comp) in
    let rereparsed = Parse.parse_string Parse.component_eof (show_comp reparsed) in
    assert_equal reparsed rereparsed in
  assert_roundtrip_f Examples.factorial_f;
  ()

let suite = "FTAL evaluations" >:::
            [
              "F: 1 + 1 = 2" >:: test1;
              "F: 1 + 1 : int" >:: test1_ty;
              "F: (lam x. x + x) 1 = 2" >:: test_f_app;
              (* "parse (5)" >:: test_parse5; TODO: should be removed? *)
              "F: fact 3 = 6" >:: test_factorial_f;
              "F: fact : int -> int" >:: test_factorial_f_ty;
              "Example roundtrips" >:: test_examples;
            ]


let () =
  run_test_tt_main suite
