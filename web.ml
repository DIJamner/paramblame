module H = Dom_html

let simple = {|
FT [int, ?] (
  [mv r1, 1;
   add r1, r1, 1;
   halt int, * {r1}],
  [])
|}

let higher_order = Ftal.F.show_exp Examples.higher_order
let factorial_f = Ftal.F.(show_exp (EApp (Examples.factorial_f, [EInt 3])))
let factorial_t = Ftal.F.(show_exp (EApp (Examples.factorial_t, [EInt 3])))
let call_to_call = Ftal.F.show_exp (Ftal.F.(EBoundary (TInt, None, Examples.call_to_call)))
let blocks_1 = Ftal.F.show_exp Examples.blocks_1
let blocks_2 = Ftal.F.show_exp Examples.blocks_2


let set_error ln m =
  let _ = Js.Unsafe.((coerce global)##seterror (Js.number_of_float (float_of_int ln)) (Js.string m)) in
  ()
let clear_errors _ =
  let _ = Js.Unsafe.((coerce global)##.clearerrors) in
  ()

let hide_machine _ =
  H.((getElementById "machine")##setAttribute (Js.string "hidden") (Js.string "on"))
let show_machine _ =
  H.((getElementById "machine")##removeAttribute (Js.string "hidden"))
let set_text i t =
  let open H in
  (getElementById i)##.innerHTML := Js.string t
let set_editor t =
  let open Js in
  clear_errors ();
  hide_machine ();
  let _ = Unsafe.((coerce (global##.codemirror))##setValue (string t)) in
  ()
let ehandle s =
  H.handler (fun _ -> set_editor s; Js._false)
let get_editor _ =
  Js.Unsafe.((coerce (global##.codemirror))##getValue)
let set_click i h =
  H.((getElementById i)##.onclick := h);
  ()

let _ =
  let hist = ref ((Ftal.F.EUnit, ([],[],[])), []) in
  let refresh _ =
    let ((e, (h,r,s)), past) = !hist in
    let _ = match Ftal.F.decomp e with
      | None ->
        H.((getElementById "next")##setAttribute (Js.string "disabled") (Js.string "on"));
        H.((getElementById "many")##setAttribute (Js.string "disabled") (Js.string "on"));
        let _ = set_text "context" (Ftal.F.show_exp e) in
        let _ = set_text "focus" "" in
        ()
      | Some (c, f) ->
        H.((getElementById "next")##removeAttribute (Js.string "disabled"));
        H.((getElementById "many")##removeAttribute (Js.string "disabled"));
        let _ = set_text "context" (Ftal.F.show_context c) in
        let _ = set_text "focus" (Ftal.F.show_ft f) in
        ()
    in
    let _ = set_text "pc" (string_of_int (List.length past)) in
    let _ = set_text "registers" (Ftal.TAL.show_regm r) in
    let _ = set_text "stack" (Ftal.TAL.show_stackm s) in
    let _ = set_text "heap" (Ftal.TAL.show_heapm h) in
    ()
  in
  let next' _ =
    let ((e,m), rest) = !hist in
    let (nm,ne) = Ftal.F.step (m, e) in
    if e = ne && m = nm
    then ()
    else hist := ((ne,nm), (e,m)::rest)
  in
  let load _ =
    let open H in
    let _ =
      let s = Js.to_string (get_editor ()) in
      Ftal.(FTAL.(
          try
            let e = Parse.parse_string Parser.f_expression_eof s in
            let _ = tc (default_context TAL.QOut) (FC e) in
            hist := ((e, ([],[],[])), []);
            refresh ();
            clear_errors ();
            show_machine ();
            Js.Opt.return Js._false
          with TypeError (t,_)
             | TypeErrorW (t,_)
             | TypeErrorH (t,_,_)
             | TypeErrorU (t,_)  ->
            begin
              set_error 3 ("Type Error: " ^ t);
              hide_machine ();
              Js.Opt.return Js._false
            end
             | x ->
               set_error 3 "Parse Error";
               hide_machine ();
               Js.Opt.return Js._false
        )) in Js._false
  in
  let next _ =
    next' ();
    refresh ();
    Js._false
  in
  let prev _ =
    begin match !hist with
      | (_, []) -> ()
      | (_, x::xs) -> hist := (x,xs); refresh ()
    end; Js._false
  in
  let many _ =
    let rec repeat f = function | 0 -> () | n -> f (); repeat f (n-1) in
    repeat next' 100;
    refresh ();
    Js._false
  in
  set_click "load" (H.handler load);
  set_click "next" (H.handler next);
  set_click "prev" (H.handler prev);
  set_click "many" (H.handler many);
  hide_machine ();
  set_click "simple" (ehandle simple);
  set_click "call_to_call" (ehandle call_to_call);
  set_click "higher_order" (ehandle higher_order);
  set_click "blocks_1" (ehandle blocks_1);
  set_click "blocks_2" (ehandle blocks_2);
  set_click "factorial_f" (ehandle factorial_f);
  set_click "factorial_t" (ehandle factorial_t);
  set_editor simple;
  ()
