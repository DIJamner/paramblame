open Ftal;;


(* Factorial Two Ways *)

let factorial_f = Parse.parse_string Parse.f_expression_eof {|
  lam (x2:int).
    (lam (fact : (mu a.(a, int) -> int, int) -> int).
       fact (fold (mu b.(b, int) -> int) fact) x2)
      (lam (f:mu a.(a, int) -> int, x1:int).
          if0 x1 1 (x1*((unfold f) f (x1-1))))
|}

