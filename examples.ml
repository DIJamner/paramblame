open Ftal;;

let expr str = Parse.parse_string Parse.expression_eof str

let factorial = expr {|
lam (x2 : int).
  let fact : * -> int -> int = lam(fact : *).lam(x : int).
    if x = 0 then 1 else x * (fact : * => * -> int -> int) fact (x - 1)
  in fact (fact : * -> int -> int => *) x2
|} 

let swap_int_bool = expr {|
  pi2 ((Lam X. Lam Y. lam (p : <X,Y>). < pi2 p, pi1 p >) [int] [bool] <1, true>)
|}

let swap_bool_int = expr {|
  pi1 ((Lam X. Lam Y. lam (p : <X,Y>). < pi2 p, pi1 p >) [bool] [int] <true, 1>)
|}


