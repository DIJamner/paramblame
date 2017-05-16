open Ftal;;
          
let factorial_f = Parse.parse_string Parse.expression_eof {|
lam (x2 : int).
  let fact : * -> int -> int = lam(fact : *).lam(x : int).
    if x = 0 then 1 else x * (fact : * => * -> int -> int) fact (x - 1)
  in fact (fact : * -> int -> int => *) x2
|} 

