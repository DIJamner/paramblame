open Ftal;;
          
let factorial_f = Parse.parse_string Parse.expression_eof {|
lam (x : int). x
|} 

(* lam (x2:int).
  (lam (fact : (( *, int) -> int, int) -> int).
     fact (fact : (( *, int) -> int, int) -> int => * ) x2)
    (lam (f: *, x1:int).
        if0 x1 1 (x1 * (f : * => (( *, int) -> int, int) -> int) f (x1-1)))) *)
