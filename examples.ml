open Ftal;;
          
let factorial_f = Parse.parse_string Parse.expression_eof {|
lam (x : int). x
|} 

(* lam (x2:int).
  (lam (fact : (( *, int) -> int, int) -> int).
     fact (fact : (( *, int) -> int, int) -> int => * ) x2)
    (lam (f: *, x1:int).
        if0 x1 1 (x1 * (f : * => (( *, int) -> int, int) -> int) f (x1-1)))) *)

let swap = Parse.parse_string Parse.expression_eof {|

 (Lam X. Lam Y. lam (p:<X,Y>). <pi2 p, pi1 p>) [int] [bool] <1,false>

|}

let double = Parse.parse_string Parse.expression_eof {|
let inc : int -> int = (lam (x : int). x + 1) in 
let double : (int -> int) -> int -> int = lam (f : int -> int). lam (x : int). f (f x) in 
double inc 0
|}   

let better-swap =  Parse.parse_string Parse.expression_eof {|

let swap : forall A.forall C.<A,C> -> <C,A> = Lam A. Lam C. lam (p : <A,C>). (<pi2 p, pi1 p>) in
swap [int] [bool] <5,false>

|}

let bad =  Parse.parse_string Parse.expression_eof {|

let bad : forall X.forall Y.<X,Y> -> int = Lam X. Lam Y. (lam (p : <X,Y>). pi1 p + pi2 p) in 
bad [int] [int] <1,2>

|}
