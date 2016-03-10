
open Eval


(*  How to make macro in ocaml? *)

(*
let EXPECT_EQUAL a b = 
    if a = b then(print_string "[     OK]\n"; SUCCESS) 
    else( print_string "[   FAIL]\n"; FAILURE)
;;

let EXPECT_THROW a error =
    try ((a); print_string "[   FAIL]\n"; FAILURE)  
    with  (print_string "[     OK]\n"; SUCCESS) 
;; *)


let main () =

    let ret = easy_eval_string "let a = 3; b = 5; in a + b;" in
        match ret with
        | [xpr] -> let v = get_int xpr in
            if v = 8 then (exit 0) else (exit (-1))
        | _ -> exit (-1)
    
;;

main ()
;;