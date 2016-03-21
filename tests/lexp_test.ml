open Lparse
open Debruijn   (* make_lexp_context *)
open Lexp 
open Utest_lib   

(* default environment *)
let lctx = make_lexp_context
let lctx = add_def "_+_" lctx
let lctx = add_def "_*_" lctx
    
(* Check if annotation are parsed and kept                  *)
(* Let and top level declarations are using the same code   *)
(* We only have to check if let's type parsing is correct   *)
let _ = (add_test "LEXP" "Type Parsing" (fun () ->
    
    (* This is garbage. I just want Nat to be defined *)
    let dcode = "
        Nat = inductive_ (dNat) (zero) (succ Nat);\n" in
        
    let _, lctx = lexp_decl_str dcode lctx in
    
    let ecode = "
        let a : Nat; a = 1; b : Nat; b = 3; 
            in 
                a + b;" in
        
    let ret, _ = lexp_expr_str ecode lctx in
        match ret with
            | [expr] ->(
            match expr with
                | Let(_, arg, _) -> match arg with
                    | [] -> failure ()
                    | (_, xp, tp)::_ ->(
                        (* tp must match Nat *)
                        match tp with
                            | Var((_, name), _) -> expect_equal_str name "Nat"
                            | _ -> failure ()
                      )
                | _ -> failure ())
            | [] -> failure ())
)
;;



run_all ()
;;