open Lparse     (* add_def       *)
open Debruijn   (* make_lexp_context *)
open Lexp
open Utest_lib   


(* default environment *)
let lctx = make_lexp_context
let lctx = add_def "_+_" lctx
let lctx = add_def "_*_" lctx

    
let _ = (add_test "LEXP" "Built-in Inference" (fun () ->
    
    let dcode = "a = 10; b = 1.12;" in
        
    let ret, _ = lexp_decl_str dcode lctx in
    
        match ret with
            | [(_, _, Builtin(_, "Int", _)); 
               (_, _, Builtin(_, "Float", _))] -> 
                success()
                
            | _ -> failure ())
);;
    


(* run all tests *)
run_all ()
;;

