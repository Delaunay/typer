open Lparse     (* add_def       *)
open Debruijn   (* make_lexp_context *)
open Eval       (* make_rte_ctx *)
open Utest_lib   


(*      Let
 * ------------------------ *)
 
let _ = (add_test "LET" "Base Case" (fun () ->
    let lctx = make_lexp_context in
        let lctx = add_def "_+_" lctx in
        let lctx = add_def "_*_" lctx in
    let rctx = make_runtime_ctx in
    
    let ret = eval_expr_str "let a = 2; b = 3; in a + b;" lctx rctx in
        (* Expect a single result *)
        match ret with
            | [r] -> expect_equal_int 5 (get_int r)  
            | _ -> failure ())
)
;;


(*      Lambda
 * ------------------------ *)
let _ = (add_test "LAMBDA" "Base Case" (fun () ->
    let lctx = make_lexp_context in
        let lctx = add_def "_+_" lctx in
        let lctx = add_def "_*_" lctx in
    let rctx = make_runtime_ctx in
    
    (* Declare lambda *)
    let rctx, lctx = eval_decl_str "sqr = lambda x -> x * x;" lctx rctx in
    
    (* Eval defined lambda *)
    let ret = eval_expr_str "(sqr 4);" lctx rctx in
        (* Expect a single result *)
        match ret with
            | [r] -> expect_equal_int 16 (get_int r)  
            | _ -> failure ())
)
;;


(* run all tests *)
run_all ()
;;

