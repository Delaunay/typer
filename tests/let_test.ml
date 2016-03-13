open Lparse     (* add_def       *)
open Debruijn   (* make_lexp_context *)
open Eval       (* make_rte_ctx *)
open Utest_lib   


(* default environment *)
let lctx = make_lexp_context
let lctx = add_def "_+_" lctx
let lctx = add_def "_*_" lctx
let rctx = make_runtime_ctx 
    
    
(*      Let
 * ------------------------ *)
 
let _ = (add_test "LET" "Base Case" (fun () ->
    (* Noise. Makes sure the correct variables are selected *)
    let dcode = "
        c = 3; a = 1; b = 2; d = 4;" in
    let rctx, lctx = eval_decl_str dcode lctx rctx in
        
    let ecode = "
        let a = 10; x = 50; y = 60; b = 20; in a + b;" in
       
    let ret = eval_expr_str ecode lctx rctx in
        (* Expect a single result *)
        match ret with
            | [r] -> expect_equal_int 30 (get_int r)  
            | _ -> failure ())
)
;;


(*      Lambda
 * ------------------------ *)
let _ = (add_test "LAMBDA" "Base Case" (fun () ->
    (* Declare lambda *)
    let rctx, lctx = eval_decl_str "sqr = lambda x -> x * x;" lctx rctx in
    
    (* Eval defined lambda *)
    let ret = eval_expr_str "(sqr 4);" lctx rctx in
        (* Expect a single result *)
        match ret with
            | [r] -> expect_equal_int (get_int r) (4 * 4)
            | _ -> failure ())
)
;;

let _ = (add_test "LAMBDA" "Nested" (fun () ->
    let code = "
        sqr = lambda x -> x * x;
        cube = lambda x -> x * (sqr x); " in
    
    (* Declare lambda *)
    let rctx, lctx = eval_decl_str code lctx rctx in
    
    (* Eval defined lambda *)
    let ret = eval_expr_str "(cube 4);" lctx rctx in
        (* Expect a single result *)
        match ret with
            | [r] -> expect_equal_int (get_int r) (4 * 4 * 4)
            | _ -> failure ())
)
;;

(*      Cases + Inductive types
 * ------------------------ *)
 
let _ = (add_test "Case" "Base Case" (fun () ->
    (* Inductive type declaration *)
    let code = "
        idt = inductive_ (idtd) (ctr0) (ctr1 idt) (ctr2 idt) (ctr3 idt);\n
        
        ctr0 = inductive-cons idt ctr0;\n
        ctr1 = inductive-cons idt ctr1;\n
        ctr2 = inductive-cons idt ctr2;\n
        ctr3 = inductive-cons idt ctr2;\n
        
        a = (ctr1 (ctr2 ctr0));\n
        b = (ctr2 (ctr2 ctr0));\n
        c = (ctr3 (ctr2 ctr0));\n

        test_fun = lambda x -> case x\n
            | ctr1 y => 1\n
            | ctr2 y => 2\n
            | _ => 3;\n" in
                
    let rctx, lctx = eval_decl_str code lctx rctx in
    
    let rcode = "(test_fun a); (test_fun b); (test_fun c)"in
                 
    (* Eval defined lambda *)
    let ret = eval_expr_str rcode lctx rctx in
        (* Expect a 3 results *)
        match ret with
            | [a; b; c] ->  
                let t1 = expect_equal_int (get_int a) 1 in 
                let t2 = expect_equal_int (get_int b) 2 in
                let t3 = expect_equal_int (get_int c) 3 in
                    if t1 = 0 && t2 = 0 && t3 = 0 then
                        success ()
                    else
                        failure ()
            | _ -> failure ())
)
;;

let _ = (add_test "MISC" "Recursive Call" (fun () ->
    (* Inductive type declaration *)
    let code = "
        Nat = inductive_ (dNat) (zero) (succ Nat);
        
        zero = inductive-cons Nat zero; 
        succ = inductive-cons Nat succ;
        
        one = (succ zero);
        two = (succ one);
        three = (succ three);

        tonum = lambda x -> case x 
            | (succ y) => (1 + (tonum y))
            | _ => 0;" in
                
    let rctx, lctx = eval_decl_str code lctx rctx in
    
    let rcode = "(tonum zero)"in
                 
    (* Eval defined lambda *)
    let ret = eval_expr_str rcode lctx rctx in
        (* Expect a 3 results *)
        match ret with
            | [a] -> expect_equal_int (get_int a) 0
                
            (*| [a; b; c] ->  
                let t1 = expect_equal_int (get_int a) 1 in 
                let t2 = expect_equal_int (get_int b) 2 in
                let t3 = expect_equal_int (get_int c) 3 in
                    if t1 = 0 && t2 = 0 && t3 = 0 then
                        success ()
                    else
                        failure () *)
            | _ -> failure ())
)
;;



(* run all tests *)
run_all ()
;;

