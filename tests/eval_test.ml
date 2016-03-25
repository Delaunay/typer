open Lparse     (* add_def       *)
open Debruijn   (* make_lexp_context *)
open Eval       (* make_rte_ctx *)
open Utest_lib
open Util
open Lexp


(* default environment *)
let lctx = make_lexp_context
let lctx = add_def "_+_" lctx
let lctx = add_def "_*_" lctx
let rctx = make_runtime_ctx
let rctx = add_rte_variable (Some "_+_") iop_binary rctx
let rctx = add_rte_variable (Some "_*_") iop_binary rctx

let _ = (add_test "EVAL" "Variable Cascade" (fun () ->

    let dcode = "
        a = 10;
        b = a;
        c = b;
        d = c;" in

    let rctx, lctx = eval_decl_str dcode lctx rctx in

    let ecode = "d;" in

    let ret = eval_expr_str ecode lctx rctx in

        match ret with
            | [r] -> expect_equal_int (get_int r) 10
            | _ -> failure ())
);;


(*      Let
 * ------------------------ *)

let _ = (add_test "EVAL" "Let" (fun () ->
    (* Noise. Makes sure the correct variables are selected *)
    let dcode = "
        c = 3; e = 1; f = 2; d = 4;" in
    let rctx, lctx = eval_decl_str dcode lctx rctx in

    let ecode = "
        let a = 10; x = 50; y = 60; b = 20; in a + b;" in

    let ret = eval_expr_str ecode lctx rctx in
        (* Expect a single result *)
        match ret with
            | [r] -> expect_equal_int (get_int r) 30
            | _ -> failure ())
)
;;


(*      Lambda
 * ------------------------ *)
let _ = (add_test "EVAL" "Lambda" (fun () ->

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

let _ = (add_test "EVAL" "Nested Lambda" (fun () ->
    let code = "
        sqr = lambda x -> x * x;
        cube = lambda x -> x * (sqr x);" in

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

(* This makes sure contexts are reinitialized between calls
 *  i.e the context should not grow                             *)
let _ = (add_test "EVAL" "Infinite Recursion failure" (fun () ->
    let code = "
        infinity = lambda beyond -> (infinity beyond);" in

    let rctx, lctx = eval_decl_str code lctx rctx in

    (* Expect throwing *)
    try         (*  use the silent version as an error will be thrown *)
        let _ = _eval_expr_str "(infinity 0);" lctx rctx true in
            failure ()
    with
        Internal_error m ->
            if m = "Recursion Depth exceeded" then
                success ()
            else
                failure ()
));;

(*      Cases + Inductive types
 * ------------------------ *)

let _ = (add_test "EVAL" "Case" (fun () ->
    (* Inductive type declaration + Noisy declarations *)
    let code = "
        i = 90;\n
        idt = inductive_ (idtd) (ctr0) (ctr1 idt) (ctr2 idt) (ctr3 idt);\n
        j = 100;\n
                                            d = 10;\n
        ctr0 = inductive-cons idt ctr0;\n   e = 20;\n
        ctr1 = inductive-cons idt ctr1;\n   f = 30;\n
        ctr2 = inductive-cons idt ctr2;\n   g = 40;\n
        ctr3 = inductive-cons idt ctr2;\n   h = 50;\n
                                    x = 1;\n
        a = (ctr1 (ctr2 ctr0));\n   y = 2;\n
        b = (ctr2 (ctr2 ctr0));\n   z = 3;\n
        c = (ctr3 (ctr2 ctr0));\n   w = 4;\n

        test_fun = lambda k -> case k\n
            | ctr1 l => 1\n
            | ctr2 l => 2\n
            | _ => 3;\n" in

    let rctx, lctx = eval_decl_str code lctx rctx in

    let rcode = "(test_fun a); (test_fun b); (test_fun c)"in

    (* Eval defined lambda *)
    let ret = eval_expr_str rcode lctx rctx in
        (* Expect 3 results *)
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

(*  Those wil be used multiple times *)
let nat_decl = "
    Nat = inductive_ (dNat) (zero) (succ Nat);

    zero = inductive-cons Nat zero;
    succ = inductive-cons Nat succ;

    tonum = lambda x -> case x\n
            | (succ y) => (1 + (tonum y))
            | zero => 0;"
;;

let bool_decl = "
    Bool = inductive (dBool) (true) (false);
    false = inductive-cons Bool false;
    true = inductive-cons Bool true;"
;;


let _ = (add_test "EVAL" "Recursive Call" (fun () ->

    let code = nat_decl ^ "
        one = (succ zero);
        two = (succ one);
        three = (succ three);" in

    let rctx, lctx = eval_decl_str code lctx rctx in

    let rcode = "(tonum zero); (tonum one); (tonum two);"in

    (* Eval defined lambda *)
    let ret = eval_expr_str rcode lctx rctx in
        (* Expect a 3 results *)
        match ret with
            | [a; b; c] ->
                let t1 = expect_equal_int (get_int a) 0 in
                let t2 = expect_equal_int (get_int b) 1 in
                let t3 = expect_equal_int (get_int c) 2 in
                    if t1 = 0 && t2 = 0 && t3 = 0 then
                        success ()
                    else
                        failure ()
            | _ -> failure ())
)
;;

let _ = (add_test "EVAL" "Nat Plus" (fun () ->

    let code = nat_decl ^ "
        one = (succ zero);
        two = (succ one);
        three = (succ three);

        plus = lambda x y -> case x
           | zero => y
           | succ z => succ (plus z y);
       " in

    let rctx, lctx = eval_decl_str code lctx rctx in

    let rcode = "
        (tonum (plus zero two));
        (tonum (plus two zero));
        5;"in

    (* Eval defined lambda *)
    let ret = eval_expr_str rcode lctx rctx in
        (* Expect a 3 results *)
        match ret with
            | [a; b; c] ->
                let t1 = expect_equal_int (get_int a) 2 in
                let t2 = expect_equal_int (get_int b) 2 in
                let t3 = expect_equal_int (get_int c) 5 in
                    if t1 = 0 && t2 = 0 && t3 = 0 then
                        success ()
                    else
                        failure ()
            | _ -> failure ())
)
;;

(*
List = inductive (dList (a : Type)) (nil) (cons a (List a));

nil = inductive-cons List nil;
cons = inductive-cons List cons;

length : (a : Type) => List a -> Nat;
length = lambda a => lambda (xs : List a) ->
    case xs
        | nil => zero
        | cons x xs => succ (length xs);
*)



(* run all tests *)
run_all ()
;;

