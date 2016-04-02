(*
 *      Typer Compiler
 *
 * ---------------------------------------------------------------------------
 *
 *      Copyright (C) 2011-2016  Free Software Foundation, Inc.
 *
 *   Author: Pierre Delaunay <pierre.delaunay@hec.ca>
 *   Keywords: languages, lisp, dependent types.
 *
 *   This file is part of Typer.
 *
 *   Typer is free software; you can redistribute it and/or modify it under the
 *   terms of the GNU General Public License as published by the Free Software
 *   Foundation, either version 3 of the License, or (at your option) any
 *   later version.
 *
 *   Typer is distributed in the hope that it will be useful, but WITHOUT ANY
 *   WARRANTY; without even the implied warranty of MERCHANTABILITY or FITNESS
 *   FOR A PARTICULAR PURPOSE.  See the GNU General Public License for
 *   more details.
 *
 *   You should have received a copy of the GNU General Public License along
 *   with this program.  If not, see <http://www.gnu.org/licenses/>.
 *
 * --------------------------------------------------------------------------- *)

open Util
open Utest_lib

open Sexp
open Lexp

open Lparse     (* eval string      *)
open Eval       (* reset_eval_trace *)

open Builtin


let get_int lxp =
    match lxp with
        | Imm(Integer(_, l)) -> l
        | _ -> (-40);
;;


(* default environment *)
let lctx = default_lctx ()
let rctx = default_rctx ()

let _ = (add_test "EVAL" "Variable Cascade" (fun () ->
    reset_eval_trace ();

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
    reset_eval_trace ();

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
    reset_eval_trace ();

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
    reset_eval_trace ();

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
    reset_eval_trace ();

    let code = "
        infinity : Int -> Int;
        infinity = lambda (beyond : Int) -> (infinity beyond);" in

    let rctx, lctx = eval_decl_str code lctx rctx in

    (* Expect throwing *)
    try         (*  use the silent version as an error will be thrown *)
        let _ = _eval_expr_str "(infinity 0);" lctx rctx true in
            failure ()
    with
        Internal_error m -> (
            if m = "Recursion Depth exceeded" then
                success ()
            else
                failure ())
));;

(*      Cases + Inductive types
 * ------------------------ *)

let _ = (add_test "EVAL" "Inductive::Case" (fun () ->
    reset_eval_trace ();

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
            | _ -> failure ()
));;

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

let _ = (add_test "EVAL" "Inductive::Recursive Call" (fun () ->
    reset_eval_trace ();

    let code = nat_decl ^ "
        one = (succ zero);
        two = (succ one);
        three = (succ two);" in

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

let _ = (add_test "EVAL" "Inductive::Nat Plus" (fun () ->
    reset_eval_trace ();

    let code = nat_decl ^ "
        one = (succ zero);
        two = (succ one);
        three = (succ two);

        plus = lambda (x : Nat) -> lambda (y : Nat) -> case x
            | zero => y
            | succ z => succ (plus z y);
       " in

    let rctx, lctx = eval_decl_str code lctx rctx in

    let rcode = "
        (tonum (plus zero two));
        (tonum (plus two zero));
        (tonum (plus two one));"in

    (* Eval defined lambda *)
    let ret = eval_expr_str rcode lctx rctx in
        (* Expect a 3 results *)
        match ret with
            | [a; b; c] ->
                let t1 = expect_equal_int (get_int a) 2 in
                let t2 = expect_equal_int (get_int b) 2 in
                let t3 = expect_equal_int (get_int c) 3 in
                    if t1 = 0 && t2 = 0 && t3 = 0 then
                        success ()
                    else
                        failure ()
            | _ -> failure ()
));;

let _ = (add_test "EVAL" "Mutually Recursive Definition" (fun () ->
    reset_eval_trace ();

    let dcode = nat_decl ^ "
        one = (succ zero);
        two = (succ one);
        three = (succ two);

        odd : Nat -> Int;
        even : Nat -> Int;
        odd = lambda (n : Nat) -> case n
            | zero => 0
            | succ y => (even y);

        even = lambda (n : Nat) -> case n
            | zero => 1
            | succ y => (odd y);" in

    let rctx, lctx = eval_decl_str dcode lctx rctx in

    let rcode = "(odd one); (even one); (odd two); (even two);" in

    (* Eval defined lambda *)
    let ret = eval_expr_str rcode lctx rctx in
        (* Expect a 3 results *)
        match ret with
            | [a; b; c; d] ->
                let t1 = expect_equal_int (get_int a) 1 in
                let t2 = expect_equal_int (get_int b) 0 in
                let t3 = expect_equal_int (get_int c) 0 in
                let t4 = expect_equal_int (get_int d) 1 in
                    if t1 = 0 && t2 = 0 && t3 = 0 && t4 = 0 then
                        success ()
                    else
                        failure ()
            | _ -> failure ()
));;


let _ = (add_test "EVAL" "Partial Application" (fun () ->
    reset_eval_trace ();

    let dcode = "
        add : Int -> Int -> Int;
        add = lambda x y -> (x + y);

        inc : Int -> Int;
        inc = (add 1);" in

    let rctx, lctx = eval_decl_str dcode lctx rctx in

    let rcode = "(inc 1); (inc 2); (inc 3);" in

    (* Eval defined lambda *)
    let ret = eval_expr_str rcode lctx rctx in
        (* Expect a 3 results *)
        match ret with
            | [a; b; c] ->
                let t1 = expect_equal_int (get_int a) 2 in
                let t2 = expect_equal_int (get_int b) 3 in
                let t3 = expect_equal_int (get_int c) 4 in
                    if t1 = 0 && t2 = 0 && t3 = 0 then
                        success ()
                    else
                        failure ()
            | _ -> failure ()
));;

(*
List = inductive_ (dList (a : Type)) (nil) (cons a (List a));

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

