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

open Utest_lib
open Util

open Sexp
open Lexp

open Lparse     (* eval string      *)
open Eval       (* reset_eval_trace *)

open Builtin
open Env

(* default environment *)
let lctx = default_lctx
let rctx = default_rctx

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
            | [Vint(r)] -> expect_equal_int r 10
            | _ -> failure ())
)


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
            | [Vint(r)] -> expect_equal_int r 30
            | _ -> failure ())
)


(*      Lambda
 * ------------------------ *)
let _ = (add_test "EVAL" "Lambda" (fun () ->
    reset_eval_trace ();

    let dcode = "
        sqr : Int -> Int;
        sqr = lambda x -> x * x;
    " in

    (* Declare lambda *)
    let rctx, lctx = eval_decl_str dcode lctx rctx in

    (* Eval defined lambda *)
    let ret = eval_expr_str "(sqr 4);" lctx rctx in
        (* Expect a single result *)
        match ret with
            | [Vint(r)] -> expect_equal_int r (4 * 4)
            | _ -> failure ())
)

let _ = (add_test "EVAL" "Nested Lambda" (fun () ->
    reset_eval_trace ();

    let code = "
        sqr : Int -> Int;
        sqr = lambda x -> x * x;

        cube : Int -> Int;
        cube = lambda x -> x * (sqr x);" in

    (* Declare lambda *)
    let rctx, lctx = eval_decl_str code lctx rctx in

    (* Eval defined lambda *)
    let ret = eval_expr_str "(cube 4);" lctx rctx in
        (* Expect a single result *)
        match ret with
            | [Vint(r)] -> expect_equal_int r (4 * 4 * 4)
            | _ -> failure ())
)

(* This makes sure contexts are reinitialized between calls
 *  i.e the context should not grow                             *)
let _ = (add_test "EVAL" "Infinite Recursion failure" (fun () ->
    reset_eval_trace ();
    _typer_verbose := (-1);

    let code = "
        infinity : Int -> Int;
        infinity = lambda (beyond : Int) -> (infinity beyond);" in

    let rctx, lctx = eval_decl_str code lctx rctx in

    (* Expect throwing *)
    try         (*  use the silent version as an error will be thrown *)
        let _ = _eval_expr_str "(infinity 0);" lctx rctx true in
            _typer_verbose := 20;
            failure ()
    with
        Internal_error m -> (
            _typer_verbose := 20;
            if m = "Recursion Depth exceeded" then
                success ()
            else
                failure ())
))

(*      Cases + Inductive types
 * ------------------------ *)

let _ = (add_test "EVAL" "Inductive::Case" (fun () ->
    reset_eval_trace ();

    (* Inductive type declaration + Noisy declarations *)
    let code = "
        i = 90;
        idt : Type;
        idt = inductive_ (idtd) (ctr0) (ctr1 idt) (ctr2 idt) (ctr3 idt);
                                          d = 10;
        ctr0 = inductive-cons idt ctr0;   e = 20;
        ctr1 = inductive-cons idt ctr1;   f = 30;
        ctr2 = inductive-cons idt ctr2;   g = 40;
        ctr3 = inductive-cons idt ctr3;   h = 50;

        a = (ctr1 (ctr2 ctr0));   y = 2;
        b = (ctr2 (ctr2 ctr0));   z = 3;
        c = (ctr3 (ctr2 ctr0));   w = 4;

        test_fun = lambda (k : idt) -> case k
            | ctr1 l => 1
            | ctr2 l => 2
            | _ => 3;" in

    let rctx, lctx = eval_decl_str code lctx rctx in

    let rcode = "(test_fun a); (test_fun b); (test_fun c)"in

    (* Eval defined lambda *)
    let ret = eval_expr_str rcode lctx rctx in
        (* Expect 3 results *)
        match ret with
            | [Vint(a); Vint(b); Vint(c)] ->
                let t1 = expect_equal_int a 1 in
                let t2 = expect_equal_int b 2 in
                let t3 = expect_equal_int c 3 in
                    if t1 = 0 && t2 = 0 && t3 = 0 then
                        success ()
                    else
                        failure ()
            | _ -> failure ()
))

(*  Those wil be used multiple times *)
let nat_decl = "
    Nat : Type;
    Nat = inductive_ (dNat) (zero) (succ Nat);

    zero = inductive-cons Nat zero;
    succ = inductive-cons Nat succ;

    to-num : Nat -> Int;
    to-num = lambda (x : Nat) -> case x
            | (succ y) => (1 + (to-num y))
            | zero => 0;"

let bool_decl = "
    Bool = inductive (dBool) (true) (false);
    false = inductive-cons Bool false;
    true = inductive-cons Bool true;"

let _ = (add_test "EVAL" "Inductive::Recursive Call" (fun () ->
    reset_eval_trace ();

    let code = nat_decl ^ "
        one = (succ zero);
        two = (succ one);
        three = (succ two);" in

    let rctx, lctx = eval_decl_str code lctx rctx in

    let rcode = "(to-num zero); (to-num one); (to-num two);"in

    (* Eval defined lambda *)
    let ret = eval_expr_str rcode lctx rctx in
        (* Expect a 3 results *)
        match ret with
            | [Vint(a); Vint(b); Vint(c)] ->
                let t1 = expect_equal_int a 0 in
                let t2 = expect_equal_int b 1 in
                let t3 = expect_equal_int c 2 in
                    if t1 = 0 && t2 = 0 && t3 = 0 then
                        success ()
                    else
                        failure ()
            | _ -> failure ())
)

let _ = (add_test "EVAL" "Inductive::Nat Plus" (fun () ->
    reset_eval_trace ();

    let code = nat_decl ^ "
        one = (succ zero);
        two = (succ one);
        three = (succ two);

        plus : Nat -> Nat -> Nat;
        plus = lambda (x : Nat) -> lambda (y : Nat) -> case x
            | zero => y
            | succ z => succ (plus z y);
       " in

    let rctx, lctx = eval_decl_str code lctx rctx in

    let rcode = "
        (to-num (plus zero two));
        (to-num (plus two zero));
        (to-num (plus two one));"in

    (* Eval defined lambda *)
    let ret = eval_expr_str rcode lctx rctx in
        (* Expect a 3 results *)
        match ret with
            | [Vint(a); Vint(b); Vint(c)] ->
                let t1 = expect_equal_int a 2 in
                let t2 = expect_equal_int b 2 in
                let t3 = expect_equal_int c 3 in
                    if t1 = 0 && t2 = 0 && t3 = 0 then
                        success ()
                    else
                        failure ()
            | _ -> failure ()
))

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
            | [Vint(a); Vint(b); Vint(c); Vint(d)] ->
                let t1 = expect_equal_int a 1 in
                let t2 = expect_equal_int b 0 in
                let t3 = expect_equal_int c 0 in
                let t4 = expect_equal_int d 1 in
                    if t1 = 0 && t2 = 0 && t3 = 0 && t4 = 0 then
                        success ()
                    else
                        failure ()
            | _ -> failure ()
))


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
            | [Vint(a); Vint(b); Vint(c)] ->
                let t1 = expect_equal_int a 2 in
                let t2 = expect_equal_int b 3 in
                let t3 = expect_equal_int c 4 in
                    if t1 = 0 && t2 = 0 && t3 = 0 then
                        success ()
                    else
                        failure ()
            | _ -> failure ()
))


let _ = (add_test "EVAL" "List" (fun () ->
    reset_eval_trace ();

    let dcode = "
        my_list = (cons 1 (cons 2 (cons 3 (cons 4 nil))));
    " in

    let rctx, lctx = eval_decl_str dcode lctx rctx in

    let rcode = "(length Int my_list);
                 (head Int my_list);
                 (head Int (tail Int my_list));" in

    (* Eval defined lambda *)
    let ret = eval_expr_str rcode lctx rctx in
        (* Expect a 3 results *)
        match ret with
            | [Vint(a); Vint(b); Vint(c)] ->
                let t1 = expect_equal_int a 4 in
                let t2 = expect_equal_int b 1 in
                let t3 = expect_equal_int c 2 in
                    if t1 = 0 && t2 = 0 && t3 = 0 then
                        success ()
                    else
                        failure ()
            | _ -> failure ()
))


(* run all tests *)
let _ = run_all ()

