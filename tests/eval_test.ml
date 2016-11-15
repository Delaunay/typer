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

(* Params:
 *  decl: declarations to be processed before evaluating
 *  run : expr to be evaluated
 *  res : expected result
 *)
let test_eval_eqv_named name decl run res =
  add_test "EVAL" name (fun () ->
    let rctx, lctx = eval_decl_str decl lctx rctx in

    let erun = eval_expr_str run lctx rctx in (* evaluated run expr *)
    let eres = eval_expr_str res lctx rctx in (* evaluated res expr *)

      if value_eq_list erun eres
      then success ()
      else (
        value_print (List.hd erun);
        value_print (List.hd eres);
        failure ()))

let test_eval_eqv decl run res = test_eval_eqv_named run decl run res

let _ = test_eval_eqv "" "2 + 2" "4"

let _ = test_eval_eqv_named
  "Variable Cascade"

  "a = 10; b = a; c = b; d = c;"

  "d" (* == *) "10"

(*      Let
 * ------------------------ *)

let _ = test_eval_eqv_named
  "Let"

  "c = 3; e = 1; f = 2; d = 4;"

  "let a = 10; x = 50; y = 60; b = 20;
    in a + b;" (* == *) "30"

let _ = test_eval_eqv_named
  "Let2"

  "c = 3; e = 1; f = 2; d = 4;"

  "let TrueProp = inductive_ TrueProp I;
       I = inductive-cons TrueProp I;
       x = let a = 1; b = 2 in I
    in (case x | I => c) : Int;" (* == *) "3"

let _ = test_eval_eqv_named
  "Let3"

  "c = 3; e = 1; f = 2; d = 4;"

  "let TrueProp : Type;
       I : TrueProp;
       TrueProp = inductive_ TrueProp I;
       I = inductive-cons TrueProp I;
       x = let a = 1; b = 2 in I
    in (case x | I => c) : Int;" (* == *) "3"

(*      Lambda
 * ------------------------ *)

let _ = test_eval_eqv_named
  "Lambda"

  "sqr : Int -> Int;
   sqr = lambda x -> x * x;"

  "sqr 4;" (* == *) "16"

let _ = test_eval_eqv_named
  "Nested Lambda"

  "sqr : Int -> Int;
   sqr = lambda x -> x * x;

   cube : Int -> Int;
   cube = lambda x -> x * (sqr x);"

  "cube 4" (* == *) "64"


(*      Cases + Inductive types
 * ------------------------ *)

let _ = test_eval_eqv_named
  "Inductive::Case"

  "i = 90;
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

   test_fun : idt -> Int;
   test_fun = lambda k -> case k
      | ctr1 l => 1
      | ctr2 l => 2
      | _ => 3;"

  "test_fun a; test_fun b; test_fun c"

  "1; 2; 3"

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

let _ = test_eval_eqv_named
  "Inductive::Recursive Call"

  (nat_decl ^ "
   one = succ zero;
   two = succ one;
   three = succ two;")

  "to-num zero; to-num one; to-num two;"

  "0; 1; 2"

let _ = test_eval_eqv_named
  "Inductive::Nat Plus"

  (nat_decl ^ "
   one = succ zero;
   two = succ one;
   three = succ two;

   plus : Nat -> Nat -> Nat;
   plus = lambda (x : Nat) -> lambda (y : Nat) -> case x
       | zero => y
       | succ z => succ (plus z y);")

  "to-num (plus zero two);
   to-num (plus two zero);
   to-num (plus two one);"

  "2; 2; 3"

let _ = test_eval_eqv_named
  "Mutually Recursive Definition"

  (nat_decl ^ "
   one = succ zero;
   two = succ one;
   three = succ two;

   even : Nat -> Int;
   odd : Nat -> Int;

   odd = lambda (n : Nat) -> case n
      | zero => 0
      | succ y => (even y);

   even = lambda (n : Nat) -> case n
      | zero => 1
      | succ y => (odd y);")

  "odd one; even one; odd two; even two;"

  "1; 0; 0; 1"


let _ = test_eval_eqv_named
  "Partial Application"

  "add : Int -> Int -> Int;
   add = lambda x y -> (x + y);

   inc : Int -> Int;
   inc = add 1;"

  "inc 1; inc 2; inc 3;"

  "2; 3; 4"

(*
 *  Lists
 *)
let _ = test_eval_eqv_named
  "Lists"

  "my_list = cons 1
            (cons 2
            (cons 3
            (cons 4 nil)))"

  "length my_list;
   head my_list;
   head (tail my_list)"

  "4; Some 1; Some 2"

(*
 *  Special forms
 *)
let _ = test_eval_eqv "w = 2" "decltype w" "Int"
let _ = test_eval_eqv "w = 2" "declexpr w" "2"

let attr_decl = "
  w = 2;
  greater-than = new-attribute (Int -> Bool);
  attribute w greater-than (lambda (y : Int) -> True);"

let _ = test_eval_eqv attr_decl
  "has-attribute w greater-than"
  "True"

(* This makes sure contexts are reinitialized between calls
 *  i.e the context should not grow                             *)
let _ = (add_test "EVAL" "Infinite Recursion failure" (fun () ->
    _typer_verbose := (-1);

    let code = "
        infinity : Int -> Int;
        infinity = lambda beyond -> infinity beyond;" in

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

let _ = (add_test "EVAL" "Monads" (fun () ->

    let dcode = "
      c = bind (open \"./_build/w_file.txt\" \"w\")
               (lambda f -> write f \"Hello2\");
    " in

    let rctx, lctx = eval_decl_str dcode lctx rctx in

    let rcode = "run-io c 2" in

    (* Eval defined lambda *)
    let ret = eval_expr_str rcode lctx rctx in
        match ret with
            | [v] -> success ()
            | _ -> failure ()
))

let _ = test_eval_eqv_named
  "Argument Reordering"

  "fun = lambda (x : Int) =>
      lambda (y : Int) ->
        lambda (z : Int) -> x * y + z;"

  "fun (x := 3) 2 1;
   fun (x := 3) (z := 1) 4;
   fun (z := 3) (y := 2) (x := 1);
   fun (z := 1) (y := 2) (x := 3);
   fun (x := 3) (y := 2) (z := 1);"

  "7; 13; 5; 7; 7"

let _ = test_eval_eqv_named "Metavars"
  "f : ?;
   f x = 2 + f (1 + x);"

  "1" "1"

let _ = test_eval_eqv_named
  "Explicit field patterns"
  "Triplet = inductive_ Triplet
             (triplet (a ::: Int) (b :: Float) (c : String));
   triplet = inductive-cons Triplet triplet;
   t = triplet (b := 5.0) (a := 3) (c := \"hello\");"

  "case t | triplet (b := bf) cf => cf;
   case t | triplet (b := bf) cf => bf;
   case t | triplet ( _ := bf) cf => cf;
   case t | triplet ( _ := af) ( _ := bf) ( _ := cf) => bf;
   case t | triplet ( _ := af) ( _ := bf) ( _ := cf) => cf;
  "

  "\"hello\"; 5.0; \"hello\"; 5.0; \"hello\"
  "

let _ = test_eval_eqv_named
  "Implicit Arguments"

  "default = new-attribute (Int -> Bool);
   attribute Int default (lambda (lst : List Sexp) -> integer_ 1);

   fun = lambda (x : Int) =>
      lambda (y : Int) ->
        lambda (z : Int) -> x * y + z;"

  "fun 2 1;
   fun (z := 1) (y := 2)"

  "3; 3"


(* run all tests *)
let _ = run_all ()

