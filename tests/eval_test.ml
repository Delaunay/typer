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
let ectx = default_ectx
let rctx = default_rctx

(* Params:
 *  decl: declarations to be processed before evaluating
 *  run : expr to be evaluated
 *  res : expected result
 *)
let test_eval_eqv_named name decl run res =
  add_test "EVAL" name (fun () ->
    let rctx, ectx = eval_decl_str decl ectx rctx in

    let erun = eval_expr_str run ectx rctx in (* evaluated run expr *)
    let eres = eval_expr_str res ectx rctx in (* evaluated res expr *)

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

  "let a = -5; x = 50; y = 60; b = 20;
    in a + b;" (* == *) "15"

let _ = test_eval_eqv_named
  "Let2"

  "c = 3; e = 1; f = 2; d = 4;"

  "let TrueProp = typecons TrueProp I;
       I = datacons TrueProp I;
       x = let a = 1; b = 2 in I
    in (case x | I => c) : Int;" (* == *) "3"

let _ = test_eval_eqv_named
  "Let3"

  "c = 3; e = 1; f = 2; d = 4;"

  "let TrueProp : Type;
       I : TrueProp;
       TrueProp = typecons TrueProp I;
       I = datacons TrueProp I;
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
   idt = typecons (idtd) (ctr0) (ctr1 idt) (ctr2 idt) (ctr3 idt);
                                     d = 10;
   ctr0 = datacons idt ctr0;   e = 20;
   ctr1 = datacons idt ctr1;   f = 30;
   ctr2 = datacons idt ctr2;   g = 40;
   ctr3 = datacons idt ctr3;   h = 50;

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
    Nat = typecons (dNat) (zero) (succ Nat);

    zero = datacons Nat zero;
    succ = datacons Nat succ;

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
   plus x y = case x
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

   inc1 = add 1;
   inc2 = _-_ 5;"

  "inc1 1; inc2 2; inc1 3;"

  "2; 3; 4"

(*
 *  Lists
 *)
let _ = test_eval_eqv_named
  "Lists"

  "my_list = cons 1
            (cons 2
            (cons 3
            (cons 4 nil)));
   List' = let L : Type -> Type;
               L = typecons (L (a : Type)) (nil) (cons a (L a))
           in L;
   cons' = datacons List' cons;
   nil' = datacons List' nil;
   my_list' = (cons' 1 nil');"

  "length my_list;
   head my_list;
   head (tail my_list)"

  "4; some 1; some 2"

(*
 *  Special forms
 *)
let _ = test_eval_eqv "w = 2" "decltype w" "Int"
let _ = test_eval_eqv "w = 2" "declexpr w" "2"

let attr_decl = "
  w = 2;
  greater-than = new-attribute (Int -> Int);
  greater-than = add-attribute greater-than w (lambda (x : Int) -> x);"

let _ = test_eval_eqv_named
  "has-attribute"

  attr_decl

  "has-attribute greater-than w;
   (get-attribute greater-than w) 3;"

  "true; 3"

let _ = (add_test "EVAL" "Monads" (fun () ->

    let dcode = "
      c = bind (open \"./_build/w_file.txt\" \"w\")
               (lambda f -> write f \"Hello2\");
    " in

    let rctx, ectx = eval_decl_str dcode ectx rctx in

    let rcode = "run-io c 2" in

    (* Eval defined lambda *)
    let ret = eval_expr_str rcode ectx rctx in
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
   f x = 2 + f (1 + x);
   %inf : ?;
   %inf x = inf (1 + x);
   test = 2;"

  "1" "1"

let _ = test_eval_eqv_named
  "Explicit field patterns"
  "Triplet = typecons Triplet
             (triplet (a ::: Int) (b :: Float) (c : String) (d :: Int));
   triplet = datacons Triplet triplet;
   t = triplet (b := 5.0) (a := 3) (d := 7) (c := \"hello\");"

  "case t | triplet (b := bf) cf => cf;
   case t | triplet (b := bf) _ => bf;
   case t | triplet (_ := bf) cf => cf;
   case t | triplet (_ := af) (_ := bf) (_ := cf) => bf;
   case t | triplet (_ := af) (_ := bf) (_ := cf) => cf;
   case t | triplet (_ := af) (_ := bf) (d := df) cf => df;
  "

  "\"hello\"; 5.0; \"hello\"; 5.0; \"hello\"; 7"

let _ = test_eval_eqv_named
  "Implicit Arguments"

  "default = new-attribute Macro;
   default = add-attribute default Int (Macro_ (lambda (lst : List Sexp) -> integer_ 1));

   fun = lambda (x : Int) =>
      lambda (y : Int) ->
        lambda (z : Int) -> x * y + z;"

  "fun 2 1;
   fun 2 1"

  "3; 3"

let _ = test_eval_eqv_named
  "Equalities"

  "f : (α : Type) ≡> (p : Eq (t := Type) Int α) -> Int -> α;
   f = lambda α ≡> lambda p x ->
       Eq_cast (t := Type) (x := Int) (y := α) (f := (lambda v -> v)) (p := p) x"

  "f Eq_refl 3"
  "3"

let _ = test_eval_eqv_named
  "Generic-typed case"

  "P = (a : Type) ≡> a -> Not (Not a);
   p : P;
   p = lambda a ≡> lambda x notx -> notx x;
   tP : Decidable P;
   tP = (datacons Decidable true) (prop := P) (p := p);"

  "case tP
   | (datacons ? true) (p := _) => 3
   | (datacons ? false) (p := _) => 4;"
  "3;"

let _ = test_eval_eqv_named
  "Y"

  "length_y = lambda t ≡>
     Y (a := List t) (witness := (lambda l -> 0))
       (lambda length l
        -> case l
           | nil => 0
           | cons _ l => 1 + length l);"

  "length_y (cons 1 (cons 5 nil));"

  "2;"

let _ = test_eval_eqv_named
  "Type Alias" "ListInt = List Int;" "" (* == *) ""

(* run all tests *)
let _ = run_all ()

