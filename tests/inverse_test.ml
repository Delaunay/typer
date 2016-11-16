(* inverse_test.ml --- Test the substitution-inversion algorithm
 *
 *      Copyright (C) 2016  Free Software Foundation, Inc.
 *
 *   Author: Vincent Bonnevalle <tiv.crb@gmail.com>
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
 * -------------------------------------------------------------------------- *)

open Sexp
open Pexp
open Lexp
open Unification
open Inverse_subst

open Lparse     (* add_def       *)

open Utest_lib

open Fmt

open Builtin
open Env

open Str

open Debug

let mkShift2 shift subst =
  S.mkShift subst shift

let rec mkTestSubst lst =
  match lst with
  | (var, shift)::tail -> S.cons (mkVar var)
                                (mkShift2 shift (mkTestSubst tail))
  | [] -> S.identity

(*TODO better checking of where it should fail*)
let input =
  ((mkTestSubst ((0, 3)::(2, 2)::(3, 5)::[])),         true)::
  ((mkTestSubst ((1, 3)::(2, 2)::(3, 5)::[])),         true)::
  ((mkTestSubst ((1, 3)::(2, 2)::(4, 5)::[])),         true)::
  ((mkTestSubst ((0, 3)::(2, 2)::(4, 5)::[])),         true)::
  ((mkTestSubst ((0, 3)::(1, 2)::(4, 5)::[])),         true)::
  ((mkTestSubst ((0, 3)::(1, 2)::(4, 1)::(5, 5)::[])), false)::
  ((S.cons (mkVar 1) (S.shift 3)),                     true)::
  ((S.cons (mkVar 1) (S.cons (mkVar 3) (S.identity))), false)::
  ((S.mkShift (S.shift 3) 4),                          true)::
  ((S.mkShift (S.cons (mkVar 1) (S.identity)) 5),      false)::
  ((mkTestSubst ((4, 0)::(2, 2)::(3, 5)::[])),         true)::
  ((mkTestSubst ((1, 2)::(5, 1)::(3, 5)::[])),         true)::
  ((mkTestSubst ((1, 2)::(5, 2)::(3, 5)::[])),         false)::
  ((mkTestSubst ((0, 3)::(1, 2)::(4, 1)::(9, 5)::[])), false)::
  []

let is_identity s =
  let rec is_identity s acc =
    match s with
    | S.Cons(Var(_, idx), s1) when idx = acc -> is_identity s1 (acc + 1)
    | S.Shift(S.Identity, shift)             -> acc = shift
    | _                                      -> S.identity_p s
  in is_identity s 0

let generateRandInput shiftMax numberOfTest =
  Random.self_init ();
  let rec generateList shiftMax numberOfTest =
    let rec generateRandInput shiftMax idx acc =
      if idx < shiftMax
      then (if Random.bool ()
            then ( let r = Random.int shiftMax in
                   let shift = (min (r + idx + 1) (shiftMax))
                   in let shift = shift + (max 0 ((idx + shift) - acc))
                   in (idx, shift)::(generateRandInput shiftMax (idx + 1) (shift + acc)) )
            else generateRandInput shiftMax (idx + 1) acc)
      else []
    in if numberOfTest >= 0
       then (mkTestSubst (generateRandInput shiftMax 0 0), true)
            ::(generateList shiftMax (numberOfTest - 1))
       else []
  in generateList shiftMax numberOfTest

let inv_add_test name inputs =
  add_test "INVERSION" name
           (fun ()
            -> if List.fold_left (fun res (s,b)
                                 -> match inverse s with
                                   | Some s'
                                     -> let comp = scompose s s' in
                                       res && (if is_identity comp
                                              then b else not b)
                                   | None -> (not b))
                                true inputs
              then success () else failure ())

let _ = inv_add_test "Manual" input

(* TODO find a better way to check test*)
let _ = inv_add_test "Random" (generateRandInput 5 10)

let _ = run_all ()
