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

open Fmt_lexp
open Debug_fun

let mkShift2 shift subst =
  S.Shift (subst, shift)

let rec mkTestSubst lst =
  match lst with
  | (var, shift)::tail -> S.Cons (mkVar var,
                                  mkShift2 shift (mkTestSubst tail))
  | [] -> S.Identity

let input =
  (mkTestSubst ((0, 3)::(2, 2)::(3, 0)::[])):: (* Seems to work *)
  (mkTestSubst ((1, 3)::(2, 2)::(3, 0)::[])):: (* Seems to work *)
  (mkTestSubst ((4, 2)::(2, 2)::(3, 0)::[])):: (* Go completly wrong -> indices not in order -> should fail ?*)
  (mkTestSubst ((1, 3)::(2, 2)::(4, 0)::[])):: (* Seems to work *)
  (mkTestSubst ((0, 3)::(2, 2)::(4, 0)::[])):: (* Seems to work *)
  (mkTestSubst ((0, 3)::(1, 2)::(4, 0)::[])):: (* Seems to work *)
  (mkTestSubst ((0, 3)::(1, 2)::(4, 1)::(5, 0)::[]))::
  (mkTestSubst ((0, 3)::(1, 2)::(4, 1)::(5, 0)::[]))::
  (S.Cons (mkVar 1, S.Shift(S.Identity, 3)))::
  []

let lxp = mkVar 3

let inputs = List.map (fun s ->
    match inverse s, flatten s with
    | Some(s'), Some(sf) -> (let lxp_inv = mkSusp lxp s'
                   in let ret = (match unify lxp lxp_inv empty_subst with
                       | Some (_) -> true
                       | _ -> false)
                   in let str = (string_of_subst sf) ^ (String.make (50 - String.length (string_of_subst sf)) ' ')
                                                     ^  " -> " ^ (string_of_subst s')
                   in (ret, str))
    | _ -> (false, ((string_of_subst s) ^ " -> Non inversable")))
    input

let _ = List.map (fun (res, str) -> add_test "INVERSE" str (fun () -> if res then success () else failure ()))
    inputs

let _ = run_all ()
