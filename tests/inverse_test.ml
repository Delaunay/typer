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

let input =
  (S.Cons (mkVar 3,
           mkShift2 3 (S.Cons (mkVar 2,
                               (mkShift2 2 (S.Cons (mkVar 1,
                                                    mkShift2 1 S.Identity)
                                           )
                               )
                              )
                      )
          )
  )::
  (S.Cons (mkVar 0, S.Shift(S.Identity, 3)))::
  []

let rec string_of_subst s =
  match s with
  | S.Cons (Var(_, idx), s2) -> "a" ^ string_of_int idx ^ " · " ^ string_of_subst s2
  | S.Cons (l, s2)           -> string_of_lxp l ^ " · " ^ string_of_subst s2
  | S.Shift (s2, shift)      -> string_of_subst s2 ^ " · ↑^" ^ string_of_int shift
  | S.Identity               -> "Id"

let lxp = mkVar 3

let _ = List.map (fun s ->
    match inverse s with
    | Some(s') -> (let lxp_inv = mkSusp lxp s'
                   in add_test "INVERSE" (((string_of_subst s) ^ " -> " ^ (string_of_subst s')))
                     (fun () -> if lxp = lxp_inv then success () else failure ()))
    | None -> add_test "INVERSE" ((string_of_subst s) ^ " -> Non inversable") (fun () -> failure ()))
    input

let _ = run_all ()
