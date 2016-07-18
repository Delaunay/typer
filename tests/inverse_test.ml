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
  (S.Cons (mkVar 0,
           mkShift2 3 (S.Cons (mkVar 2,
                               (mkShift2 2 (S.Cons (mkVar 3,
                                                    mkShift2 0 S.Identity)
                                           )
                               )
                              )
                      )
          )
  )::
  (S.Cons (mkVar 1, S.Shift(S.Identity, 3)))::
  []

let lxp = mkVar 3

(* let _ = List.iter (fun i -> *)
    (* match (flatten i) with *)
    (* | Some (i') -> *)
      (* print_string (str_red (string_of_subst i)); *)
      (* print_string " -- flatten --> "; *)
      (* print_string (str_magenta (string_of_subst i')); *)
      (* print_newline () *)
    (* | None -> print_string "None"; print_newline ()) *)
    (* input *)

let inputs = List.map (fun s ->
    match inverse s with
    | Some(s') -> (let lxp_inv = mkSusp lxp s'
                   in let ret = (match unify lxp lxp_inv empty_subst with
                       | Some (_) -> true
                       | _ -> false)
                   in let str = (string_of_subst s) ^ " -> " ^ (string_of_subst s')
                   in (ret, str))
    | None -> (false, ((string_of_subst s) ^ " -> Non inversable")))
    input

let _ = List.map (fun (res, str) -> add_test "INVERSE" str (fun () -> if res then success () else failure ()))
    inputs

let _ = run_all ()
