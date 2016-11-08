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
    | S.Shift(S.Identity, shift)             -> (acc = shift)
    | S.Identity                             -> true
    | _                                      -> false
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
    then (mkTestSubst (generateRandInput shiftMax 0 0))::(generateList shiftMax (numberOfTest - 1))
    else []
  in generateList shiftMax numberOfTest

let lxp = mkVar 3

let test
    (input_gen: (unit -> 'a list))
    (fmt: 'b list -> string list)
    (tester: 'a -> ('b * bool)): (string * bool) list =
  let input = List.map tester (input_gen ())
  in let str = List.map (fun (s, _) -> s ) input
  in let b = List.map (fun (_, b) -> b) input
  in List.combine (fmt str) b

let generate_tests (name: string)
    (input_gen: (unit -> 'a list))
    (fmt: 'b list -> string list)
    (tester: 'a -> ('b * bool)) =
  let idx = (ref 0)
  in List.map (fun (sub, res) ->
      idx := !idx + 1;
      add_test name
        ((U.padding_left (string_of_int (!idx)) 2 '0') ^ " - " ^ sub)
        (fun () -> if res then success () else failure ()))
    (test input_gen fmt tester)


let get_dim lst =
  let max i s = max i (String.length s)
  in
  List.fold_left
    (fun (acs, acs', acc) (s, s', comp) -> ((max acs s), (max acs' s'), (max acc comp)))
    (0,0,0)
    lst

let fmt_res str =
  let (ds, ds', dcomp) = get_dim str
  in List.map (fun (s, s', com) -> (U.padding_right s ds ' ') ^ " -> "
                                ^ (U.padding_right s' ds' ' ') ^ " = "
                                ^ com)
              str

let get_dim lst =
  let max i s = max i (String.length s)
  in
  List.fold_left
    (fun (acs, acs', acc) (s, s', comp) -> ((max acs s), (max acs' s'), (max acc comp)))
    (0,0,0)
    lst


let _ = generate_tests "INVERSION"
    (fun () -> input)
    fmt_res
    (fun (s, b) -> ( match inverse s with
         | Some (s') -> (let comp = scompose s s' in
                        let ret = (is_identity comp) in
                        let str = (subst_string s, subst_string s',
                                   subst_string comp) in
                        (str, ret))
         | None      -> ((subst_string s, "None", "None"), not b)
       )
    )

let fmt_res str =
  List.map (fun (s, s', com) -> (s) ^ " -> " ^
                                (s') ^ " = " ^
                                (com) ) str

(* TODO find a better way to check test*)
let _ = generate_tests "INVERSION-RAND"
    (fun () -> generateRandInput 5 10)
    fmt_res
    (fun (s) -> ( match inverse s with
         | Some (s') -> (let comp = scompose s s' in
                        let ret = (is_identity comp) in
                        let str = (subst_string s,
                                   subst_string s',
                                   subst_string comp) in
                        (str, ret))
         | None      -> ((subst_string s , "None"             , "None") , false)
    ))

let _ = run_all ()
