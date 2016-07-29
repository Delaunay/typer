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
  S.mkShift subst shift

let rec mkTestSubst lst =
  match lst with
  | (var, shift)::tail -> S.cons (mkVar var)
                                (mkShift2 shift (mkTestSubst tail))
  | [] -> S.identity

type result_type =
  | Ok
  | TransfoFail
  | InverseFail

(*TODO better checking of where it should fail*)
let input =
  ((mkTestSubst ((0, 3)::(2, 2)::(3, 5)::[])),         Ok)::
  ((mkTestSubst ((1, 3)::(2, 2)::(3, 5)::[])),         Ok)::
  ((mkTestSubst ((1, 3)::(2, 2)::(4, 5)::[])),         Ok)::
  ((mkTestSubst ((0, 3)::(2, 2)::(4, 5)::[])),         Ok)::
  ((mkTestSubst ((0, 3)::(1, 2)::(4, 5)::[])),         Ok)::
  ((mkTestSubst ((0, 3)::(1, 2)::(4, 1)::(5, 5)::[])), TransfoFail)::
  ((S.cons (mkVar 1) (S.shift 3)),                     Ok)::
  ((S.cons (mkVar 1) (S.cons (mkVar 3) (S.identity))), TransfoFail)::
  ((S.mkShift (S.shift 3) 4),                          Ok)::
  ((S.mkShift (S.cons (mkVar 1) (S.identity)) 5),      TransfoFail)::
  ((mkTestSubst ((4, 0)::(2, 2)::(3, 5)::[])),         Ok)::
  ((mkTestSubst ((1, 2)::(5, 1)::(3, 5)::[])),         Ok)::
  ((mkTestSubst ((1, 2)::(5, 2)::(3, 5)::[])),         InverseFail)::
  ((mkTestSubst ((0, 3)::(1, 2)::(4, 1)::(9, 5)::[])), TransfoFail)::
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
        ((padding_left (string_of_int (!idx)) 2 '0') ^ " - " ^ sub)
        (fun () -> if res then success () else failure ()))
    (test input_gen fmt tester)


let get_dim lst =
  let max i s = max i (String.length s)
  in
  List.fold_left
    (fun (acs, acsf, acs', acc) (s, sf, s', comp) -> ((max acs s), (max acsf sf), (max acs' s'), (max acc comp)))
    (0,0,0,0)
    lst

let fmt_res str =
  let (ds, dsf, ds', dcomp) = get_dim str
  in List.map (fun (s, sf, s', com) -> "[ " ^
                                       (padding_right s ds ' ') ^ " -> " ^
                                       (padding_right (sf ^ " ]") dsf ' ') ^ " ∘ " ^
                                       (padding_right s' ds' ' ') ^ " = " ^
                                       (com)
              ) str

(* let string_of_subst = ocaml_string_of_subst *)
(* let fmt_res str = *)
(* List.map (fun (_, sf, s', com) -> sf  ^ " ∘ " ^ s'  ^ " = " ^ com ) str *)

let get_dim lst =
  let max i s = max i (String.length s)
  in
  List.fold_left
    (fun (acs, acsf, acs', acc) (s, sf, s', comp) -> ((max acs s), (max acsf sf), (max acs' s'), (max acc comp)))
    (0,0,0,0)
    lst


let inverse = inverse2
let _ = generate_tests "INVERSION"
    (fun () -> input)
    fmt_res
    (fun (s, b) -> ( match inverse s, flatten s with
         | Some (s'), Some (sf) -> (let comp = scompose sf s' in
                                    let ret = (match (is_identity comp), b with
                                        | true, Ok -> true (*if we are here, the result of the composition should be Id*)
                                        | false, Ok -> false
                                        | _, _ -> false)
                                    in let str = ((string_of_subst s), (string_of_subst sf), (string_of_subst s'), (string_of_subst comp))
                                    in (str, ret))
         | Some (s'), None -> ((string_of_subst s, "None", string_of_subst s', "None"),(match b with
             | TransfoFail -> true
             | _ -> false))
         | None, Some(sf) -> ((string_of_subst s, string_of_subst sf, "None", "None"), (match b with
             | InverseFail -> true
             | _ -> false))
         | _ -> ((string_of_subst s, "None", "None", "None"), (match b with
             | Ok -> false
             | _ -> true)))
    )

let fmt_res str =
  List.map (fun (s, sf, s', com) -> "[ " ^
                                       (s) ^ " -> " ^
                                       ((sf ^ " ]")) ^ " ∘ " ^
                                       (s') ^ " = " ^
                                       (com)
              ) str

(* TODO find a better way to check test*)
let _ = generate_tests "INVERSION-RAND"
    (fun () -> generateRandInput 5 10)
    fmt_res
    (fun (s) -> ( match inverse s, flatten s with
         | Some (s'), Some (sf) -> (let comp = scompose sf s' in
                                    let ret = (is_identity comp)
                                    in let str = ((string_of_subst s), (string_of_subst sf), (string_of_subst s'), (string_of_subst comp))
                                    in (str, ret))
         | Some (s'), None -> ((string_of_subst s, "None", string_of_subst s', "None"),false)
         | None, Some(sf) -> ((string_of_subst s, string_of_subst sf, "None", "None"), false)
         | _ -> ((string_of_subst s, "None", "None", "None"), false)
    ))

let _ = generate_tests "TRANSFORMATION"
    (fun () -> input)
    (fun subst ->
       let padding_right s d c = "\n" ^ s ^ "\n"
       in let string_of_subst = pp_ocaml_string_of_subst
       in let subst = List.map (fun (s,fs) -> (string_of_subst s, string_of_subst fs)) subst
       in let get_dim lst =
            let max i s = max i (String.length s)
            in List.fold_left (fun (acs, acsf) (s, sf) -> ((max acs s), (max acsf sf))) (0,0) lst
       in let (ds, dsf) = get_dim subst
       in List.map (fun (s,sf) -> (padding_right s ds ' ') ^ " -> " ^ (padding_right sf dsf ' ')) subst)
    (fun (subst, b) -> match flatten subst, b with
       | Some(s), Ok -> ((subst, (s)), true)
       | Some(s), InverseFail -> ((subst, (s)), true)
       | None, TransfoFail -> ((subst, S.identity), true)
       | Some (s), _ -> ((subst, s), false)
       | None, _ -> ((subst, S.identity), false))

let _ = run_all ()
