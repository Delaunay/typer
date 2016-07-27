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
  ((S.Cons (mkVar 1, S.Shift(S.Identity, 3))),         Ok)::
  ((S.Cons (mkVar 1, S.Cons (mkVar 3, S.Identity))),   TransfoFail)::
  ((S.Shift (S.Shift (S.Identity, 3), 4)),             Ok)::
  ((S.Shift (S.Cons (mkVar 1, S.Identity), 5)),        TransfoFail)::
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
  in match s with
  | S.Shift(S.Identity, _) -> true
  | S.Identity             -> true
  | _                      -> is_identity s 0

let generateRandInput n m =
  Random.self_init ();
  let rec generateList n m =
    let rec generateRandInput n i =
      if n > i
      then (if Random.bool ()
            then ( let r = Random.int n in
                   (i, (min (r + i) n))::(generateRandInput n (i + 1)) )
            else generateRandInput n (i + 1))
      else []
    in if m >= 0
    then (mkTestSubst (generateRandInput n 0))::(generateList n (m - 1))
    else []
  in generateList n m

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

let _ = generate_tests "INVERSION"
    (fun () -> input)
    fmt_res
    (fun s -> ( match inverse s, flatten s with
         | Some (s'), Some (sf) -> (let comp = scompose sf s' in
                                    let ret = (match comp with
                                        | S.Identity -> true
                                        | _          -> false)
                                    in let str = ((string_of_subst s), (string_of_subst sf), (string_of_subst s'), (string_of_subst comp))
                                    in (str, ret))
         | Some (s'), None -> ((string_of_subst s, "None", string_of_subst s', "None"),
                 false )
         | None, Some(sf) -> ((string_of_subst s, string_of_subst sf, "None", "None"),
                 false )
         | _ -> ((string_of_subst s, "None", "None", "None"),
                 false ))
    )

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
    (fun subst -> match flatten subst with
       |Some s -> ((subst, (s)), true)
       | None -> ((subst, S.Identity), false))

let _ = run_all ()
