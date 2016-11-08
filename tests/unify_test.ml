
open Sexp
open Pexp
open Lexp
open Unification

open Lparse     (* add_def       *)

open Utest_lib

open Fmt

open Builtin
open Env

open Str

open Debug

type result =
  | Constraint
  | Unification
  | Equivalent
  | Nothing

type unif_res = (result * (substitution * constraints) option * lexp * lexp)

type triplet = string * string * string

let string_of_result r =
  match r with
  | Constraint  -> "Constraint"
  | Unification -> "Unification"
  | Equivalent  -> "Equivalent"
  | Nothing     -> "Nothing"

let max_dim (lst: (string * string * string * string) list): (int * int * int *int) =
  let max i l = max i (String.length l)
  in List.fold_left
    (fun (la, ca1, ca2, ra) (l, c1, c2, r) -> ((max la l), (max ca1 c1), (max ca2 c2), (max ra r)))
    (0, 0, 0, 0)
    lst

let fmt (lst: (lexp * lexp * result * result) list): string list =
  let str_lst = List.map
      (fun (l1, l2, r1, r2) -> ((lexp_string l1), (lexp_string l2), (string_of_result r1), (string_of_result r2)))
      lst
  in let l, c1, c2, r = max_dim str_lst
  in List.map (fun (l1, l2, r1, r2) -> (U.padding_right l1 l ' ')
                                       ^ ", "
                                       ^ (U.padding_right l2 c1 ' ')
                                       ^ " -> got: "
                                       ^ (U.padding_right r2 r ' ')
                                       ^ " expected: "
                                       ^ (U.padding_right r1 c2 ' ')
              ) str_lst

(* Inputs for the test *)
let str_induct = "Nat : Type; Nat = inductive_ (dNat) (zero) (succ Nat)"
let str_int_3  = "i = 3"
let str_int_4  = "i = 4"
let str_case   = "i = case True
| True => 2
| False => 42"
let str_case2 = "i = case nil(a := Int)
| nil => 12
| _ => 24"
let str_let = "i = let a = 5 in a + 1"
let str_let2 = "j = let b = 5 in b"
let str_lambda = "sqr = lambda (x : Int) -> x * x;"
let str_lambda2 = "sqr = lambda (x : Int) -> x * x;"
let str_lambda3 = "sqr = lambda (x : Int) -> lambda (y : Int) -> x * y;"
let str_type = "i = let j = decltype(Type) in decltype(j);"
let str_type2 = "j = let i = Int -> Int in decltype(i);"

let generate_ltype_from_str str =
  List.hd ((fun (lst, _) ->
      (List.map
         (fun (_, _, ltype) -> ltype))
        (List.flatten lst))
       (lexp_decl_str str default_lctx))

let generate_lexp_from_str str =
  List.hd ((fun (lst, _) ->
      (List.map
         (fun (_, lxp, _) -> lxp))
        (List.flatten lst))
       (lexp_decl_str str default_lctx))

let input_induct  = generate_lexp_from_str str_induct
let input_int_4   = generate_lexp_from_str str_int_4
let input_int_3   = generate_lexp_from_str str_int_3
let input_case    = generate_lexp_from_str str_case
let input_case2   = generate_lexp_from_str str_case2
let input_let     = generate_lexp_from_str str_let
let input_let2    = generate_lexp_from_str str_let
let input_lambda  = generate_lexp_from_str str_lambda
let input_lambda2 = generate_lexp_from_str str_lambda2
let input_lambda3 = generate_lexp_from_str str_lambda3
let input_arrow   = generate_ltype_from_str str_lambda
let input_arrow2  = generate_ltype_from_str str_lambda2
let input_arrow3  = generate_ltype_from_str str_lambda3
let input_type    = generate_ltype_from_str str_type
let input_type_t  = generate_ltype_from_str str_type2

let generate_testable (_: lexp list) : ((lexp * lexp * result) list) =

  ( Lambda ((Aexplicit),
              (Util.dummy_location, "L1"),
              Var((Util.dummy_location, "z"), 3),
              Imm (Integer (Util.dummy_location, 3))),
      Lambda ((Aexplicit),
              (Util.dummy_location, "L2"),
              Var((Util.dummy_location, "z"), 4),
              Imm (Integer (Util.dummy_location, 3))), Nothing )

  ::(input_induct  , input_induct  , Equivalent)  (* 2 *)
  ::(input_int_4   , input_int_4   , Equivalent)  (* 3 *)
  ::(input_int_3   , input_int_4   , Nothing)     (* 4 *)
  ::(input_case    , input_int_4   , Constraint)  (* 5 *)
  ::(input_case    , input_induct  , Constraint)  (* 6 *)
  ::(input_case    , input_case    , Equivalent)  (* 7 *)
  ::(input_case    , input_case2   , Nothing)     (* 8 *)

  ::(input_let     , input_induct  , Constraint)  (* 9 *)
  ::(input_let     , input_int_4   , Constraint)  (* 10 *)
  ::(input_let     , input_case    , Constraint)  (* 11 *)
  ::(input_let     , input_let     , Equivalent)  (* 12 *)
  ::(input_let2    , input_let     , Equivalent)  (* 13 *)
  ::(input_let2    , input_let2    , Equivalent)  (* 14 *)

  ::(input_lambda  , input_int_4   , Nothing)     (* 15 *)
  ::(input_lambda  , input_induct  , Nothing)     (* 16 *)
  ::(input_lambda  , input_case    , Constraint)  (* 17 *)
  ::(input_lambda  , input_case2   , Constraint)  (* 18 *)
  ::(input_lambda  , input_let     , Constraint)  (* 19 *)
  ::(input_lambda  , input_induct  , Nothing)     (* 20 *)
  ::(input_lambda  , input_lambda  , Equivalent)  (* 21 *)

  ::(input_lambda2 , input_int_4   , Nothing)     (* 22 *)
  ::(input_lambda2 , input_induct  , Nothing)     (* 23 *)
  ::(input_lambda2 , input_case    , Constraint)  (* 24 *)
  ::(input_lambda2 , input_case2   , Constraint)  (* 25 *)
  ::(input_lambda2 , input_let     , Constraint)  (* 26 *)
  ::(input_lambda2 , input_induct  , Nothing)     (* 27 *)
  ::(input_lambda2 , input_lambda  , Equivalent)  (* 28 *)
  ::(input_lambda2 , input_lambda2 , Equivalent)  (* 29 *)
  ::(input_lambda2 , input_lambda3 , Constraint)  (* 30 *)
  ::(input_lambda3 , input_lambda3 , Equivalent)  (* 31 *)

  ::(input_arrow2  , input_int_4   , Unification) (* 32 *)
  ::(input_arrow2  , input_induct  , Unification) (* 33 *)
  ::(input_arrow2  , input_case    , Constraint)  (* 34 *)
  ::(input_arrow2  , input_case2   , Constraint)  (* 35 *)
  ::(input_arrow2  , input_let     , Constraint)  (* 36 *)
  ::(input_arrow2  , input_induct  , Unification) (* 37 *)
  ::(input_arrow2  , input_lambda  , Unification) (* 38 *)
  ::(input_arrow2  , input_lambda2 , Unification) (* 39 *)
  ::(input_arrow2  , input_arrow3  , Unification) (* 40 *)
  ::(input_arrow3  , input_arrow   , Unification) (* 41 *)
  ::(input_arrow2  , input_arrow   , Unification) (* 42 *)
  ::(input_arrow3  , input_arrow3  , Equivalent)  (* 43 *)

  ::(input_type    , input_type_t  , Equivalent)  (* 44 *)

  ::(Metavar (0, S.Identity, (Util.dummy_location, "M"), type0),
     Var ((Util.dummy_location, "x"), 3), Unification) (* 45 *)

  ::[]

let test_input (lxp1: lexp) (lxp2: lexp) (subst: substitution): unif_res =
  let res = unify lxp1 lxp2 Myers.nil subst in
  let tmp = match res with
  | Some (s, []) when s = empty_subst -> (Equivalent, res, lxp1, lxp2)
  | Some (_, [])                      -> (Unification, res, lxp1, lxp2)
  | Some _                            -> (Constraint, res, lxp1, lxp2)
  | None                              -> (Nothing, res, lxp1, lxp2)
  in tmp

let check (lxp1: lexp) (lxp2: lexp) (res: result) (subst: substitution): bool =
  let r, _, _, _ = test_input lxp1 lxp2 subst
  in if r = res then true else false

let test_if (input: lexp list) sample_generator checker : bool =
  let rec test_if_ samples checker =
    match samples with
    | (l1, l2, res)::t -> if checker l1 l2 res empty_subst then test_if_ t checker else false
    | [] -> true
  in test_if_ (sample_generator input) checker

let unifications = List.map
    (fun (l1, l2, res) ->
       let r, _, _, _ = test_input l1 l2 empty_subst
       in (l1, l2, res, r))
    (generate_testable [])

let idx = ref 0
let _ = List.map
    (fun (str, (l1, l2, expected, res)) ->
       idx := !idx + 1;
       add_test "UNIFICATION"
         ((if !idx < 10 then "0" else "") ^ (string_of_int !idx) ^ " " ^ str )
         (fun () -> if expected = res then success () else failure ()))
    (List.combine (fmt unifications) unifications )

let _ = run_all ()


