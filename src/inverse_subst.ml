
open Lexp
module S = Subst

(* type s_list = *)
  (* | Node of lexp S.subst * s_list (* Cons(a_i, ↑^x) * (...) *) *)
  (* | Identity *)

type inter_subst = lexp S.subst list (* Intermediate between "tree"-like substitution and fully flattened subsitution *)

let rec flatten_s (s: lexp S.subst) : inter_subst =
    match s with
    | S.Shift (s_1, offset)    -> let var, s_2 = flatten_cons s_1 in
      (S.Cons (var, S.Shift(S.Identity, offset)))::(s_2)
    | S.Identity               -> [S.Identity]
    | _                        -> [S.Identity] (*To make the compiler happy : delete after*)

and flatten_cons (s: lexp S.subst) : (lexp * inter_subst) =
  match s with
  | S.Cons (Var _ as v, s_1) -> (v, flatten_s s_1)
  (* Otherwise : fail *)

(** s:S.subst -> l:lexp -> s':S.subst where l[s][s'] = l *)
let rec inverse (subst: lexp S.subst ) : lexp S.subst option = None

