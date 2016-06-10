
open Lexp

module VMap = Map.Make (struct type t = int let compare = compare end)

type substitution = lexp VMap.t
type constraints  = (lexp * lexp) list

let unify (lhs: lexp) (rhs: lexp) : ((subst * constraints) option) =
  let rec unify' (l: lexp) (r: lexp) (subst: substitution) : ((subst * constraints) option) =
    (* lexp, lexp -> OK
     * lexp, metavar -> unif
     * lexp, (metavar -> lexp) -> lexp == lexp
     * metavar, metavar -> ?*)
    (*TODO*)
    match (l, r) with
        (* Straightforward Imm case*)
      | (Imm (Integer (_, value)), Imm(Integer (_, value2))) ->
          if value = value2 then add_subst subst l r
          else None
      | (Imm (Float (_, value)), Imm(Float (_, value2))) ->
          if value = value2 then add_subst subst l r
          else None
      | (Imm (String (_, value)), Imm(String (_, value2))) ->
          if value = value2 then add_subst subst l r
          else None
  in unify' lhs rhs () (* <- Construct empty VMap.t*)
