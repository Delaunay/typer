
open Lexp

module VMap = Map.Make (struct type t = int let compare = compare end)

type substitution = lexp VMap.t
type constraints  = (lexp * lexp) list
(* IMPROVEMENT For error handling : can carry location and name of type error *)
type a' expected =
  | Some of 'a
  | Error of location * string (*location * type name*)
  | None

(* For convenience *)
type return_type = (substitution * constraints) option

(**
 * Imm       , Imm                -> if Imm =/= Imm then ERROR else ??
 * Cons      , Cons               -> ERROR
 * Builtin   , Builtin            -> if Builtin =/= Builtin then error else UNIFY ?
 * Let       , lexp               -> try UNIFY
 * Var       , lexp               -> try UNIFY
 * Arrow     , lexp               -> try UNIFY
 * Call      , lexp               -> try UNIFY
 * Inductive , lexp               -> ????
 * Case      , case               -> ??
 * lexp      , {metavar <-> none} -> UNIFY
 * lexp      , {metavar <-> lexp} -> if lexp ~= lexp then UNIFY else ERROR
 * metavar   , metavar            -> ?
 * lexp      , lexp               -> ERROR
 * Sort(Level) ??
 *)
(*Maybe transform the result to return_type only at the end of the function ?*)
let rec unify (l: lexp) (r: lexp) (subst: substitution) : return_type =
    (* Dispatch to the right unifyer*)
    match (l, r) with
      | (Imm, Imm)   -> _unify_imm l r subst
      | (Builtin, _) -> _unify_builtin l r subst
      | (Let, _)     -> _unify_let l r subst
      | (Cons, Cons) -> None (*Useless ??*)
      | (_, _)       -> None

(** Add one of the Imm (the first arguement) to the substitution *)
let _unify_imm (l: lexp) (r: lexp) (subst: substitution) : return_type =
  match (l, r) with
    | (Imm (String (_, v1)), Imm (String (_, v2))
       -> if v1 = v2 then (add_substitution l subst, ())
       else None
    | (Imm (Integer (_, v1)), Imm (Integer (_, v2))
       -> if v1 = v2 then (add_substitution l subst, ())
       else None
    | (Imm (Float (_, v1)), Imm (Float (_, v2))
       -> if v1 = v2 then (add_substitution l subst, ())
       else None
    | (Imm (Node (_, v1)), Imm (Node (_, v2))
       -> if v1 = v2 then (add_substitution l subst, ())
       else None
    | (_, _) -> None

let _unify_builtin (l: lexp) (r: lexp) (subst: substitution) : return_type =
  match (l, r) with
    | (Builtin ((_, name1), _), Builtin ((_, name2),_))
      -> if name1 = name2 then (add_substitution l subst, ())
      else None (* assuming that builtin have unique name *)
    | (Builtin (_, lxp), _) -> unify lxp r subst
    | (_, _) -> None

let _unify_let (l: lexp) (r: lexp) (subst: substitution) : return_type = (*TODO*)

(** Generate the next metavar by assuming that the key goes from
 * one to X, so the next metavar is `(lenght subst) + 1`*)
(*FIXME : find a better solution to have the size of the map :
 * - have the map carry its size with it
 *            -> 'private function' that handle this kind of map
 * - global last_idx :-( *)
let add_substitution (lxp: lexp) (subst: substitution) : substitution =
  let last_idx = VMap.fold (fun _ acc -> acc + 1) subst 1
  in VMap.add last_idx lxp subst
