
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
 * Builtin   , lexp               -> try UNIFY lexp of Builtin with lexp (???)
 * Let       , lexp               -> try UNIFY (???)
 * Var       , Var                -> if db_index ~= db_index UNIFY else ERROR
 * Var       , MetaVar            -> UNIFY Metavar
 * Var       , lexp               -> ???
 * Arrow     , lexp               -> try UNIFY
 * Call      , lexp               -> try UNIFY
 * Inductive , lexp               -> ????
 * Case      , case               -> ??
 * lexp      , {metavar <-> none} -> UNIFY
 * lexp      , {metavar <-> lexp} -> if lexp ~= lexp then UNIFY else ERROR
 * metavar   , metavar            -> ?
 * lexp      , lexp               -> ERROR
 * Sort(Level) ??

 * lexp mean that that it ca be any lexp
 * (Let , lexp) == (lexp , Let)
*)
(*Maybe transform the result to return_type only at the end of the function ?*)
(*l & r commutative ?*)
let rec unify (l: lexp) (r: lexp) (subst: substitution) : return_type =
  (* Dispatch to the right unifyer*)
  match (l, r) with
  | (Imm, Imm)   -> _unify_imm l r subst
  | (Builtin, _) -> _unify_builtin l r subst
  | (_, Builtin) -> _unify_builtin r l subst
  | (Let, _)     -> _unify_let l r subst
  | (_, Let)     -> _unify_let r l subst
  | (Var, _)     -> _unify_var l r subst (*TODO : work in progress*)
  | (_, Var)     -> _unify_var r l subst (*TODO : work in progress*)
  | (Arrow, _)   -> _unify_arrow l r subst
  | (_, Arrow)   -> _unify_arrow r l subst
  | (Cons, Cons) -> None (*Useless ??*)
  | (_, _)       -> None

let rec _unify_arrow (arrow: lexp) (lxp: lexp) (subst: substitution)
  : return_type =
  match (arrow, lxp) with
  (*?????*)
  | (Arrow (_, _, ltype1, lexp1), Arrow (_, _, ltype2, lexp2))
    -> if var_kind1 = var_kind2
    then _unify_inner_arrow ltype1 lexp1 ltype2 lexp2
    else None
  (*| *)
  | (_, _) -> None

let _unify_inner_arrow (lxp1: lexp) (lt1: lexp)
    (lxp2: lexp) (lt2: lexp) : return_type =
  match unify lt1 lt2 subst with
  | Some (subst_, const) -> (
      match unify lxp1 lxp2 subst_ with
      | Some (s, c) -> Some(s, const@c)
      | None -> None )
  | None -> None

(*TODO : shift db_index*)
let _unify_var (l: lexp) (r: lexp) (subst: substitution) : return_type =
  match (l, r) with
  | (Var (_, idx1), Var (_, idx2))
    -> if idx1 = idx2 then (add_substitution l subst, ())
    else None
  | (Var, Metavar) -> _unify_metavar r l subst
  (*| (Var, _) -> ???(*TODO*)*)
  | (_, _)   -> None

(** Unify two Imm if they match *)
(* Add one of the Imm (the first arguement) to the substitution *)
let _unify_imm (l: lexp) (r: lexp) (subst: substitution) : return_type =
  match (l, r) with
  | (Imm (String (_, v1)), Imm (String (_, v2)))
    -> if v1 = v2 then (add_substitution l subst, ())
    else None
  | (Imm (Integer (_, v1)), Imm (Integer (_, v2)))
    -> if v1 = v2 then (add_substitution l subst, ())
    else None
  | (Imm (Float (_, v1)), Imm (Float (_, v2)))
    -> if v1 = v2 then (add_substitution l subst, ())
    else None
  | (_, _) -> None

(** Unify a builtin (bltin) and a lexp (lxp) if it is possible
 * If the two arguments are builtin, unify based on name
 * If it's a Builtin and an other lexp, unify lexp part of Builtin with the lexp
*)
let _unify_builtin (bltin: lexp) (lxp: lexp) (subst: substitution) : return_type =
  match (bltin, lxp) with
  | (Builtin ((_, name1), _), Builtin ((_, name2),_))
    -> if name1 = name2 then (add_substitution l subst, ())
    else None (* assuming that builtin have unique name *)
  | (Builtin (_, lxp_), _) -> unify lxp lxp subst
  | (_, _) -> None

(** Unify a Let (let_) and a lexp (lxp), if possible
 * Unify the lexp pat of the Let with the lexp
*)
let _unify_let (let_: lexp) (lxp: lexp) (subst: substitution) : return_type =
  match let_ with (* Discard the middle part of Let : right behavior ? *)
  | Let (_, _, lxp_) -> unify lxp_ lxp subst
  | _ -> None

(** Generate the next metavar by assuming that the key goes from
 * one to X, so the next metavar is `(lenght subst) + 1`*)
(*FIXME : find a better solution to have the size of the map :
 * - have the map carry its size with it
 *            -> 'private function' that handle this kind of map
 * - global last_idx :-( *)
let add_substitution (lxp: lexp) (subst: substitution) : substitution =
  let last_idx = VMap.fold (fun _ acc -> acc + 1) subst 1
  in VMap.add last_idx lxp subst

let find_or_none (value: lexp) (map: substitution) : lexp option =
  match value with
  | Metavar idx -> if VMap.mem idx map
    then Some (VMap.find idx map)
    else None
  | _ -> None

