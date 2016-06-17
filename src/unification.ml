
open Lexp
open Sexp

module VMap = Map.Make (struct type t = int let compare = compare end)

type substitution = lexp VMap.t * int
type constraints  = (lexp * lexp) list
(* IMPROVEMENT For error handling : can carry location and name of type error *)
type 'a expected =
  | Some of 'a
  | Error of Util.location * string (*location * type name*)
  | None

(* For convenience *)
type return_type = (substitution * constraints) option


(** Alias for VMap.add*)
let associate (meta: int) (lxp: lexp) ((subst, max_): substitution)
  : substitution =
  (VMap.add meta lxp subst, (max max_ meta ))

(** Generate the next metavar by taking the highest value and
 * adding it one
 *)
let add_substitution (lxp: lexp) ((subst, max_): substitution) : substitution =
  associate (max_ + 1) lxp (subst, max_)

(** If key is in map returns the value associated
 * else returns None
 *)
let find_or_none (value: lexp) ((map, max_): substitution) : lexp option =
  match value with
  | Metavar (idx, _, _) -> (if max_ < idx (* 0 < keys <= max_ *)
                    then None
                    else (if VMap.mem idx map
                           then Some (VMap.find idx map)
                           else None))
  | _ -> None

let empty_subst = (VMap.empty, 0)

(**
 * Imm       , Imm                -> if Imm =/= Imm then ERROR else OK

 * Cons      , Cons               -> ERROR

 * Builtin   , Builtin            -> if Builtin =/= Buitin
                                     then ERROR else OK
 * Builtin   , lexp               -> UNIFY lexp of Builtin with lexp

 * Let       , lexp               -> UNIFY right part of Let with lexp

 * Var       , Var                -> if db_index ~= db_index UNIFY else ERROR
 * Var       , MetaVar            -> UNIFY Metavar
 * Var       , lexp               -> ERROR

 * Arrow     , Arrow              -> if var_kind = var_kind
                                     then UNIFY ltype & lexp else ERROR
 * Arrow     , lexp               -> ERROR

 * lexp      , {metavar <-> none} -> UNIFY
 * lexp      , {metavar <-> lexp} -> UNFIFY lexp subst[metavar]
 * metavar   , metavar            -> if Metavar = Metavar then OK else ERROR
 * metavar   , lexp               -> ERROR

 * Lamda     , Lambda             -> if var_kind = var_kind
                                     then unify ltype & lxp else ERROR
 * Lambda    , Var                -> constraints
 * Lambda    , lexp               -> ERROR
 * Call      , Imm                -> CONSTRAINT
 * Call      , Cons               -> ERROR
 * Call      , Buitin             -> ERROR
 * Call      , Var                -> CONSTRAINT
 * Call      , Let                -> ERROR
 * Call      , Arrow              -> ERROR
 * Call      , Call               -> CONSTRAINT

   (*TODO*)
 * Inductive , lexp               ->
 * Case      , case               ->
 * lexp      , lexp               ->

 * lexp is equivalent to _ in ocaml
 * (Let , lexp) == (lexp , Let)
 * UNIFY -> recursive call or dispatching
 * OK -> add a substituion to the list of substitution
*)

(** Dispatch to the right unifyer.
 * If (_unify_X X Y) don't handle the case (X, Y), it call (unify Y X)
 * The metavar unifyer is the end rule, it can't call unify with it's parameter (changing their order)
 *)
let rec unify (l: lexp) (r: lexp) (subst: substitution) : return_type =
  match (l, r) with
  | (Imm _, _)       -> _unify_imm      l r subst
  | (Cons _, Cons _) -> None
  | (Builtin _, _)   -> _unify_builtin  l r subst
  | (Let _, _)       -> _unify_let      l r subst
  | (Var _, _)       -> _unify_var      l r subst
  | (Arrow _, _)     -> _unify_arrow    l r subst
  | (Lambda _, _)    -> _unify_lambda   l r subst
  | (Metavar _, _)   -> _unify_metavar  l r subst
  | (Call _, _)      -> _unify_call     l r subst
  | (_, _)           -> None

and _unify_call (call: lexp) (lxp: lexp) (subst: substitution) : return_type =
  match (call, lxp) with
  | (Call _, Imm _)     -> Some ((subst, [(call, lxp)]))
  | (Call _, Cons _)    -> None
  | (Call _, Builtin _) -> None
  | (Call _, Var _)     -> Some ((subst, [(call, lxp)]))
  | (Call _, Let _)     -> None (*¿?*)
  | (Call _, Arrow _)   -> None (*¿?*)
  | (Call _, Call _)    -> Some ((subst, [(call, lxp)]))
  | (Call _, _)         -> unify lxp call subst
  | (_, _)              -> None

(* maybe split unify into 2 function : is_unifyable and unify ?
 * cf _unify_lambda for (Lambda, Lambda) behavior*)

(** Unify a Lambda and a lexp if possible
 * See above for result
 *)
and _unify_lambda (lambda: lexp) (lxp: lexp) (subst: substitution) : return_type =
  match (lambda, lxp) with
  | (Lambda (var_kind1, _, ltype1, lexp1), Lambda (var_kind2, _, ltype2, lexp2))
    -> if var_kind1 = var_kind2
    then _unify_inner_arrow ltype1 lexp1 ltype2 lexp2 subst
    else None
  | (Lambda _, Var _)   -> Some ((subst, [(lambda, lxp)]))
  | (Lambda _, Let _)   -> Some ((subst, [(lambda, lxp)]))
  | (Lambda _, Arrow _) -> Some ((subst, [(lambda, lxp)])) (* ?? *)
  | (Lambda _, Call _)  -> Some ((subst, [(lambda, lxp)]))
  | (Lambda _, _)       -> unify lxp lambda subst
  | (_, _)              -> None

(** Unify a Metavar and a lexp if possible
 * See above for result
 * Metavar is the 'end' of the rules i.e. : it can call unify with his argument (re-ordered)
 *)
and _unify_metavar (meta: lexp) (lxp: lexp) (subst: substitution) : return_type =
  match (meta, lxp) with
  | (Metavar (val1, _, _), Metavar (val2, _, _)) ->
    if val1 = val2
    then Some ((add_substitution meta subst, []))
    else None
  | (Metavar (v, _, _), _) -> (
      match find_or_none meta subst with
      | None          -> Some ((associate v lxp subst, []))
      | Some (lxp_)   -> unify lxp_ lxp subst) (*Not sure if it's the expected behavior*)
  | (_, _) -> None

(** Unify a Arrow and a lexp if possible
 * (Arrow, Arrow) -> if var_kind = var_kind
                     then unify ltype & lexp (Arrow (var_kind, _, ltype, lexp))
                     else None
 * (_, _) -> None
 *)
and _unify_arrow (arrow: lexp) (lxp: lexp) (subst: substitution)
  : return_type =
  match (arrow, lxp) with
  (*?????*)
  | (Arrow (var_kind1, _, ltype1, _, lexp1), Arrow (var_kind2, _, ltype2, _, lexp2))
    -> if var_kind1 = var_kind2
    then (match _unify_inner_arrow ltype1 lexp1 ltype2 lexp2 subst with
        | Some _ -> Some ((add_substitution arrow subst, []))
        | None -> None)
    else None
  | (Arrow _, _) -> unify lxp arrow subst
  | (_, _) -> None

(** Unify lexp & ltype (Arrow (_,_,ltype, lexp)) of two Arrow*)
and _unify_inner_arrow (lt1: lexp) (lxp1: lexp)
    (lt2: lexp) (lxp2: lexp) (subst: substitution): return_type =
  match unify lt1 lt2 subst with
  | Some (subst_, const) -> ( (*bracket for formating*)
      match unify lxp1 lxp2 subst_ with
      | Some (s, c) -> Some(s, const@c)
      | None -> None )
  | None -> None

(** Unify a Var and a lexp, if possible
 * (Var, Var) -> unify if they have the same debruijn index FIXME : shift indexes
 * (Var, Metavar) -> unify_metavar Metavar var subst
 * (_, _) -> None
 *)
and _unify_var (var: lexp) (r: lexp) (subst: substitution) : return_type =
  match (var, r) with
  | (Var (_, idx1), Var (_, idx2))
    -> if idx1 = idx2 then Some ((add_substitution var subst, []))
    else None
  | (Var _, _) -> unify r var subst (*returns to unify*)
  | (_, _)   -> None

(** Unify two Imm if they match <=> Same type and same value
 * Add one of the Imm (the first arguement) to the substitution *)
and _unify_imm (l: lexp) (r: lexp) (subst: substitution) : return_type =
  match (l, r) with
  | (Imm (String (_, v1)), Imm (String (_, v2)))
    -> if v1 = v2 then Some ((add_substitution l subst, []))
    else None
  | (Imm (Integer (_, v1)), Imm (Integer (_, v2)))
    -> if v1 = v2 then Some ((add_substitution l subst, []))
    else None
  | (Imm (Float (_, v1)), Imm (Float (_, v2)))
    -> if v1 = v2 then Some ((add_substitution l subst, []))
    else None
  | (Imm _, Imm _) -> None
  | (Imm _, _) -> unify r l subst
  | (_, _) -> None

(** Unify a builtin (bltin) and a lexp (lxp) if it is possible
 * If the two arguments are builtin, unify based on name
 * If it's a Builtin and an other lexp, unify lexp part of Builtin with the lexp
*)
and _unify_builtin (bltin: lexp) (lxp: lexp) (subst: substitution) : return_type =
  match (bltin, lxp) with
  | (Builtin ((_, name1), _), Builtin ((_, name2),_))
    -> if name1 = name2 then Some ((add_substitution lxp subst, []))
    else None (* assuming that builtin have unique name *)
  | (Builtin (_, lxp_), _) -> (match unify lxp lxp subst with
      | None -> None
      | Some (_, c)-> Some ((add_substitution bltin subst, c)))
  | (_, _) -> None

(** Unify a Let (let_) and a lexp (lxp), if possible
 * Unify the left lexp part of the Let (Let (_, _, lxp)) with the lexp
 *)
and _unify_let (let_: lexp) (lxp: lexp) (subst: substitution) : return_type =
  match let_ with (* Discard the middle part of Let : right behavior ? *)
  | Let (_, _, lxp_) -> (match unify lxp_ lxp subst with
      | None -> None
      | Some (_, c) -> Some ((add_substitution let_ subst, c)))
  | _ -> None

