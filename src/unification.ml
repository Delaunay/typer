
open Lexp
open Sexp

module VMap = Map.Make (struct type t = int let compare = compare end)

type substitution = lexp VMap.t
type constraints  = (lexp * lexp) list
(* IMPROVEMENT For error handling : can carry location and name of type error *)
type 'a expected =
  | Some of 'a
  | Error of Util.location * string (*location * type name*)
  | None

let global_last_metavar = ref 0
let create_metavar = global_last_metavar := !global_last_metavar + 1; !global_last_metavar

let expected_to_option (e: 'a expected) : ('a option) =
  match e with
  | Some elt -> Some elt
  | Error _  -> None
  | None     -> None

(* For convenience *)
type return_type = (substitution * constraints) option

(** Alias for VMap.add*)
let associate (meta: int) (lxp: lexp) (subst: substitution)
  : substitution =
  (VMap.add meta lxp subst)

(** If key is in map returns the value associated
 * else returns None
*)
let find_or_none (value: lexp) (map: substitution) : lexp option =
  match value with
  | Metavar (idx, _) -> (if VMap.mem idx map
                            then Some (VMap.find idx map)
                            else None)
  | _ -> None

let empty_subst = (VMap.empty)

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
 * Arrow     , Imm                -> ERROR
 * Arrow     , Var                -> CONSTRAINT

 * lexp      , {metavar <-> none} -> UNIFY
 * lexp      , {metavar <-> lexp} -> UNFIFY lexp subst[metavar]
 * metavar   , metavar            -> if Metavar = Metavar then OK else ERROR
 * metavar   , lexp               -> ERROR

 * Lamda     , Lambda             -> if var_kind = var_kind
                                     then UNIFY ltype & lxp else ERROR
 * Lambda    , Var                -> CONSTRAINT
 * Lambda    , lexp               -> ERROR
 * Call      , Imm                -> CONSTRAINT
 * Call      , Cons               -> ERROR
 * Call      , Buitin             -> ERROR
 * Call      , Var                -> CONSTRAINT
 * Call      , Let                -> ERROR
 * Call      , Arrow              -> ERROR
 * Call      , Call               -> CONSTRAINT
 * Case      , lexp               -> ERROR

   (*TODO*)
 * Inductive , lexp               ->
 * Susp      , lexp               ->
 * lexp      , lexp               ->

 * lexp is equivalent to _ in ocaml
 * (Let , lexp) == (lexp , Let)
 * UNIFY      -> recursive call or dispatching
 * OK         -> add a substituion to the list of substitution
 * CONSTRAINT -> returns a constraint
*)

(** Dispatch to the right unifyer.
 * If (_unify_X X Y) don't handle the case (X, Y), it call (unify Y X)
 * The metavar unifyer is the end rule, it can't call unify with it's parameter (changing their order)
*)

let rec unify (l: lexp) (r: lexp) (subst: substitution) : return_type =
  match (l, r) with
  | (_, Metavar _) -> _unify_metavar  r l subst
  | (_, Call _)    -> _unify_call     r l subst
  | (Imm _, _)     -> _unify_imm      l r subst
  | (Cons _, _)    -> _unify_cons     l r subst
  | (Builtin _, _) -> _unify_builtin  l r subst
  | (Let _, _)     -> _unify_let      l r subst
  | (Var _, _)     -> _unify_var      l r subst
  | (Arrow _, _)   -> _unify_arrow    l r subst
  | (Lambda _, _)  -> _unify_lambda   l r subst
  | (Metavar _, _) -> _unify_metavar  l r subst
  | (Call _, _)    -> _unify_call     l r subst
  | (Susp _, _)    -> _unify_susp     l r subst
  | (Case _, _)    -> None
  | (_, _)         -> None

and _unify_susp (susp_: lexp) (lxp: lexp) (subst: substitution) : return_type =
  match susp_ with
  | Susp _ -> unify (unsusp_all susp_) lxp subst
  | _ -> None

and _unify_cons (cons: lexp) (lxp: lexp) (subst: substitution) : return_type =
  (* symbol = (location * string)*)
  match (cons, lxp) with
  (*FIXME which parameter of Cons is it's name ?*)
  | (Cons ((_, idx),  (_, name)),
     Cons ((_, idx2), (_, name2))) when name = name2 ->
          if idx = idx2 then Some (subst, []) (*TODO shift indexes ?*)
          else None
  | (_, _) -> None

and _unify_call (call: lexp) (lxp: lexp) (subst: substitution) : return_type =
  let combine list1 list2 =
    let l1 = List.fold_left (fun acc (_, x) -> x::acc) [] list1
    and l2 = List.fold_left (fun acc (_, x) -> x::acc) [] list2
    in List.combine l1 l2
  in match (call, lxp) with
  | (Call (lxp1, lxp_list1), Call (lxp2, lxp_list2)) ->
    _unify_inner ((lxp1, lxp2)::(combine lxp_list1 lxp_list2)) subst
  | (Call _, _) -> Some ((subst, [(call, lxp)]))
  | (_, _)      -> None

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
  | (Lambda _, Arrow _) -> None
  | (Lambda _, Call _)  -> Some ((subst, [(lambda, lxp)]))
  | (Lambda _, Imm _)   -> None
  | (Lambda _, _)       -> unify lxp lambda subst
  | (_, _)              -> None

(** Unify a Metavar and a lexp if possible
 * See above for result
 * Metavar is the 'end' of the rules i.e. : it can call unify with his argument (re-ordered)
*)
and _unify_metavar (meta: lexp) (lxp: lexp) (subst: substitution) : return_type =
  match (meta, lxp) with
  | (Metavar (val1, _), Metavar (val2, _)) when val1 = val2 ->
    Some ((subst, []))
  | (Metavar (v, _), _) -> (
      match find_or_none meta subst with
      | None          -> Some ((associate v lxp subst, []))
      | Some (lxp_)   -> unify lxp_ lxp subst)
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
  | (Arrow (var_kind1, _, ltype1, _, lexp1), Arrow (var_kind2, _, ltype2, _, lexp2))
    -> if var_kind1 = var_kind2
    then _unify_inner_arrow ltype1 lexp1 ltype2 lexp2 subst
    else None
  | (Arrow _, Imm _) -> None
  | (Arrow _, Var _) -> Some (subst, [(arrow, lxp)]) (* FIXME Var can contain type ???*)
  | (Arrow _, _) -> unify lxp arrow subst
  (*| (Arrow _, Call _) -> None*) (* Call can return type (?) *)
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
    -> if idx1 = idx2 then Some ((subst, []))
    else None
  | (Var _, Imm _) -> Some (subst, [(var, r)])(*FIXME : check for the value of Var -> need context ?*)
  | (Var _, _)     -> unify r var subst (*returns to unify*)
  | (_, _)         -> None

(** Unify two Imm if they match <=> Same type and same value
 * Add one of the Imm (the first arguement) to the substitution *)
and _unify_imm (l: lexp) (r: lexp) (subst: substitution) : return_type =
  match (l, r) with
  | (Imm (String (_, v1)), Imm (String (_, v2)))
    -> if v1 = v2 then Some ((subst, []))
    else None
  | (Imm (Integer (_, v1)), Imm (Integer (_, v2)))
    -> if v1 = v2 then Some ((subst, []))
    else None
  | (Imm (Float (_, v1)), Imm (Float (_, v2)))
    -> if v1 = v2 then Some ((subst, []))
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
    -> if name1 = name2 then Some ((subst, []))
    else None (* assuming that builtin have unique name *)
  | (Builtin (_, lxp_bltin), _) -> unify lxp_bltin lxp subst
  | (_, _) -> None

(** Unify a Let (let_) and a lexp (lxp), if possible
 * Unify the left lexp part of the Let (Let (_, _, lxp)) with the lexp
*)
and _unify_let (let_: lexp) (lxp: lexp) (subst: substitution) : return_type =
  match (let_, lxp) with
  | (Let (_, m, lxp_), Let (_, m1, lxp2)) ->
    _unify_inner ((lxp_, lxp2)::(combine m m1)) subst
  | (Let _,  _) -> Some (subst, [(let_, lxp)])
  | _, _ -> None

(** take two list [(vdef * ltype * lexp), (vdef2 * ltype2 * lexp2)...]
    map them to [ltype, lexp, ltype2, lexp2, ...]
    and zip them to
    [(ltype * ltype), (lexp * lexp), (ltype2 * ltype2), (lexp2 * lexp2), ...]
*)
and combine list1 list2 =
  let l1 = List.fold_left (fun acc (_, t, x) -> t::x::acc) [] list1
  and l2 = List.fold_left (fun acc (_, t, x) -> t::x::acc) [] list2
  in List.combine l1 l2

and _unify_inner (lxp_l: (lexp * lexp) list) (subst: substitution) : return_type =
  let merge ((s, c): (substitution * constraints))
      (lxp_list: (lexp * lexp) list) : return_type =
    match _unify_inner lxp_list s with
    | None -> Some (s, c)
    | Some (s_,c_) -> Some (s_, c@c_)
  in
  match lxp_l with
  | (lxp1, lxp2)::tail -> ( match unify lxp1 lxp2 subst with
      | Some (s, c) -> merge (s, c) tail
      | None -> None)
  | [] -> None


