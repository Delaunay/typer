
open Lexp
open Sexp

module VMap = Map.Make (struct type t = int let compare = compare end)

type substitution = lexp VMap.t
type constraints  = (lexp * lexp) list

(* IMPROVEMENT For error handling : can carry location and name of type error *)
(*type 'a result =*)
(*| Some of 'a*)
(*| Error of Util.location * string (*location * type name*)*)
(*| Nil*)

(*let result_to_option (e: 'a result) : ('a option) =*)
(*match e with*)
(*| Some elt -> Some elt*)
(*| Error _  -> None*)
(*| Nil      -> None*)

let global_last_metavar = ref 0
let create_metavar = global_last_metavar := !global_last_metavar + 1; !global_last_metavar

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

(* Zip while applying a function, returns empty list if l1 & l2 have different size*)
let zip_map (l1: 'a list ) (l2: 'b list ) (f: ('a -> 'b -> 'c)): 'c list option =
  let rec zip_ ll1 ll2 f =
    match ll1, ll2 with
    | (h1::t1, h2::t2) -> (f h1 h2)::(zip_ t1 t2 f)
    | ([], []) -> []
    | _, _ -> [] (* Should never happen since we check length before actually calling the recursion but without this case, the compiler complains*)
  in if List.length l1 = List.length l2 then Some (zip_ l1 l2 f) else None

let zip (l1: 'a list) (l2: 'b list): (('a * 'b) list option) = zip_map l1 l2 (fun x z -> (x, z))

let zip_fold list1 list2 f =
  let l1 = List.fold_right (f) list1 []
  and l2 = List.fold_right (f) list2 []
  in zip l1 l2

(**
 * lexp is equivalent to _ in ocaml
 * (Let , lexp) == (lexp , Let)
 * UNIFY      -> recursive call or dispatching
 * OK         -> add a substituion to the list of substitution
 * CONSTRAINT -> returns a constraint
*)

(****************************** Top level unify *************************************)

(** Dispatch to the right unifyer.
 * If (_unify_X X Y) don't handle the case (X, Y), it call (unify Y X)
 * The metavar unifyer is the end rule, it can't call unify with it's parameter (changing their order)
*)
let rec unify (l: lexp) (r: lexp) (subst: substitution) : return_type =
  let tmp = match (l, r) with
    | (_, Metavar _)   -> _unify_metavar  r l subst
    | (_, Call _)      -> _unify_call     r l subst
    | (_, Case _)      -> _unify_case     r l subst
    | (_, Susp _)      -> _unify_susp     r l subst
    | (_, Let _)       -> _unify_let      r l subst
    | (Imm _, _)       -> _unify_imm      l r subst
    | (Cons _, _)      -> _unify_cons     l r subst
    | (Builtin _, _)   -> _unify_builtin  l r subst
    | (Let _, _)       -> _unify_let      l r subst
    | (Var _, _)       -> _unify_var      l r subst
    | (Arrow _, _)     -> _unify_arrow    l r subst
    | (Lambda _, _)    -> _unify_lambda   l r subst
    | (Metavar _, _)   -> _unify_metavar  l r subst
    | (Call _, _)      -> _unify_call     l r subst
    | (Susp _, _)      -> _unify_susp     l r subst
    | (Case _, _)      -> _unify_case     l r subst
    | (Inductive _, _) -> _unfiy_induct   l r subst
    | (Sort _, _)      -> _unify_sort     l r subst
    | (SortLevel _, _) -> _unify_sortlvl  l r subst
    (*  | (_, _)           -> None*)
  in match tmp with
  | Some _ -> Debug_fun.debug_print_unify "unify" l r " -> unification success"; tmp
  | None -> Debug_fun.debug_print_unify "unify" l r " -> unification failed"; tmp

(********************************* Type specific unify *******************************)

(** Unify two Imm if they match <=> Same type and same value
 * Add one of the Imm (the first arguement) to the substitution
 * Imm, Imm  ->  if Imm =/= Imm then ERROR else OK
 * Imm, lexp -> unify lexp Imm
*)
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

(** Unify a Cons and a lexp
 * Cons, Cons -> if Cons ~= Cons then OK else ERROR
 * Cons, _    -> ERROR
*)
(*FIXME which parameter of Cons is it's name ?*)
(* symbol = (location * string)*)
(*TODO in index comparison : shift indexes ?*)
and _unify_cons (cons: lexp) (lxp: lexp) (subst: substitution) : return_type =
  match (cons, lxp) with
  | (Cons ((_, idx),  (_, name)),
     Cons ((_, idx2), (_, name2))) when name = name2 ->
    if idx = idx2 then Some (subst, [])
    else None
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
 * Let , Let -> check the 'inside' of the let
 * Let , lexp -> constraint
*)
and _unify_let (let_: lexp) (lxp: lexp) (subst: substitution) : return_type =
  let concat = (fun (_, lxp, lt) acc -> lxp::lt::acc)
  in
  let try_zip_fold m m1 f lxp_ lxp2 subst = match zip_fold m m1 f with
    | Some [] -> Some (subst, []) (* ??? *)
    | None -> None
    | Some tail -> _unify_inner ((lxp_, lxp2)::(tail)) subst
  in
  let tmp = match (let_, lxp) with
  | (Let (_, m, lxp_), Let (_, m1, lxp2)) -> try_zip_fold m m1 concat lxp_ lxp2 subst
  | (Let _,  _) -> Some (subst, [(let_, lxp)])
  | _, _ -> None
  in match tmp with
  | Some _ -> Debug_fun.debug_print_unify "_unify_let" let_ lxp " -> unification success"; tmp
  | None -> Debug_fun.debug_print_unify "_unify_let" let_ lxp " -> unification failed"; tmp

(** Unify a Var and a lexp, if possible
 * (Var, Var) -> unify if they have the same debruijn index FIXME : shift indexes
 * (Var, Metavar) -> unify_metavar Metavar var subst
 * (Var _, _) -> unfiy lexp Var subst
*)
(*FIXME : check for the value of Var -> need context ?*)
and _unify_var (var: lexp) (r: lexp) (subst: substitution) : return_type =
  match (var, r) with
  | (Var (_, idx1), Var (_, idx2))
    -> if idx1 = idx2 then Some ((subst, []))
    else None
  | (Var _, Imm _) -> Some (subst, [(var, r)])
  | (Var _, _)     -> unify r var subst (*returns to unify*)
  | (_, _)         -> None

(** Unify a Arrow and a lexp if possible
 * (Arrow, Arrow) -> if var_kind = var_kind
                     then unify ltype & lexp (Arrow (var_kind, _, ltype, lexp))
                     else None
 * (Arrow, Var) -> Constraint
 * (_, _) -> None
*)
and _unify_arrow (arrow: lexp) (lxp: lexp) (subst: substitution)
  : return_type =
  match (arrow, lxp) with
  | (Arrow (var_kind1, _, ltype1, _, lexp1), Arrow (var_kind2, _, ltype2, _, lexp2))
    -> if var_kind1 = var_kind2
    then _unify_inner ((ltype1, ltype2)::(lexp1, lexp2)::[]) subst
    else None
  | (Arrow _, Imm _) -> None
  | (Arrow _, Var _) -> Some (subst, [(arrow, lxp)])
  | (Arrow _, _) -> unify lxp arrow subst
  | (_, _) -> None

(** Unify a Lambda and a lexp if possible
 * Lamda     , Lambda             -> if var_kind = var_kind
                                     then UNIFY ltype & lxp else ERROR
 * Lambda    , Var                -> CONSTRAINT
 * Lambda    , Call               -> Constraint
 * Lambda    , Let                -> Constraint
 * Lambda    , lexp               -> unify lexp lambda subst
*)
and _unify_lambda (lambda: lexp) (lxp: lexp) (subst: substitution) : return_type =
  match (lambda, lxp) with
  | (Lambda (var_kind1, _, ltype1, lexp1), Lambda (var_kind2, _, ltype2, lexp2))
    -> if var_kind1 = var_kind2
    then _unify_inner ((ltype1, ltype2)::(lexp1, lexp2)::[]) subst
    else None
  | (Lambda _, Var _)   -> Some ((subst, [(lambda, lxp)]))
  | (Lambda _, Let _)   -> Some ((subst, [(lambda, lxp)]))
  | (Lambda _, Arrow _) -> None
  | (Lambda _, Call _)  -> Some ((subst, [(lambda, lxp)]))
  | (Lambda _, Imm _)   -> None
  | (Lambda _, _)       -> unify lxp lambda subst
  | (_, _)              -> None

(** Unify a Metavar and a lexp if possible
 * lexp      , {metavar <-> none} -> UNIFY
 * lexp      , {metavar <-> lexp} -> UNFIFY lexp subst[metavar]
 * metavar   , metavar            -> if Metavar = Metavar then OK else ERROR
 * metavar   , lexp               -> OK
*)
and _unify_metavar (meta: lexp) (lxp: lexp) (subst: substitution) : return_type =
  let find_or_unify metavar value lxp s =
    match find_or_none metavar s with
    | None          -> Some ((associate value lxp s, []))
    | Some (lxp_)   -> unify lxp_ lxp s
  in
  match (meta, lxp) with
  | (Metavar (val1, _), Metavar (val2, _)) when val1 = val2 ->
    Some ((subst, []))
  | (Metavar (v, _), _) -> find_or_unify meta v lxp subst
  | (_, _) -> None

(** Unify a Call (call) and a lexp (lxp)
 * Call      , Call               -> UNIFY
 * Call      , lexp               -> CONSTRAINT
*)
and _unify_call (call: lexp) (lxp: lexp) (subst: substitution) : return_type =
  let f = (fun (_, x) acc -> x::acc)
  in let try_zip_fold lst1 lst2 lxp1 lxp2 subst = (match zip_fold lst1 lst2 f with
      | Some [] -> Some (subst, [])
      | None -> None
      | Some tail -> _unify_inner ((lxp1, lxp2)::(tail)) subst)
  in
  let tmp = match (call, lxp) with
  | (Call (lxp_left, lxp_list1), Call (lxp_right, lxp_list2)) -> try_zip_fold lxp_list1 lxp_list2 lxp_left lxp_right subst
  | (Call _, _) -> Some ((subst, [(call, lxp)]))
  | (_, _)      -> None
  in match tmp with
  | None -> Debug_fun.debug_print_unify "_unify_call" call lxp " -> unification failed"; tmp
  | Some _ -> Debug_fun.debug_print_unify "_unify_call" call lxp " -> unification success"; tmp

(** Apply unsusp to the Susp and unify the result with the lexp
*)
and _unify_susp (susp_: lexp) (lxp: lexp) (subst: substitution) : return_type =
  match susp_ with
  | Susp _ -> unify (unsusp_all susp_) lxp subst
  | _ -> None

(** Unify a Case with a lexp
 * Case, Case -> try to unify
 * Case, _ -> Constraint
*)
and _unify_case (case: lexp) (lxp: lexp) (subst: substitution) : return_type =
  let merge (_, c) r2 = match r2 with
    | None -> None
    | Some (s', c') -> Some (s', c@c')
  in
  let match_unify_inner lst sm1 sm2 s = match _unify_inner lst s with
    | None -> None
    | Some (s, c) -> merge (s, c) (_unify_inner_case (zip (SMap.bindings sm1) (SMap.bindings sm2)) s)
  in
  let match_lxp_opt lo1 lo2 tail sm1 sm2 s = match lo1, lo2 with
    | Some lxp1, Some lxp2 -> match_unify_inner ((lxp1, lxp2)::tail) sm1 sm2 s
    | _, _ -> None
  in
  let tmp = match case, lxp with
    | (Case (_, lxp, lt11, lt12, smap, lxpopt), Case (_, lxp2, lt21, lt22, smap2, lxopt2))
      -> match_lxp_opt lxpopt lxopt2 ((lt11, lt21)::(lt12, lt22)::[]) smap smap2 subst
    | (Case _, _)     -> Some (subst, [(case, lxp)])
    | (_, _) -> None
  in match tmp with
  | Some _ -> Debug_fun.debug_print_unify "_unify_case" case lxp " -> unification success"; tmp
  | None -> Debug_fun.debug_print_unify "_unify_case" case lxp " -> unification failed"; tmp

(** Unify a Inductive and a lexp
 * Inductive, Inductive -> try unify
 * Inductive, Var -> constraint
 * Inductive, Call/Metavar/Case/Let -> constraint
 * Inductive, _ -> None
*)
and _unfiy_induct (induct: lexp) (lxp: lexp) (subst: substitution) : return_type =
  let transform (a, b, c) (d, e, f) = ((a, Some b, c), (d, Some e, f))
  and merge m1 m2 (s, c) : return_type = match (_unify_induct_sub_list (SMap.bindings m1) (SMap.bindings m2) s) with
    | Some (s', c') -> Some (s', c@c')
    | None -> None
  in
  let zip_unify lst subst m1 m2 : return_type = match _unify_inner_induct lst subst with
    | None        -> None
    | Some (s, c) -> merge m1 m2 (s, c)
  in
  match (induct, lxp) with
  | (Inductive (_, lbl1, farg1, m1), Inductive (_, lbl2, farg2, m2)) when lbl1 = lbl2 ->
    (match zip_map farg1 farg2 transform with
     | Some [] -> Some (subst, [])
     | Some lst -> zip_unify lst subst m1 m2
     | None -> None)
  | (Inductive _, Var _) -> Some (subst, [(induct, lxp)])
  | (_, _) -> None

(** Unify a SortLevel with a lexp
 * SortLevel, SortLevel -> if SortLevel ~= SortLevel then OK else ERROR
 * SortLevel, _         -> ERROR
*)
and _unify_sortlvl (sortlvl: lexp) (lxp: lexp) (subst: substitution) : return_type =
  match sortlvl, lxp with
  | (SortLevel s, SortLevel s2) -> (match s, s2 with
      | SLn i, SLn j when i = j -> Some (subst, [])
      | SLsucc l1, SLsucc l2 -> unify l1 l2 subst (* Is SLsucc some kind of linked list ? *)
      | _, _ -> None)
  | _, _ -> None

(** Unify a Sort and a lexp
 * Sort, Sort -> if Sort ~= Sort then OK else ERROR
 * Sort, Var  -> Constraint
 * Sort, lexp -> ERROR
*)
and _unify_sort (sort_: lexp) (lxp: lexp) (subst: substitution) : return_type =
  match sort_, lxp with
  | (Sort (_, srt), Sort (_, srt2)) -> (match srt, srt2 with
      | Stype lxp1, Stype lxp2 -> unify lxp1 lxp2 subst
      | StypeOmega, StypeOmega -> Some (subst, [])
      | StypeLevel, StypeLevel -> Some (subst, [])
      | _, _ -> None)
  | Sort _, Var _ -> Some (subst, [(sort_, lxp)])
  | _, _          -> None

(************************ Helper function **************************************)

(***** for Case *****)
(** Check arg_king in (arg_kind * vdef option) list in Case *)
and is_same arglist arglist2 =
  match arglist, arglist2 with
  | (akind, _)::t1, (akind2, _)::t2 when akind = akind2 -> is_same t1 t2
  | [], [] -> Debug_fun.debug_print "is_same" " unification success"; true
  | _, _ -> Debug_fun.debug_print "is_same" " unification failed"; false

(** try to unify the SMap part of the case *)
and _unify_inner_case l s =
  let rec _unify_inner_case list_ s =
    match list_ with
    | ((key, (_, arglist, lxp)), (key2, (_, arglist2, lxp2)))::tail when key = key2 ->
      (if is_same arglist arglist2 then ( match unify lxp lxp2 s with
           | Some (s', c) -> (match _unify_inner_case tail s' with
               | Some (s_, c_) -> Debug_fun.debug_print "_unify_inner_case" "unification success"; Some (s_, c@c_)
               | None -> Debug_fun.debug_print "_unify_inner_case" "unification failed"; None)
           | None -> Debug_fun.debug_print "_unify_inner_case" "unification failed"; None)
       else None)
    | [] -> Debug_fun.debug_print "_unify_inner_lxp" "unification success"; Some (s, [])
    | _ -> Debug_fun.debug_print "_unify_inner_case" "unification failed"; None
  in (match l with
      | Some [] -> Some (s, [])
      | None -> None
      | Some l -> _unify_inner_case l s)

(***** for Inductive *****)
(** for _unify_induct : unify the formal arg*)
and _unify_inner_induct lst subst : return_type =
  let test ((a1, _, l1), (a2, _, l2)) subst : return_type =
    if a1 = a2 then unify l1 l2 subst
    else None
  in
  List.fold_left (fun a e -> (match a with
      | Some (s, c) -> (match test e s with
          | Some (s1, c1) -> Some (s1, c1@c)
          | None -> Some (s, c))
      | None -> test e subst)
    ) None lst

(** unify the SMap of list in Inductive *)
and _unify_induct_sub_list l1 l2 subst =
  let test l1 l2 subst =
    let merge l1 l2 subst (s, c) = match (_unify_induct_sub_list l1 l2 subst) with
      | Some (s1, c1) -> Some (s1, c1@c)
      | None -> Some (s, c)
    in
    let unify_zip lst t1 t2 = match _unify_inner_induct lst subst with
      | Some (s, c) -> merge l1 l2 subst (s, c)
      | None -> (_unify_induct_sub_list t1 t2 subst)
    in
    match l1, l2 with
    | (k1, v1)::t1, (k2, v2)::t2 when k1 = k2 ->
      (match zip v1 v2 with
       | Some [] -> Some (subst, [])
       | Some lst -> unify_zip lst t1 t2
       | None -> None)
    | _, _ -> None
  in test l1 l2 subst

(***** general *****)

(** take two list [(vdef * ltype * lexp), (vdef2 * ltype2 * lexp2)...]
    map them to [ltype, lexp, ltype2, lexp2, ...]
    and zip them to
    [(ltype * ltype), (lexp * lexp), (ltype2 * ltype2), (lexp2 * lexp2), ...]
*)
and _unify_inner (lxp_l: (lexp * lexp) list) (subst: substitution) : return_type =
  let merge ((s, c): (substitution * constraints))
      (lxp_list: (lexp * lexp) list) : return_type =
    match _unify_inner lxp_list s with
    (*| None -> Some (s, c)*)
    | None -> Debug_fun.debug_print "_unify_inner.merge" "unification failed"; None
    | Some (s_,c_) -> Debug_fun.debug_print "_unify_inner.merge" "unification success"; Some (s_, c@c_)
  in
  match lxp_l with
  | (lxp1, lxp2)::tail -> ( match unify lxp1 lxp2 subst with
      | Some (s, c) -> merge (s, c) tail
      | None -> Debug_fun.debug_print "_unify_inner" "unification failed"; None)
  | [] -> Debug_fun.debug_print "_unify_inner" "unification success : list empty"; Some (subst, [])

