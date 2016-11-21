(* lexp.ml --- Lambda-expressions: the core language.

Copyright (C) 2011-2016  Free Software Foundation, Inc.

Author: Stefan Monnier <monnier@iro.umontreal.ca>
Keywords: languages, lisp, dependent types.

This file is part of Typer.

Typer is free software; you can redistribute it and/or modify it under the
terms of the GNU General Public License as published by the Free Software
Foundation, either version 3 of the License, or (at your option) any
later version.

Typer is distributed in the hope that it will be useful, but WITHOUT ANY
WARRANTY; without even the implied warranty of MERCHANTABILITY or FITNESS
FOR A PARTICULAR PURPOSE.  See the GNU General Public License for
more details.

You should have received a copy of the GNU General Public License along with
this program.  If not, see <http://www.gnu.org/licenses/>.  *)

module U = Util
module L = List
module SMap = U.SMap
open Fmt

open Sexp
open Pexp

open Myers
open Grammar

(* open Unify *)
module S = Subst

type vdef = U.vdef
type vref = U.vref

type label = symbol

type attribute_key  = (int * string)  (* rev_dbi * Var name *)
module AttributeMap = Map.Make (struct type t = attribute_key let compare = compare end)

(*************** Elaboration to Lexp *********************)

(* The scoping of `Let` is tricky:
 *
 * Since it's a recursive let, the definition part of each binding is
 * valid in the "final" scope which includes all the new bindings.
 *
 * But the type of each binding is not defined in that same scope.  Instead
 * it's defined in the scope of all the previous bindings.
 *
 * For exemple the type of the second binding of such a Let is defined in
 * the scope of the surrounded context extended with the first binding.
 * And the type of the 3rd binding is defined in the scope of the
 * surrounded context extended with the first and the second bindings.  *)

type ltype = lexp
 and subst = lexp S.subst
 and lexp =
   | Imm of sexp                        (* Used for strings, ...  *)
   | SortLevel of sort_level
   | Sort of U.location * sort
   | Builtin of vdef * ltype * lexp AttributeMap.t option
   | Var of vref
   | Susp of lexp * subst  (* Lazy explicit substitution: e[σ].  *)
   (* This "Let" allows recursion.  *)
   | Let of U.location * (vdef * lexp * ltype) list * lexp
   | Arrow of arg_kind * vdef option * ltype * U.location * lexp
   | Lambda of arg_kind * vdef * ltype * lexp
   | Call of lexp * (arg_kind * lexp) list (* Curried call.  *)
   | Inductive of U.location * label
                  * ((arg_kind * vdef * ltype) list) (* formal Args *)
                  * ((arg_kind * vdef option * ltype) list) SMap.t
   | Cons of lexp * symbol (* = Type info * ctor_name  *)
   | Case of U.location * lexp
             * ltype (* The type of the return value of all branches *)
             * (U.location * (arg_kind * vdef option) list * lexp) SMap.t
             * (vdef option * lexp) option               (* Default.  *)
   (* The `subst` only applies to the lexp associated
    * with the metavar's index (i.e. its "value"), not to the ltype.  *)
   | Metavar of int * subst * vdef * ltype
 (*   (\* For logical metavars, there's no substitution.  *\)
  *   | Metavar of (U.location * string) * metakind * metavar ref
  * and metavar =
  *   (\* An uninstantiated var, along with a venv (stipulating over which vars
  *    * it should be closed), and its type.
  *    * If its type is not given, it implies its type should be a sort.  *\)
  *   | MetaUnset of (lexp option * lexp) VMap.t * ltype option * scope_level
  *   | MetaSet of lexp
  * and metakind =
  *   | MetaGraft of subst
  *   (\* Forward reference or Free var: Not known yet, but not instantiable by
  *    * unification.  *\)
  *   | MetaFoF
  * and subst = lexp VMap.t *)
 (*
  * The PTS I'm imagining looks like:
  *
  *    S = { TypeLevel, TypeOmega, Type ℓ }
  *    A = { Level : TypeLevel, Z : Level, S : Level → Level,
  *          Type : (ℓ : Level) → Type (S ℓ) }
  *    R = { (TypeLevel, Type ℓ, TypeOmega),
  *          (TypeLevel, TypeOmega, TypeOmega),
  *          (Type ℓ, TypeOmega, TypeOmega),
  *          (Type ℓ₁, Type ℓ₂, Type (max l₁ l₂) }
  *)
 and sort =
   | Stype of lexp
   | StypeOmega
   | StypeLevel
 and sort_level =
   | SLz
   | SLsucc of lexp

type varbind =
  | Variable
  | ForwardRef
  | LetDef of lexp

module VMap = Map.Make (struct type t = int let compare = compare end)
type meta_subst = lexp VMap.t
type constraints  = (lexp * lexp) list
let empty_meta_subst = VMap.empty

let builtin_size = ref 0

(********************** Hash-consing **********************)

(* FIXME: We'd want this hash-table to be weak in its values: as soon
 * as one of its values can be GC'd, the entry should be removed.  *)
let hc_table : (lexp, lexp) Hashtbl.t = Hashtbl.create 1000
let hc (e : lexp) : lexp =
  try Hashtbl.find hc_table e
  with Not_found -> Hashtbl.add hc_table e e;
                            e
let mkImm s                    = hc (Imm s)
let mkSortLevel l              = hc (SortLevel l)
let mkSort (l, s)              = hc (Sort (l, s))
let mkBuiltin (v, t, m)        = hc (Builtin (v, t, m))
let mkVar v                    = hc (Var v)
let mkLet (l, ds, e)           = hc (Let (l, ds, e))
let mkArrow (k, v, t1, l, t2)  = hc (Arrow (k, v, t1, l, t2))
let mkLambda (k, v, t, e)      = hc (Lambda (k, v, t, e))
let mkInductive (l, n, a, cs)  = hc (Inductive (l, n, a, cs))
let mkCons (t, n)              = hc (Cons (t, n))
let mkCase (l, e, rt, bs, d)   = hc (Case (l, e, rt, bs, d))
let mkMetavar (n, s, v, t)     = hc (Metavar (n, s, v, t))
let mkCall (f, es)
  = match f, es with
  | Call (f', es'), _ -> hc (Call (f', es' @ es))
  | _, [] -> f
  | _ -> hc (Call (f, es))

(********* Helper functions to use the Subst operations  *********)
(* This basically "ties the knot" between Subst and Lexp.
 * Maybe it would be cleaner to just move subst.ml into lexp.ml
 * and be done with it.  *)

let rec mkSusp e s =
  if S.identity_p s then e else
    (* We apply the substitution eagerly to some terms.
     * There's no deep technical rason for that:
     * it just seemed like a good idea to do it eagerly when it's easy.  *)
    match e with
    | Susp (e, s') -> mkSusp e (scompose s' s)
    | Var (l,v) -> slookup s l v
    | Metavar (vn, s', vd, t) -> mkMetavar (vn, scompose s' s, vd, mkSusp t s)
    | _ -> hc (Susp (e, s))
and scompose s1 s2 = S.compose mkSusp s1 s2
and slookup s l v = S.lookup (fun l i -> mkVar (l, i))
                             (fun e o -> mkSusp e (S.shift o))
                             s l v
let ssink = S.sink (fun l i -> mkVar (l, i))


let rec lexp_location e =
  match e with
  | Sort (l,_) -> l
  | SortLevel (SLsucc e) -> lexp_location e
  | SortLevel SLz -> U.dummy_location
  | Imm s -> sexp_location s
  | Var ((l,_),_) -> l
  | Builtin ((l, _), _, _) -> l
  | Let (l,_,_) -> l
  | Arrow (_,_,_,l,_) -> l
  | Lambda (_,(l,_),_,_) -> l
  | Call (f,_) -> lexp_location f
  | Inductive (l,_,_,_) -> l
  | Cons (_,(l,_)) -> l
  | Case (l,_,_,_,_) -> l
  | Susp (e, _) -> lexp_location e
  (* | Susp (_, e) -> lexp_location e *)
  | Metavar (_,_,(l,_), _) -> l


(********* Normalizing a term *********)

let vdummy = (U.dummy_location, "<anon>")
let maybev mv = match mv with None -> vdummy | Some v -> v

let rec push_susp e s =            (* Push a suspension one level down.  *)
  match e with
  | Imm _ -> e
  | SortLevel (SLz) -> e
  | SortLevel (SLsucc e') -> mkSortLevel (SLsucc (mkSusp e' s))
  | Sort (l, Stype e) -> mkSort (l, Stype (mkSusp e s))
  | Sort (l, _) -> e
  | Builtin _ -> e
  | Let (l, defs, e)
    -> let s' = L.fold_left (fun s (v, _, _) -> ssink v s) s defs in
      let (_,ndefs) = L.fold_left (fun (s,ndefs) (v, def, ty)
                                   -> (ssink v s,
                                      (v, mkSusp e s', mkSusp ty s) :: ndefs))
                                  (s, []) defs in
      mkLet (l, ndefs, mkSusp e s')
  | Arrow (ak, v, t1, l, t2)
    -> mkArrow (ak, v, mkSusp t1 s, l, mkSusp t2 (ssink (maybev v) s))
  | Lambda (ak, v, t, e) -> mkLambda (ak, v, mkSusp t s, mkSusp e (ssink v s))
  | Call (f, args) -> mkCall (mkSusp f s,
                             L.map (fun (ak, arg) -> (ak, mkSusp arg s)) args)
  | Inductive (l, label, args, cases)
    -> let (s, nargs) = L.fold_left (fun (s, nargs) (ak, v, t)
                                    -> (ssink v s, (ak, v, mkSusp t s) :: nargs))
                                   (s, []) args in
      let ncases = SMap.map (fun args
                             -> let (_, ncase)
                                 = L.fold_left (fun (s, nargs) (ak, v, t)
                                                -> (ssink (maybev v) s,
                                                   (ak, v, mkSusp t s)
                                                   :: nargs))
                                               (s, []) args in
                               L.rev ncase)
                            cases in
      mkInductive (l, label, nargs, ncases)
  | Cons (it, name) -> Cons (mkSusp it s, name)
  | Case (l, e, ret, cases, default)
    -> mkCase (l, mkSusp e s, mkSusp ret s,
              SMap.map (fun (l, cargs, e)
                        -> let s' = L.fold_left (fun s carg
                                                -> match carg with
                                                  | (_,None) -> s
                                                  | (_,Some v) -> ssink v s)
                                               s cargs in
                          (l, cargs, mkSusp e s'))
                       cases,
              match default with
              | None -> default
              | Some (v,e) -> Some (v, mkSusp e (ssink (maybev v) s)))
  (* Susp should never appear around Var/Susp/Metavar because mkSusp
   * pushes the subst into them eagerly.  IOW if there's a Susp(Var..)
   * or Susp(Metavar..) it's because some chunk of code should use mkSusp
   * rather than Susp.
   * But we still have to handle them here, since push_susp is called
   * in many other cases than just when we bump into a Susp.  *)
  | Susp (e,s') -> push_susp e (scompose s' s)
  | (Var _ | Metavar _) -> nosusp (mkSusp e s)

and nosusp e =                  (* Return `e` with no outermost `Susp`.  *)
  match e with
    | Susp(e, s) -> push_susp e s
    | _ -> e


(* Get rid of `Susp`ensions and instantiated `Maetavar`s.  *)
let clean meta_ctx e =
  let rec clean s e = match e with
    | Imm _ -> e
    | SortLevel (SLz) -> e
    | SortLevel (SLsucc e) -> mkSortLevel (SLsucc (clean s e))
    | Sort (l, Stype e) -> mkSort (l, Stype (clean s e))
    | Sort (l, _) -> e
    | Builtin _ -> e
    | Let (l, defs, e)
      -> let s' = L.fold_left (fun s (v, _, _) -> ssink v s) s defs in
        let (_,ndefs) = L.fold_left (fun (s,ndefs) (v, def, ty)
                                     -> (ssink v s,
                                        (v, clean s' e, clean s ty) :: ndefs))
                                  (s, []) defs in
        mkLet (l, ndefs, clean s' e)
    | Arrow (ak, v, t1, l, t2)
      -> mkArrow (ak, v, clean s t1, l, clean (ssink (maybev v) s) t2)
    | Lambda (ak, v, t, e) -> mkLambda (ak, v, clean s t, clean (ssink v s) e)
    | Call (f, args) -> mkCall (clean s f,
                               L.map (fun (ak, arg) -> (ak, clean s arg)) args)
    | Inductive (l, label, args, cases)
      -> let (s, nargs) = L.fold_left (fun (s, nargs) (ak, v, t)
                                    -> (ssink v s, (ak, v, clean s t) :: nargs))
                                   (s, []) args in
      let ncases = SMap.map (fun args
                             -> let (_, ncase)
                                 = L.fold_left (fun (s, nargs) (ak, v, t)
                                                -> (ssink (maybev v) s,
                                                   (ak, v, clean s t)
                                                   :: nargs))
                                               (s, []) args in
                               L.rev ncase)
                            cases in
      mkInductive (l, label, nargs, ncases)
    | Cons (it, name) -> Cons (clean s it, name)
    | Case (l, e, ret, cases, default)
      -> mkCase (l, clean s e, clean s ret,
                SMap.map (fun (l, cargs, e)
                          -> let s' = L.fold_left (fun s carg
                                                  -> match carg with
                                                    | (_,None) -> s
                                                    | (_,Some v) -> ssink v s)
                                                 s cargs in
                            (l, cargs, clean s' e))
                         cases,
                match default with
                | None -> default
                | Some (v,e) -> Some (v, clean (ssink (maybev v) s) e))
    | Susp (e, s') -> clean (scompose s' s) e
    | Var _ -> if S.identity_p s then e
              else clean S.identity (mkSusp e s)
    | Metavar (idx, s', l, t)
      -> let s = (scompose s' s) in
        try clean s (VMap.find idx meta_ctx)
        with Not_found -> mkMetavar (idx, s, l, t)
  in clean S.identity e

let lexp_name e =
  match e with
    | Imm    _ -> "Imm"
    | Var    _ -> "Var"
    | Let    _ -> "let"
    | Arrow  _ -> "Arrow"
    | Lambda _ -> "lambda"
    | Call   _ -> "Call"
    | Cons   _ -> "inductive-cons"
    | Case   _ -> "case"
    | Inductive _ -> "inductive_"
    | Susp      _ -> "Susp"
    | Builtin   (_, _, None) -> "Builtin"
    | Builtin   _ -> "AttributeTable"
    | _ -> "lexp_to_string: not implemented"

(* ugly printing (sexp_print (pexp_unparse (lexp_unparse e))) *)
let rec lexp_unparse lxp =
  match lxp with
    | Susp _ as e -> lexp_unparse (nosusp e)
    | Imm (sexp) -> Pimm (sexp)
    | Builtin ((loc, name), _, None) -> Pvar((loc, name))
    | Builtin ((loc, name), ltp, _   )
      -> Pcall(Pvar((loc, name)), [pexp_unparse (lexp_unparse ltp)])

    | Var ((loc, name), _) -> Pvar((loc, name))
    | Cons (t, ctor) -> Pcons (lexp_unparse t, ctor)
    | Lambda (kind, vdef, ltp, body) ->
      Plambda(kind, vdef, Some (lexp_unparse ltp), lexp_unparse body)
    | Arrow (arg_kind, vdef, ltp1, loc, ltp2) ->
      Parrow(arg_kind, vdef, lexp_unparse ltp1, loc, lexp_unparse ltp2)

    | Let (loc, ldecls, body)
      -> (* (vdef * lexp * ltype) list *)
       let pdecls = List.fold_left
                      (fun acc (vdef, lxp, ltp)
                       -> Ptype (vdef, lexp_unparse ltp)
                         :: Pexpr(vdef, lexp_unparse lxp)::acc)
                      [] ldecls in
       Plet (loc, pdecls, lexp_unparse body)

    | Call(lxp, largs) -> (* (arg_kind * lexp) list *)
      let pargs = List.map (fun (kind, elem) -> lexp_unparse elem) largs in
      let sargs = List.map (fun elem -> pexp_unparse elem) pargs in
        Pcall(lexp_unparse lxp, sargs)

    | Inductive(loc, label, lfargs, ctor) ->
      (* (arg_kind * vdef * ltype) list *)
      (* (arg_kind * pvar * pexp option) list *)
      let pfargs = List.map (fun (kind, vdef, ltp) ->
        (kind, vdef, Some (lexp_unparse ltp))) lfargs in

      (* ((arg_kind * vdef option * ltype) list) SMap.t *)
      (* (symbol * (arg_kind * pvar option * pexp) list) list *)
      let ctor = List.map (fun (str, largs) ->
        let pargs = List.map (fun (kind, var, ltp) ->
          match var with
            | Some (loc, name) -> (kind, Some (loc, name), lexp_unparse ltp)
            | None             -> (kind, None, lexp_unparse ltp)) largs
          in ((loc, str), pargs)
          ) (SMap.bindings ctor)
        in Pinductive(label, pfargs, ctor)

    | Case (loc, target, bltp, branches, default) ->
       let bt = lexp_unparse bltp in
      let pbranch = List.map (fun (str, (loc, args, bch)) ->
        match args with
          | [] -> Ppatsym (loc, str), lexp_unparse bch
          | _  ->
             let pat_args
               = List.map (fun (kind, vdef)
                           -> match vdef with
                             | Some vdef -> Some vdef, Ppatsym vdef
                             | None -> None, Ppatany loc)
                          args
            (* FIXME: Rather than a Pcons we'd like to refer to an existing
             * binding with that value!  *)
            in Ppatcons (Pcons (bt, (loc, str)), pat_args), lexp_unparse bch
        ) (SMap.bindings branches) in

      let pbranch = match default with
        | Some (v,dft) -> ((match v with
                           | None -> Ppatany loc
                           | Some vdef -> Ppatsym vdef),
                          lexp_unparse dft)::pbranch
        | None -> pbranch
        in Pcase (loc, lexp_unparse target, pbranch)

    (* FIXME: The cases below are all broken!  *)
    | Metavar (idx, subst, (loc, name), _)
      -> Pimm (Symbol (loc, "?<" ^ name ^ "-" ^ string_of_int idx
                           ^ "[" ^ subst_string subst ^ "]>"))

    | SortLevel (SLz) -> Pimm (Integer (U.dummy_location, 0))
    | SortLevel (SLsucc sl) -> Pcall (Pimm (Symbol (U.dummy_location, "<S>")),
                                     [pexp_unparse (lexp_unparse sl)])
    | Sort (l, StypeOmega) -> Pimm (Symbol (l, "<TypeOmega>"))
    | Sort (l, StypeLevel) -> Pimm (Symbol (l, "<TypeLevel>"))
    | Sort (l, Stype sl) -> Pcall (Pimm (Symbol (l, "<Type>")),
                                  [pexp_unparse (lexp_unparse sl)])

(* FIXME: ¡Unify lexp_print and lexp_string!  *)
and lexp_string lxp = sexp_string (pexp_unparse (lexp_unparse lxp))

and subst_string s = match s with
  | S.Identity -> "Id"
  | S.Shift (s, n) -> "(↑"^ string_of_int n ^ " " ^ subst_string s ^ ")"
  | S.Cons (l, s) -> lexp_string l ^ " · " ^ subst_string s

(*
 *      Printing
 * --------------------- *)
(*
    pretty ?        (print with new lines and indents)
    indent level
    print_type?     (print inferred Type)
    print_index     (print dbi index)
    separate decl   (print extra newline between declarations)
    indent size     2/4
    highlight       (use console color to display hints)
*)

type print_context = (bool * int * bool * bool * bool * bool* int)

let pretty_ppctx  = ref (true , 0, true, false, true,  2, true)
let compact_ppctx = ref (false, 0, true, false, true,  2, false)
let debug_ppctx   = ref (false, 0, true, true , false, 2, true)

let rec lexp_print e =  _lexp_print (!debug_ppctx) e
and _lexp_print ctx e = print_string (_lexp_to_str ctx e)

(*
type print_context2 = int SMap.t

let default_print_context =
  List.fold (fun map (key, v) -> SMap.add key v map)
    [
      (* true options *)
      ("pretty",        1);
      ("print_type",    1);
      ("print_dbi",     1);
      ("indent_size",   2);
      ("color",         1);
      ("separate_decl", 1);

      (* State information *)
      ("indent_level",  0);
      ("previous node", 0)
    ]
    SMap.empty *)

(*  Print a lexp into its typer equivalent                              *)
(*  Depending on the print_context the output can be correct typer code *)
(*  This function will be very useful when debugging generated code     *)

(* If I remember correctly ocaml doc, concat string is actually terrible *)
(* It might be better to use a Buffer. *)
and lexp_pretty_string exp = _lexp_to_str (!debug_ppctx) exp

and _lexp_to_str ctx exp =
    (* create a string instead of printing *)

    let (pretty, indent, ptype, pindex, _, isize, color) = ctx in
    let lexp_to_str = _lexp_to_str ctx in

    (* internal context, when parsing let *)
    let inter_ctx = (pretty, indent + 1, ptype, pindex, false, isize, color) in

    let lexp_to_stri idt e =
        _lexp_to_str (pretty, indent + idt, ptype, pindex, false, isize, color) e in

    (* colors *)
    let red     = if color then red else "" in
    let green   = if color then green else "" in
    let yellow  = if color then yellow else "" in
    let magenta = if color then magenta else "" in
    let cyan    = if color then cyan else "" in
    let reset   = if color then reset  else "" in

    let _index idx = if pindex then ("[" ^ (string_of_int idx) ^ "]") else "" in

    let make_indent idt = if pretty then (make_line ' ' ((idt + indent) * isize)) else "" in
    let newline = (if pretty then "\n" else " ") in
    let nl = newline in

    let keyword str  = magenta ^ str ^ reset in
    let error str    = red     ^ str ^ reset in
    let tval str     = yellow  ^ str ^ reset in
    let fun_call str = cyan    ^ str ^ reset in

    let index idx = let str = _index idx in if idx < 0 then (error str) else
        (green ^ str ^ reset) in

    let kind_str k =
        match k with
            | Aexplicit -> "->" | Aimplicit -> "=>" | Aerasable -> "≡>" in

    let kindp_str k =
        match k with
            | Aexplicit -> ":" | Aimplicit -> "::" | Aerasable -> ":::" in

    match exp with
        | Imm(value) -> (match value with
            | String (_, s) -> tval ("\"" ^ s ^ "\"")
            | Integer(_, s) -> tval (string_of_int s)
            | Float  (_, s) -> tval (string_of_float s)
            | e -> sexp_string e)

        | Susp (e, s) -> _lexp_to_str ctx (push_susp e s)

        | Var ((loc, name), idx) -> name ^ (index idx) ;

        | Metavar (idx, subst, (loc, name), _)
          -> "?" ^ name ^ (index idx) (*TODO : print subst*)

        | Let (_, decls, body)   ->
            (* Print first decls without indent *)
            let h1, decls, idt_lvl =
                match _lexp_str_decls inter_ctx decls with
                    | h1::decls -> h1, decls, 2
                    | _ -> "", [], 1 in

            let decls = List.fold_left (fun str elem
                                        -> str ^ (make_indent 1) ^ elem ^ nl)
                                       (h1 ^ nl) decls  in

            let n = String.length decls - 2 in
            (* remove last newline *)
            let decls = (String.sub decls 0 n) in

            (keyword "let ") ^ decls ^ (keyword " in ") ^ newline ^
                (make_indent idt_lvl) ^ (lexp_to_stri 1 body)

        | Arrow(k, Some (_, name), tp, loc, expr) ->
            "(" ^ name ^ " : " ^ (lexp_to_str tp) ^ ") " ^
                (kind_str k) ^ " " ^ (lexp_to_str expr)

        | Arrow(k, None, tp, loc, expr) ->
           "(" ^ (lexp_to_str tp) ^ " "
           ^ (kind_str k) ^ " " ^ (lexp_to_str expr) ^ ")"

        | Lambda(k, (loc, name), ltype, lbody) ->
            let arg = "(" ^ name ^ " : " ^ (lexp_to_str ltype) ^ ")" in

            (keyword "lambda ") ^ arg ^ " " ^ (kind_str k) ^ newline ^
                (make_indent 1) ^ (lexp_to_stri 1 lbody)

        | Cons(t, (_, ctor_name)) ->
            (keyword "inductive-cons ") ^ (lexp_to_str t) ^ " " ^ ctor_name

        | Call(fname, args) -> (
            (*  get function name *)
            let str, idx, inner_parens, outer_parens = match fname with
                | Builtin ((_, name), _, _) -> name,  0,  false, true
                | Var((_, name), idx)    -> name, idx, false, true
                | Lambda _               -> "__",  0,  true,  false
                | Cons _                 -> "__",  0,  false, false
                | _                      -> "__", -1,  true,  true  in

            let binop_str op (_, lhs) (_, rhs) =
                (lexp_to_str lhs) ^ op ^ (index idx) ^ " " ^ (lexp_to_str rhs) in

            let add_parens bl str =
                if bl then "(" ^ str ^ ")" else str in

            match (str, args) with
                (* Special Operators *)
                (* FIXME: Get rid of these special cases:
                 * Either use the boring (_+_ e1 e2) notation, or check the
                 * grammar to decide when we can use the infix notation and
                 * when to add parenthese.  *)
                | ("_=_", [lhs; rhs]) -> binop_str " =" lhs rhs
                | ("_+_", [lhs; rhs]) -> binop_str " +" lhs rhs
                | ("_-_", [lhs; rhs]) -> binop_str " -" lhs rhs
                | ("_/_", [lhs; rhs]) -> binop_str " /" lhs rhs
                | ("_*_", [lhs; rhs]) -> binop_str " *" lhs rhs
                (* not an operator *)
                | _ ->
                    let args = List.fold_left
                                 (fun str (_, lxp)
                                  -> str ^ " " ^ (lexp_to_str lxp))
                                 "" args in

                    let str = fun_call (lexp_to_str fname) in
                    let str = add_parens inner_parens str in
                    let str = str ^ args in
                        add_parens outer_parens str)

        | Inductive (_, (_, name), [], ctors) ->
            (keyword "inductive_") ^ " (" ^ name ^") " ^
                                            (lexp_str_ctor ctx ctors)

        | Inductive (_, (_, name), args, ctors)
          -> let args_str
              = List.fold_left
                  (fun str (arg_kind, (_, name), ltype)
                   -> str ^ " (" ^ name ^ " " ^ (kindp_str arg_kind) ^ " "
                     ^ (lexp_to_str ltype) ^ ")")
                  "" args in

            (keyword "inductive_") ^ " (" ^ name ^ args_str ^") "
            ^ (lexp_str_ctor ctx ctors)

        | Case (_, target, _ret, map, dflt) ->(
            let str = (keyword "case ") ^ (lexp_to_str target)
            (* FIXME: `tpe' is the *base* type of `target`.  E.g. if `target`
             * is a `List Int`, then `tpe` will be `List`.
               ^ * " : " ^ (lexp_to_str tpe) *) in
            let arg_str arg
              = List.fold_left (fun str v
                                -> match v with
                                  | (_,None) -> str ^ " _"
                                  | (_, Some (_, n)) -> str ^ " " ^ n)
                               "" arg in

            let str = SMap.fold (fun k (_, arg, exp) str ->
                str ^ nl ^ (make_indent 1) ^
                    "| " ^ (fun_call k) ^ (arg_str arg) ^ " => " ^ (lexp_to_stri 1 exp))
                map str in

            match dflt with
                | None -> str
                | Some (v, df) ->
                   str ^ nl ^ (make_indent 1)
                   ^ "| " ^ (match v with None -> "_" | Some (_,name) -> name)
                   ^ " => " ^ (lexp_to_stri 1 df))

        | Builtin ((_, name), _, _) -> name

        | Sort (_, Stype (SortLevel SLz)) -> "Type_0"
        | Sort (_, Stype _) -> "Type_?"
        | Sort (_, StypeOmega) -> "Type_ω"
        | Sort (_, StypeLevel) -> "Type_Level"

        | SortLevel (SLz) -> "<Level0>"
        | SortLevel (SLsucc e) -> "<LevelS?>"

and lexp_str_ctor ctx ctors =
  SMap.fold (fun key value str
             -> let str = str ^ " (" ^ key in
               let str = List.fold_left (fun str (k, _, arg)
                                         -> str ^ " " ^ (_lexp_to_str ctx arg))
                                        str value in
               str ^ ")")
            ctors ""

and _lexp_str_decls ctx decls =

    let (pretty, indent, ptype, pindex, sepdecl, isize, _) = ctx in
    let lexp_to_str = _lexp_to_str ctx in

    (* let make_indent idt =
        if pretty then (make_line ' ' ((idt + indent) * isize)) else "" in *)

    let sepdecl = (if sepdecl then "\n" else "") in

    let type_str name lxp = (if ptype then (
         name ^ " : " ^ (lexp_to_str lxp) ^ ";") else "") in

    let ret = List.fold_left
                (fun str ((_, name), lxp, ltp)
                 -> let str = if ptype then (type_str name ltp)::str else str in
                   (name ^ " = " ^ (lexp_to_str lxp) ^ ";" ^ sepdecl)::str)
                [] decls in
    List.rev ret
