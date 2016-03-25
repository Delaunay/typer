(*
 *      Typer Compiler
 *
 * ---------------------------------------------------------------------------
 *
 *      Copyright (C) 2011-2016  Free Software Foundation, Inc.
 *
 *   Author: Pierre Delaunay <pierre.delaunay@hec.ca>
 *   Keywords: languages, lisp, dependent types.
 *
 *   This file is part of Typer.
 *
 *   Typer is free software; you can redistribute it and/or modify it under the
 *   terms of the GNU General Public License as published by the Free Software
 *   Foundation, either version 3 of the License, or (at your option) any
 *   later version.
 *
 *   Typer is distributed in the hope that it will be useful, but WITHOUT ANY
 *   WARRANTY; without even the implied warranty of MERCHANTABILITY or FITNESS
 *   FOR A PARTICULAR PURPOSE.  See the GNU General Public License for
 *   more details.
 *
 *   You should have received a copy of the GNU General Public License along
 *   with this program.  If not, see <http://www.gnu.org/licenses/>.
 *
 * ---------------------------------------------------------------------------
 *
 *      Description:
 *          parse pexp expression into lexp
 *
 * --------------------------------------------------------------------------- *)

open Util
open Sexp
open Pexp
open Lexp
open Grammar
open Debruijn
open Fmt

open Lexer
open Prelexer

(* Shortcut => Create a Var *)
let make_var name index loc =
    Var(((loc, name), index))
;;

let not_implemented_error () =
    internal_error "not implemented"
;;

let dlxp = UnknownType(dloc)
let dltype = UnknownType(dloc)
let dloc = dummy_location

let lexp_warning = msg_warning "LEXP"
let lexp_error = msg_error "LEXP"
let lexp_fatal loc msg =
    msg_error "LEXP" loc msg;
    raise (internal_error msg)
;;


module StringSet
    = Set.Make (struct type t = string let compare = String.compare end)
;;

              (*  pretty ? * indent level * print_type? *)
type print_context = (bool * int * bool)

(* Built-in list of types/functions *)
let lexp_builtins = [
(*    NAME  |     LXP               *)
    ("Int"  , type_int);
    ("Float", type_float);
    ("_=_"  , type_eq);    (*  t  ->  t  -> bool *)
    ("_+_"  , iop_binary); (* int -> int -> int  *)
    ("_*_"  , iop_binary); (* int -> int -> int  *)
]

(* Make lxp context with built-in types *)
let default_lctx () =
    (* Empty context *)
    let lctx = make_lexp_context in

    (* populate ctx *)
    List.fold_left
      (fun ctx (name, lxp) ->
        let var = (dloc, name) in
        let ctx = senv_add_var var ctx in
        env_add_var_info (0, var, None, lxp) ctx)
      lctx
      lexp_builtins
;;

let _global_lexp_ctx = ref make_lexp_context;;
let _global_lexp_trace = ref []

(*  The main job of lexp (currently) is to determine variable name (index)
 *  and to regroup type specification with their variable
 *
 *  lexp_context is composed of two environment: senv and env.
 *  the senv environment is used to find the correct debruijn index
 *  while the env environment is used to save variable information.
 *  the env environment look a lot like the runtime environment that will be
 *  used in the eval section.
 *
 *  While most of the time senv and env will be synchronised it is
 *  possible for env to hold more variables than senv since senv is a map
 *  which does not allow multiple definition while env does.
 *
 *)

let rec lexp_parse (p: pexp) (ctx: lexp_context): lexp =
    _lexp_parse p ctx 1

and _lexp_parse p ctx i: lexp =

    let lexp_parse p ctx = _lexp_parse p ctx (i + 1) in
    let tloc = pexp_location p in

    _global_lexp_ctx := ctx;
    _global_lexp_trace := (i, tloc, p)::!_global_lexp_trace;

    match p with
        (*  Block/String/Integer/Float *)
        | Pimm value -> Imm(value)

        (*  Symbol i.e identifier *)
        | Pvar (loc, name) -> begin
            try
                (*  Send Variable loc *)
                let idx = senv_lookup name ctx in
                    (make_var name idx loc)

            with Not_found ->
                (lexp_error loc ("The Variable: " ^ name ^ " was not declared");
                (* Error recovery. The -1 index will raise an error later on *)
                (make_var name (-1) loc))  end

        (*  Let, Variable declaration + local scope *)
        | Plet(loc, decls, body) ->
            let decl, nctx = lexp_decls decls ctx in
            let bdy = lexp_parse body nctx in
            Let(tloc, decl, bdy)

        (* ->/=> *)
        | Parrow (kind, Some var, tp, loc, expr) ->
            let nvar = var in               (* /!\ HERE *)
            let ltyp = lexp_parse tp ctx in
            let lxp = lexp_parse expr ctx in
            Arrow(kind, Some nvar, ltyp, tloc, lxp)

        | Parrow (kind, None, tp, loc, expr) ->
            let ltyp = lexp_parse tp ctx in
            let lxp = lexp_parse expr ctx in
                Arrow(kind, None, ltyp, tloc, lxp)

        | Plambda (kind, var, pt, body) ->
           let tctx = env_extend ctx var None dltype in
           let ltp = match pt with
             | None -> dltype
             | Some pt -> lexp_parse pt tctx in
           let nctx = env_extend ctx var None ltp in
           let lbody = lexp_parse body nctx in
            Lambda(kind, var, ltp, lbody)

        | Pcall (fname, _args) ->
            lexp_call fname _args ctx i

        (* Pinductive *)
        | Pinductive (label, [], ctors) ->
            let map_ctor = lexp_parse_inductive ctors ctx i in
            Inductive(tloc, label, [], map_ctor)

        (* Pcons *)
        | Pcons(vr, sym) -> (
            let (loc, type_name) = vr in
            (*  An inductive type named type_name must be in the environment *)
            try let idx = senv_lookup type_name ctx in
                (*  Check if the constructor exists *)
                            (* TODO *)
                Cons((vr, idx), sym)
            with Not_found ->
                lexp_error loc
                ("The inductive type: " ^ type_name ^ " was not declared");
                Cons((vr, -1), sym))

        (* Pcase *)
        | Pcase (loc, target, patterns) ->

            (*  I need type info HERE *)
            let lxp = lexp_parse target ctx in
            let ltp = UnknownType(loc) in

            (*  Read patterns one by one *)
            let rec loop ptrns merged dflt =
                match ptrns with
                    | [] -> merged, dflt
                    | hd::tl ->
                        let (pat, exp) = hd in
                        (*  Create pattern context *)
                        let (name, iloc, arg), nctx = lexp_read_pattern pat exp lxp ctx in
                        (*  parse using pattern context *)
                        let exp = lexp_parse exp nctx in

                        if name = "_" then
                            loop tl merged (Some exp)
                        else
                            let merged = SMap.add name (iloc, arg, exp) merged in
                            loop tl merged dflt in

            let (lpattern, dflt) = loop patterns SMap.empty None in
            Case(loc, lxp, ltp, lpattern, dflt)

        | _
            -> UnknownType(tloc)

(*  Identify Call Type and return processed call *)
and lexp_call (fname: pexp) (_args: sexp list) ctx i =
    (*  Process Arguments *)
    let pargs = List.map pexp_parse _args in

    (*  Call to named function which must have been defined earlier  *
     *          i.e they must be in the context                      *)
    begin try begin
        (*  Get function name *)
        let name, loc = match fname with
            | Pvar(loc, nm) -> nm, loc
            | Pcons (_, (loc, nm)) -> nm, loc
            | _ -> raise Not_found in

        let largs = _lexp_parse_all pargs ctx i in
        let new_args = List.map (fun g -> (Aexplicit, g)) largs in

        try
            (*  Check if the function was defined *)
            let idx = senv_lookup name ctx in
            let vf = (make_var name idx loc) in
                Call(vf, new_args)

        with Not_found ->
            (*  Don't stop even if an error was found *)
            lexp_error loc ("The function \"" ^ name ^
                                                  "\" was not defined");
            let vf = (make_var name (-1) loc) in
                Call(vf, new_args) end

    (*  Call to a nameless function *)
    with Not_found ->
        let largs = _lexp_parse_all pargs ctx i in
        let new_args = List.map (fun g -> (Aexplicit, g)) largs in
        let fname = _lexp_parse fname ctx (i + 1) in
            Call(fname, new_args) end

(*  Read a pattern and create the equivalent representation *)
and lexp_read_pattern pattern exp target ctx:
          ((string * location * (arg_kind * vdef) option list) * lexp_context) =

    match pattern with
        | Ppatany (loc) ->            (* Catch all expression nothing to do  *)
            ("_", loc, []), ctx

        | Ppatvar ((loc, name) as var) ->(
            (* FIXME better check *)
            try
                let _ = senv_lookup name ctx in
                    (* constructor with no args *)
                    (name, loc, []), ctx

            (* would it not make a default match too? *)
            with Not_found ->
                (* Create a variable containing target *)
                let nctx = env_extend ctx var (Some target) dltype in
                    (name, loc, []), nctx)

        | Ppatcons (ctor_name, args) ->
            let (loc, name) = ctor_name in

            (* read pattern args *)
            let args, nctx = lexp_read_pattern_args args ctx in
                (name, loc, args), nctx

(*  Read patterns inside a constructor *)
and lexp_read_pattern_args args ctx:
                   (((arg_kind * vdef) option list) * lexp_context)=

    let rec loop args acc ctx =
        match args with
            | [] -> (List.rev acc), ctx
            | hd::tl -> (
                let (_, pat) = hd in
                match pat with
                    (* Nothing to do *)
                    | Ppatany (loc) -> loop tl (None::acc) ctx
                    | Ppatvar ((loc, name) as var) ->
                        (*  Add var *)
                        let nctx = env_extend ctx var None dltype in
                        let nacc = (Some (Aexplicit, var))::acc in
                            loop tl nacc nctx
                    | _ -> lexp_error dloc "Constructor inside a Constructor";
                           loop tl (None::acc) ctx)

    in loop args [] ctx

(*  Parse inductive type definition.  *)
and lexp_parse_inductive ctors ctx i =
    let lexp_parse p ctx = _lexp_parse p ctx (i + 1) in
    let make_args (args:(arg_kind * pvar option * pexp) list) ctx
        : (arg_kind * vdef option * ltype) list =
        let rec loop args acc ctx =
            match args with
                | [] -> (List.rev acc)
                | hd::tl -> begin
                    match hd with
                    | (kind, var, exp) ->
                       let lxp = lexp_parse exp ctx in
                       match var with
                         | None -> loop tl ((kind, None, lxp)::acc) ctx
                         | Some (var) ->
                            let nctx = env_extend ctx var None dltype in
                            loop tl ((kind, Some var, lxp)::acc) nctx
                  end in
        loop args [] ctx in

    List.fold_left
      (fun lctors ((_, name), args) ->
        SMap.add name (make_args args ctx) lctors)
      SMap.empty ctors

(*  Parse let declaration *)
and lexp_decls decls ctx: (((vdef * lexp * ltype) list) * lexp_context) =
    (* The new implementation suppose that forward declarations are
     * used when mutually recursive type are declared.
     * old implementation was going through declaration 4 times
     * now everything is done by going through them once            *)
    let lexp_parse p ctx = _lexp_parse p ctx 1 in
    let m = (List.length decls) + (get_size ctx) in

    (* Make it look like we processed all declarations once already*)
    let forge_ctx ctx n =
        let ((m, map), a, b) = ctx in
            ((n, map), a, b) in

    let iter_fun (idx, ctx, sset, acc) elem =
        let ((loc, name), pxp, bl) = elem in (
            (* Process Type *)
            if bl then (
                (* Temporary extend *)
                (* type info must be present for recursive call  *)
                let tctx = env_extend ctx (loc, name) None dltype in
                let ltp = lexp_parse pxp (forge_ctx tctx m) in

                let ctx = env_extend ctx (loc, name) None ltp in
                let sset = StringMap.add name ltp sset in
                    (idx + 1, ctx, sset, acc)
            )
            (* Process instruction *)
            else(
                (* Type annotations was provided *)
                try
                    let ltp = StringMap.find name sset in
                    (* Type check *)
                    let lxp = lexp_p_check pxp ltp (forge_ctx ctx m) in
                        (idx + 1, ctx, sset, ((loc, name), lxp, ltp)::acc)

                (* No Type annotations *)
                with Not_found ->
                    let tctx = env_extend ctx (loc, name) None dltype in
                    let lxp, ltp = lexp_p_infer pxp (forge_ctx tctx m) in

                    let ctx = env_extend ctx (loc, name) (Some lxp) ltp in
                        (idx + 1, ctx, sset, ((loc, name), lxp, ltp)::acc))
            ) in

    let (n, nctx, _, decls) = List.fold_left iter_fun
        (0, ctx, StringMap.empty, []) decls in
        (* NB: if some var x was type annotated then it does not have
         * a "value" in the env. A second pass through the declaration could
         * solve this. Nevertheless, I not sure if it is truly useful *)
        (List.rev decls), nctx

and _lexp_parse_all (p: pexp list) (ctx: lexp_context) i : lexp list =

    let rec loop (plst: pexp list) ctx (acc: lexp list) =
        match plst with
            | [] -> (List.rev acc)
            | _  -> let lxp = _lexp_parse (List.hd plst) ctx (i + 1) in
                    (loop (List.tl plst) ctx (lxp::acc)) in

    (loop p ctx [])

(*
 *      Free Variables
 * --------------------- *)
(** Return a list of all free variables contained in an expression lxp *)

(* Tree Nodes that make reference to declarations are:
 *  Call/Var/Cons
 *)

(* free_var should use a lexp since we are going to need free_v during eval *)
and free_variable pxp =
(* Expression that can have free variables:
 *      - Lambda
 *      - Let
 *      - Call
 * Expression that can be free variables:
 *      - Var/ Function (Call)                                  *)

    let bound = StringSet.empty in       (* bound variables  *)
    let free = ([], StringSet.empty) in  (* decl order * map *)

    let rec _fv pxp (bound, free) =
        match pxp with
            | Plambda (_, (_, name), _, body) ->
                let bound = StringSet.add name bound in
                    _fv body (bound, free)

            (*
            | Plet (_, args, body) ->

                let bound = List.fold_left
                    (fun s ((_, name), _, _) -> StringSet.add name s) bound args in
                        _fv body bound free *)

            | Pcall (xp, lst) ->
                (* check if function is declared outside *)
                let (bound, free) = _fv xp (bound, free) in
                let pargs = List.map pexp_parse lst in
                    (* check for fv inside call args *)
                    List.fold_left (fun a g -> _fv g a) (bound, free) pargs

            | Pvar (_, name) ->(
                try let _ = StringSet.find name bound in
                    (bound, free)
                with
                    Not_found ->(
                        let (arr, set) = free in
                            try let _ = StringSet.find name set in
                                (bound, free)
                            with
                                Not_found ->(
                                    let set = StringSet.add name set in
                                    let arr = name :: arr in
                                        (bound, (arr, set)))))
            | _ -> (bound, free) in

    let (bound, (afree, sfree)) = _fv pxp (bound, free) in
        (bound, (List.rev afree, sfree))


(*
 *      Type Inference
 * --------------------- *)
(* Parsing a Pexp into an Lexp is really "elaboration", i.e. it needs to
 * infer the types and perform macro-expansion.  For won't really
 * do any of that, but we can already start structuring it accordingly.
 *
 * More specifically, we do it with 2 mutually recursive functions:
 * one takes a Pexp along with its expected type and return an Lexp
 * of that type (hopefully), whereas the other takes a Pexp and
 * infers its type (which it returns along with the Lexp).
 * This is the idea of "bidirectional type checking", which minimizes
 * the amount of "guessing" and/or annotations.  Basically guessing/annotations
 * is only needed at those few places where the code is not fully-normalized,
 * which in normal programs is only in "let" definitions.
 * So the rule of thumbs are:
 * - use lexp_p_infer for destructors, and use lexp_p_check for constructors.
 * - use lexp_p_check whenever you can.
 *)

and lexp_p_infer (p : pexp) (env : lexp_context): lexp * ltype =

    (* Parse expr *)
    let tloc = pexp_location p in
    let lxp = lexp_parse p env in

    let rec get_return_type lxp =
        match lxp with
            | Arrow(_, _, _, _, ret_type) -> (get_return_type ret_type)
            | _ -> lxp in

    let rec get_type lxp ctx =
        match lxp with
            (* Leafs        *)
            (* ------------ *)
            | Var vrf -> env_lookup_type ctx vrf
            | Cons (vrf, _) -> env_lookup_type ctx vrf
            | Imm sxp -> (match sxp with
                (* FIXME use the ones that are already in the ctx *)
                | Integer _ -> type_int
                | Float _ -> type_float
                | _ -> lexp_error tloc "Could not infer type"; dltype)

            (* Types by definition *)
            | Inductive _ -> lxp
            | Builtin (_, _, ltp) -> ltp
            | Arrow _ -> lxp
            | UnknownType _ -> lxp

            (* Nodes        *)
            (* ------------ *)
            | Let (_, _, body) -> (get_type body ctx)
            | Call(f, _) ->
                (* FIXME: check arg and f type are compatible *)
                (* FIXME: call cannot be partial *)
                (get_return_type (get_type f ctx))

            (* we need to check that all branches return the same type *)
            | Case (_, _, _, branches, dflt) ->(
                (* FIXME *)
                match dflt with
                    | None -> lexp_error tloc "Could not infer type"; dltype
                    | Some expr -> (get_type expr ctx))

            | Lambda (kind, vdef, ltp, lxp) ->
                let nctx = env_extend ctx vdef (Some ltp) lxp in
                Arrow(kind, Some vdef, (get_type ltp nctx), tloc,
                                       (get_type lxp nctx))

            (* debug catch all *)
            | _ ->  print_string
                    ("Catch all was used by: " ^ (lexp_to_string lxp) ^ "\n");
                dltype in

        (lxp, (get_type lxp env))


and lexp_p_check (p : pexp) (t : ltype) (env : lexp_context): lexp =
  match p with
  | _
    -> let (e, inferred_t) = lexp_p_infer p env in
      (* FIXME: check that inferred_t = t!  *)
      e
(*
 *      Printing
 * --------------------- *)
(* FIXME: transform to lexp_to_buffer *)
and lexp_print_adv opt exp =

    let slexp_print = lexp_print_adv opt in (* short_lexp_print *)
    let (pty, indent, prtp) = opt in
    match exp with
        | Imm(value)             -> sexp_print value
        | Var ((loc, name), idx) ->
            print_string name;
            print_string "["; print_int idx; print_string "]"

        | Let (_, decls, body)   ->
            print_string "let"; lexp_print_decls (pty, indent + 1, prtp) decls;
            if pty then print_string (make_line ' ' (indent * 4 + 4));
            print_string " in "; lexp_print_adv (pty, indent + 2, prtp) body

        | Arrow(kind, Some (_, name), tp, loc, expr) -> print_string "(";
            lexp_print_type opt tp; print_string ": "; print_string name; print_string ")";
            print_string " -> "; lexp_print_type opt expr;

        | Arrow(kind, None, tp, loc, expr) ->
            lexp_print_type opt tp; print_string " -> "; lexp_print_type opt expr;

        | Lambda(kind, (loc, name), ltype, lbody) ->
            print_string "lambda ("; print_string (name ^ ": ");
            slexp_print ltype; print_string ") -> "; slexp_print lbody;

        | Cons(vf, symbol) ->
            let (loc, name) = symbol in
            let ((loc, vname), idx) = vf in
                print_string (name ^ "("); print_string vname;
                print_string "["; print_int idx; print_string "])"

        | Call(fname, args) -> begin  (*  /!\ Partial Print *)
            (*  get function name *)
            let str, idx = match fname with
                | Var((_, name), idx) -> name, idx
                | _ -> "unkwn", -1 in

            let print_arg arg = match arg with | (kind, lxp) ->
                 lexp_print_adv (pty, 0, prtp) lxp in

            let print_binop op lhs rhs =
                print_arg lhs; print_string op; print_arg rhs in

            match (str, args) with
                (* Special Operator *)
                | ("_=_", [lhs; rhs]) -> print_binop " = " lhs rhs
                | ("_+_", [lhs; rhs]) -> print_binop " + " lhs rhs
                | ("_-_", [lhs; rhs]) -> print_binop " - " lhs rhs
                | ("_/_", [lhs; rhs]) -> print_binop " / " lhs rhs
                | ("_*_", [lhs; rhs]) -> print_binop " * " lhs rhs
                (* not an operator *)
                | _ ->
                    print_string ("(" ^ str ^ "["); print_int idx; print_string "]";
                    List.iter (fun arg -> print_string " "; print_arg arg) args;
                    print_string ")" end

        | Inductive (_, (_, name), _, ctors) ->
            print_string ("inductive_ " ^ name ^ " ");
            lexp_print_ctors opt ctors;

        | Case (_, target, tpe, map, dflt) -> begin
            print_string "case "; slexp_print target;
            print_string ": "; slexp_print tpe;

            if pty then print_string "\n";

            let print_arg arg =
                 List.iter (fun v ->
                    match v with
                        | None -> print_string " _"
                        | Some (kind, (l, n)) -> print_string (" " ^ n)) arg in

            SMap.iter (fun key (loc, arg, exp) ->
                print_string (make_line ' ' (indent * 4));
                print_string ("| " ^ key); print_arg arg;
                print_string " -> ";
                slexp_print exp; print_string "; ";
                if pty then print_string "\n";)
                map;

            match dflt with
                | None -> ()
                | Some df ->
                    print_string (make_line ' ' (indent * 4));
                    print_string "| _ -> "; slexp_print df;
                    print_string ";"; if pty then print_string "\n"; end

        | Builtin (tp, name, lxp) ->
            print_string name;

        (* debug catch all *)
        | UnknownType (loc)      -> print_string "unkwn";
        | _ -> print_string "Printing Not Implemented"


and lexp_print_ctors opt ctors =
    SMap.iter (fun key value ->
            print_string ("(" ^ key ^ ": ");
            List.iter (fun (kind, _, arg) ->
                lexp_print_adv opt arg; print_string " ") value;
            print_string ")")
        ctors

and lexp_print_type opt ltp =
    let (_, _, prtp) = opt in
    match ltp with
        | Inductive(_, (_, l), _, _) -> print_string l;
        | _ -> lexp_print_adv opt ltp

and lexp_print_decls opt decls =
    let (pty, indent, prtp) = opt in
    let print_type nm tp =
        print_string (" " ^ nm ^  ": "); lexp_print_type opt tp;
        print_string ";"; in

    List.iteri (fun idx g -> match g with
        | ((loc, name), expr, ltyp) ->
            if pty && idx > 0 then print_string (make_line ' ' (indent * 4));
            if prtp then print_type name ltyp; print_string " ";
            print_string (name ^ " = ");
            lexp_print_adv opt expr; print_string ";";
            if pty then print_string "\n")
        decls

(*  Print context  *)
and print_lexp_ctx ctx =
    let ((n, map), env, f) = ctx in
    let dv_size = n in                (* Number of declared Variables       *)
    let ti_size = Myers.length env in (* Number of variables with type info *)
    let sync_offset = dv_size - ti_size in

    print_string (make_title " LEXP CONTEXT ");

    make_rheader [
        (Some ('l', 10), "NAME");
        (Some ('l',  7), "INDEX");
        (Some ('l', 10), "NAME");
        (Some ('l', 36), "VALUE:TYPE")];

    print_string (make_sep '-');

    StringMap.iter (fun key idx ->
        (* Print senv info *)
        print_string "    | ";  lalign_print_string key 10;
        print_string    " | ";  lalign_print_int (n - idx - 1) 7;
        print_string    " | ";

        (*  Print env Info *)
        try let (_, (_, name), exp, tp) =
                        env_lookup_by_index (n - idx - 1 - sync_offset) ctx in

            lalign_print_string name 10; (*   name must match *)
            print_string " | ";
            (match exp with
             | None -> print_string "<var>"
             | Some exp -> lexp_print_adv (false, 0, true) exp);
            print_string ": ";
            lexp_print_type (false, 0, true) tp;
            print_string "\n"
        with
            Not_found -> print_string "Not_found  |\n")

        map;

    print_string (make_sep '=');

and print_lexp_trace () =
    print_trace " LEXP TRACE " 50 pexp_to_string pexp_print !_global_lexp_trace

(*  Only print var info *)
and lexp_print_var_info ctx =
    let ((m, _), env, _) = ctx in
    let n = Myers.length env in
    let sync_offset = m - n in

    for i = 0 to n - 1 do (
        let (_, (_, name), exp, tp) = Myers.nth i env in
        print_int i; print_string " ";
        print_string name; (*   name must match *)
        print_string " = ";
         (match exp with
             | None -> print_string "<var>"
             | Some exp -> lexp_print_adv (false, 0, true) exp);
        print_string ": ";
        lexp_print_adv (false, 0, true) tp;
        print_string "\n")
    done;
;;


let lexp_parse_all p ctx = _lexp_parse_all p ctx 1;;
let lexp_print e = lexp_print_adv (false, 0, true) e;;


(* add dummy definition helper *)
let add_def name ctx =
    let var = (dloc, name) in
    let ctx = senv_add_var var ctx in
    env_add_var_info (0, var, None, dlxp) ctx
;;


(*      String Parsing
 * ------------------------ *)

(* Lexp helper *)
let _lexp_expr_str (str: string) (tenv: bool array)
            (grm: grammar) (limit: string option) (ctx: lexp_context) =
    let pretoks = prelex_string str in
    let toks = lex tenv pretoks in
    let sxps = sexp_parse_all_to_list grm toks limit in
    let pxps = pexp_parse_all sxps in
        lexp_parse_all pxps ctx
;;

(* specialized version *)
let lexp_expr_str str lctx =
    _lexp_expr_str str default_stt default_grammar (Some ";") lctx
;;


let _lexp_decl_str (str: string) tenv grm limit ctx =
    let pretoks = prelex_string str in
    let toks = lex tenv pretoks in
    let sxps = sexp_parse_all_to_list grm toks limit in
    let pxps = pexp_decls_all sxps in
        lexp_decls pxps ctx
;;

(* specialized version *)
let lexp_decl_str str lctx =
    _lexp_decl_str str default_stt default_grammar (Some ";") lctx
;;
