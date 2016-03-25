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
]

(* Make lxp context with built-in types *)
let default_lctx =
    (* Empty context *)
    let lctx = make_lexp_context in

    (* populate ctx *)
    List.fold_left (fun ctx (name, lxp) ->
        let ctx = senv_add_var name dloc ctx in
            env_add_var_info (0, (dloc, name), lxp, lxp) ctx)
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
            let bdy = lexp_parse body (local_scope nctx (get_roffset nctx)) in
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

        (*  *)
        | Plambda (kind, var, Some ptype, body) ->
            (*  Add argument to context *)
            let (loc, vname) = var in
            let ltp = lexp_parse ptype ctx in   (*  Get Type *)

            let nctx = senv_add_var vname loc ctx in
            let nctx = env_add_var_info (0, (loc, vname), dlxp, ltp) nctx in

            let ltyp = lexp_parse ptype nctx in

            let nctx = (local_scope nctx (get_roffset nctx)) in
            let lbody = lexp_parse body nctx in
                Lambda(kind, var, ltyp, lbody)

        | Plambda (kind, var, None, body) ->
            let (loc, vname) = var in

            let nctx = senv_add_var vname loc ctx in
            let nctx = env_add_var_info (0, (loc, vname), dlxp, dltype) nctx in

            let nctx = (local_scope nctx (get_roffset nctx)) in
            let lbody = lexp_parse body nctx in
            Lambda(kind, var, UnknownType(tloc), lbody)

        | Pcall (fname, _args) ->
            lexp_call fname _args ctx i

        (* Pinductive *)
        | Pinductive (label, [], ctors) ->
            let map_ctor, nctx = lexp_parse_constructors ctors ctx i in
                Inductive(tloc, label, [], map_ctor)

        (* Pcons *)
        | Pcons(vr, sym) -> (
            let (loc, type_name) = vr in
            let (_, ctor_name) = sym in
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
            (* Exit case, send back old context *)
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
        (*  I think this should not modify context.
         *  if so, funny things might happen when evaluating *)
        let fname = lexp_parse fname ctx in
        Call(fname, new_args) end

(*  Read a pattern and create the equivalent representation *)
and lexp_read_pattern pattern exp target ctx:
          ((string * location * (arg_kind * vdef) option list) * lexp_context) =

    match pattern with
        | Ppatany (loc) ->            (* Catch all expression nothing to do  *)
            ("_", loc, []), ctx

        | Ppatvar (loc, name) ->(
            (* FIXME better check *)
            try
                let idx = senv_lookup name ctx in
                    (* constructor with no args *)
                    (name, loc, []), ctx

            (* would it not make a default match too? *)
            with Not_found ->
                (* Create a variable containing target *)
                let nctx = senv_add_var name loc ctx in
                let nctx = env_add_var_info (0, (loc, name), target, dltype) nctx in
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
                    | Ppatvar (loc, name) ->
                        (*  Add var *)
                        let nctx = senv_add_var name loc ctx in
                        let nctx = env_add_var_info (0, (loc, name), dlxp, dltype) nctx in
                        let nacc = (Some (Aexplicit, (loc, name)))::acc in
                            loop tl nacc nctx
                    | _ -> lexp_error dloc "Constructor inside a Constructor";
                           loop tl (None::acc) ctx)

    in loop args [] ctx

(*  Parse inductive constructor *)
and lexp_parse_constructors ctors ctx i =
    let lexp_parse p ctx = _lexp_parse p ctx (i + 1) in
    let make_args (args:(arg_kind * pvar option * pexp) list):
                                       (arg_kind * ltype) list * lexp_context =
        let rec loop args acc ctx =
            match args with
                | [] -> (List.rev acc), ctx
                | hd::tl -> begin
                    match hd with
                        (* What does the optional Pvar do ?
                                        that expression does not exist in LEXP*)
                        | (kind, _, exp) ->
                        let lxp = lexp_parse exp ctx in
                        loop tl ((kind, lxp)::acc) ctx end in
        loop args [] ctx in

    let rec loop ctors merged ctx =
        match ctors with
            | [] -> merged, ctx
            | hd::tl -> begin
                match hd with
                    | ((loc, name), args) ->
                        let largs, nctx = make_args args in
                        let nmerged = SMap.add name largs merged in
                        loop tl nmerged ctx
            end in

    loop ctors SMap.empty ctx

(*  Parse let declaration *)
and lexp_decls decls ctx: (((vdef * lexp * ltype) list) * lexp_context) =
    let lexp_parse p ctx = _lexp_parse p ctx 1 in
    (*  Merge Type info and declaration together                      *)
    (* merge with a map to guarantee uniqueness. *)
    let rec merge_decls (decls: (pvar * pexp * bool) list) merged acc:
                ((location * pexp option * pexp option) SMap.t * string list)  =

        (*  we cant evaluate here because variable are not in the environment *)
        match decls with
            | [] -> merged, (List.rev acc)
            | hd::tl ->
                match hd with
                (*  Type Info: Var:Type *)
                | ((loc, name), type_info, true) -> begin
                    try
                        (*  If found its means the instruction was declared
                         *  before the type info. Should we allow this? *)
                        let (l, inst, _) = SMap.find name merged in
                        let new_decl = (l, inst, Some type_info) in
                        let nmerged = SMap.add name new_decl merged in
                            (merge_decls tl nmerged acc)
                    with Not_found ->
                        let new_decl = (loc, None, Some type_info) in
                        let nmerged = SMap.add name new_decl merged in
                        (merge_decls tl nmerged (name::acc)) end

                (* Instruction: Var = expr *)
                | ((loc, name), inst, false) -> begin
                    try
                        let (l, _, tp) = SMap.find name merged in
                        let new_decl = (l, Some inst, tp) in
                        let nmerged = SMap.add name new_decl merged in
                            (merge_decls tl nmerged acc)

                    with Not_found ->
                        let new_decl = (loc, Some inst, None) in
                        let nmerged = SMap.add name new_decl merged in
                        (merge_decls tl nmerged (name::acc)) end in

    let mdecls, ord = merge_decls decls SMap.empty [] in

    (* cast map to list to preserve declaration order *)
    let decls = List.map (fun name ->
            let (l, inst, tp) = SMap.find name mdecls in
                ((l, name), inst, tp) ) ord
        in

    (*  Add Each Variable to the environment *)
    let nctx = List.fold_left (fun ctx hd ->
        match hd with
            | (_, None, _) -> ctx   (*  Unused variable: No Instruction *)
            | ((loc, name), _, _) -> senv_add_var name loc ctx)
        ctx decls in

    let n = (List.length decls) - 1 in

    (*  Add Variable info *)
    let rec process_var_info dcl_lst _ctx acc m =
        match dcl_lst with
            | [] -> (List.rev acc), _ctx
            | hd::tl ->
                match hd with
                    | ((loc, name), Some pinst, None) ->(
                        let nctx = local_scope _ctx m in
                        let lxp, ltp = lexp_p_infer pinst nctx in
                        let nacc = ((loc, name), lxp, ltp)::acc in
                        let ctx2 = env_add_var_info (0, (loc, name), lxp, ltp) nctx in
                            process_var_info tl ctx2 nacc (m - 1))

                    | ((loc, name), Some pinst, Some ptype) ->(
                        let nctx = local_scope _ctx m in
                        let linst  = lexp_parse pinst nctx in
                        let ltyp = lexp_parse ptype nctx in
                        let nacc = ((loc, name), linst, ltyp)::acc in
                        let ctx3 = env_add_var_info (0, (loc, name), linst, ltyp) nctx in
                            process_var_info tl ctx3 nacc (m - 1))

                    (* Skip the variable *)
                    | ((loc, name), None, _) -> (lexp_warning loc "Unused Variable";
                            process_var_info tl _ctx acc m) in

    let acc, ctx = process_var_info decls nctx [] n in
        acc, ctx

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

    (* determine type *)
    match lxp with
        (* Trivial *)
        | Imm (sxp) -> (
            match sxp with
                | Integer _ -> (lxp, type_int)
                | Float _ -> (lxp, type_float)
                | _ -> lexp_error tloc "Could not infer type";
                    (lxp, UnknownType(tloc)))

        | Var v ->
            let ltp = env_lookup_type env v in
                (lxp, ltp)

        (*
        | PCall(pxp_name, sxp_args) ->(
            (* Get function Type (x -> y) *)
            let lxp, ltp = lexp_p_infer pxp_name env in
            (* TODO check arg types *)
                (lxp, ltp))

        | Plet (_, decls, body) ->
            let _, env = lexp_decls decls env in
            let lxp, ltp = lexp_p_infer body env in
                (lxp, ltp)

        | *)

        (* Pinductive *)
        (* PCons return its Pinductive type *)

        (* Plambda *)
        (* we need to build (t0 -> ... -> tn) *)

        (* PCase *)
        (* return target type *)

        (**)

        (* dev catch all *)
        | _ -> (lxp, UnknownType(dloc))


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

        | Arrow(kind, Some (_, name), tp, loc, expr) ->
            slexp_print tp; print_string ": "; print_string name;
            print_string " -> "; slexp_print expr;

        | Arrow(kind, None, tp, loc, expr) ->
            slexp_print tp; print_string " -> "; slexp_print expr;

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
            List.iter (fun (kind, arg) ->
                lexp_print_adv opt arg; print_string " ") value;
            print_string ")")
        ctors

and lexp_print_decls opt decls =
    let (pty, indent, prtp) = opt in
    let print_type nm tp =
        print_string (" " ^ nm ^  ": "); lexp_print_adv opt tp;
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

    print_string (make_title " LEXP CONTEXT ");

    make_rheader [
        (Some ('r', 10), "NAME");
        (Some ('r',  7), "INDEX");
        (Some ('r', 10), "NAME");
        (Some ('r', 20), "VALUE:TYPE")];

    print_string (make_sep '-');

    StringMap.iter (fun key idx ->
        (* Print senv info *)
        print_string "    | ";
        ralign_print_string key 10;
        print_string " | ";
        ralign_print_int (n - idx - 1) 7;
        print_string " | ";

        (*  Print env Info *)
        try let (_, (_, name), exp, tp) = env_lookup_by_index (n - idx - 1) ctx in
            ralign_print_string name 10; (*   name must match *)
            print_string " | ";
            lexp_print_adv (false, 0, true) exp;
            print_string ": ";
            lexp_print_adv (false, 0, true) tp;
            print_string "\n"
        with
            Not_found -> print_string "Not_found \n")

        map;

    print_string (make_sep '=');

and print_lexp_trace () =
    print_trace " LEXP TRACE " 50 pexp_to_string pexp_print !_global_lexp_trace

(*  Only print var info *)
and lexp_print_var_info ctx =
    let ((_, _), env) = ctx in
    let n = Myers.length env in

    for i = 0 to n - 1 do (
        let (_, (_, name), exp, tp) = Myers.nth i env in
        print_string name; (*   name must match *)
        print_string " = ";
        lexp_print_adv (false, 0, true) exp;
        print_string ": ";
        lexp_print_adv (false, 0, true) tp;
        print_string "\n")
    done;
;;


let lexp_parse_all p ctx = _lexp_parse_all p ctx 1;;
let lexp_print e = lexp_print_adv (false, 0, true) e;;


(* add dummy definition helper *)
let add_def name ctx =
    let ctx = senv_add_var name dloc ctx in
    env_add_var_info (0, (dloc, name), dlxp, dlxp) ctx
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
