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
open Fmt
open Myers

open Sexp
open Pexp
open Lexp

open Debruijn
open Eval

open Grammar
open Builtin

(* Shortcut => Create a Var *)
let make_var name index loc =
    Var(((loc, name), index))
;;

let dlxp = type0
let dltype = type0
let dloc = dummy_location

let lexp_warning = msg_warning "LPARSE"
let lexp_error = msg_error "LPARSE"
let lexp_fatal = msg_fatal "LPARSE"

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

(*
 * Infer: Imm, bultin, var, let, arrow, call, inductive, cons, case
 *
 * check: lambda
 *)
let rec lexp_p_infer (p : pexp) (ctx : lexp_context): lexp * ltype =
    _lexp_p_infer p ctx 1

and _lexp_p_infer (p : pexp) (ctx : lexp_context) i: lexp * ltype =

    let lexp_infer p ctx = _lexp_p_infer p ctx (i + 1) in
    let tloc = pexp_location p in

    _global_lexp_ctx := ctx;
    _global_lexp_trace := (i, tloc, p)::!_global_lexp_trace;

    match p with
        (*  Block/String/Integer/Float *)
        | Pimm value -> (Imm(value),
            match value with
                | Integer _ -> type_int
                | Float _ -> type_float
                | String _ -> lexp_error tloc "Could not find String"; dltype;
                | _ -> lexp_error tloc "Could not find type";
                        pexp_print p; print_string "\n"; dltype)

        (*  Symbol i.e identifier *)
        | Pvar (loc, name) ->(
            try let idx = senv_lookup name ctx in
                let lxp = (make_var name idx loc) in

                (* search type *)
                let ltp = env_lookup_type ctx ((loc, name), idx) in
                    lxp, ltp

            with Not_found ->
                (lexp_error loc ("The variable: \"" ^ name ^ "\" was not declared");
                (* Error recovery. The -1 index will raise an error later on *)
                (make_var name (-1) loc), dltype))

        (*  Let, Variable declaration + local scope *)
        | Plet(loc, decls, body) ->
            let decl, nctx = _lexp_decls decls ctx i in
            let bdy, ltp = lexp_infer body nctx in
                Let(tloc, decl, bdy), ltp

        (* ->/=> *)
        | Parrow (kind, Some var, tp, loc, expr) ->
            let nvar = var in               (* /!\ HERE *)
            let ltyp, _ = lexp_infer tp ctx in
            let lxp, _ = lexp_infer expr ctx in
            let v = Arrow(kind, Some nvar, ltyp, tloc, lxp) in
                v, v

        | Parrow (kind, None, tp, loc, expr) ->
            let ltyp, _ = lexp_infer tp ctx in
            let lxp, _ = lexp_infer expr ctx in
            let v = Arrow(kind, None, ltyp, tloc, lxp) in
                v, v

        | Plambda (kind, var, ptype, body) ->
            let ltp, _ = match ptype with
                | None -> dltype, dltype
                | Some pt -> lexp_infer pt ctx in

            let nctx = env_extend ctx var None ltp in
            let lbody, lbtp = lexp_infer body nctx in

            let lambda_type = Arrow(kind, None, ltp, tloc, lbtp) in
                Lambda(kind, var, ltp, lbody), lambda_type

        | Pcall (fname, _args) ->
            lexp_call fname _args ctx i

        (* Pinductive *)
        | Pinductive (label, [], ctors) ->
            let map_ctor = lexp_parse_inductive ctors ctx i in
            let v = Inductive(tloc, label, [], map_ctor) in
                v, v

        (* Pcons *)
        | Pcons(vr, sym) -> (
            let (loc, type_name) = vr in
            let (_, cname) = sym in

            (*  An inductive type named type_name must be in the environment *)
            try let idx = senv_lookup type_name ctx in
                (*  Check if the constructor exists *)
                let idt = env_lookup_type ctx (vr, idx) in

                (* make Base type *)
                let inductive_type = Var((loc, type_name), idx) in

                (* Get constructor args *)
                let args = match idt with
                    | Inductive(_, _, _, ctor_def) -> (
                        try (SMap.find cname ctor_def)
                        with Not_found ->
                            lexp_error loc
                                ("Constructor \"" ^ cname ^ "\" does not exist");
                                [])

                    | _ -> lexp_error loc "Not an Inductive Type"; [] in

                (* build Arrow type *)
                let cons_type = List.fold_left (fun ltp (kind, v, tp) ->
                    Arrow(kind, v, ltp, loc, tp)) inductive_type args in

                Cons((vr, idx), sym), cons_type

            with Not_found ->
                lexp_error loc
                ("The inductive type: " ^ type_name ^ " was not declared");
                Cons((vr, -1), sym), dltype)

        (* Pcase *)
        | Pcase (loc, target, patterns) ->

            let tlxp, tltp = lexp_infer target ctx in

            let uniqueness_warn name =
                lexp_warning loc ("Pattern " ^ name ^ " is a duplicate." ^
                                       " It will override previous pattern.") in

            let check_uniqueness loc name map = (
                try let _ = SMap.find name map in uniqueness_warn name
                with e -> ()) in

            (* FIXME: check if case is exhaustive  *)

            (* make a list of all branches return type *)
            let texp = ref [] in

            (*  Read patterns one by one *)
            let rec loop ptrns merged dflt =
                match ptrns with
                    | [] -> merged, dflt
                    | hd::tl ->
                        let (pat, exp) = hd in
                        (*  Create pattern context *)
                        let (name, iloc, arg), nctx = lexp_read_pattern pat exp tlxp ctx in
                        (*  parse using pattern context *)
                        let exp, ltp = lexp_infer exp nctx in
                            texp := ltp::!texp;

                        if name = "_" then (
                            (if dflt != None then uniqueness_warn name);
                            loop tl merged (Some exp))
                        else (
                            check_uniqueness iloc name merged;
                            let merged = SMap.add name (iloc, arg, exp) merged in
                            loop tl merged dflt) in

            let (lpattern, dflt) = loop patterns SMap.empty None in

            (* FIXME: check return types are equivalent *)
            let return_type = match (!texp), dflt with
                | hd::tl, Some _ -> hd
                | hd::tl, None -> hd
                | _, Some v -> v
                | _, None -> lexp_error loc "case with no branch ?"; dltype in

                Case(loc, tlxp, tltp, lpattern, dflt), (return_type)

        | _ -> lexp_fatal tloc "Unhandled Pexp"

and lexp_p_check (p : pexp) (t : ltype) (ctx : lexp_context) i: lexp =
    let tloc = pexp_location p in

    _global_lexp_ctx := ctx;
    _global_lexp_trace := (i, tloc, p)::!_global_lexp_trace;

    match p with
    | _ -> let (e, inferred_t) = _lexp_p_infer p ctx (i + 1) in
        (* FIXME: check that inferred_t = t!  *)
        e

(*  Identify Call Type and return processed call *)
and lexp_call (fname: pexp) (_args: sexp list) ctx i =
    (*  Process Arguments *)
    let pargs = List.map pexp_parse _args in
    let largs = _lexp_parse_all pargs ctx i in
    let new_args = List.map (fun g -> (Aexplicit, g)) largs in

    (* check if anonymous *)
    match fname with
        (* arg_kind * pvar * pexp option * pexp *)
        | Plambda _ -> let lbd, ltype = _lexp_p_infer fname ctx (i + 1) in
            Call(lbd, new_args), ltype

        | _ -> begin

    (* get function name *)
    let name, loc = match fname with
        | Pvar(loc, nm) -> nm, loc
        | Pcons (_, (loc, nm)) -> nm, loc
        | _->
            lexp_fatal (pexp_location fname) "This expression cannot be called" in

    (* retrieve function body *)
    let body, ltp = _lexp_p_infer fname ctx (i + 1) in

    try

    (*  Check if the function was defined *)
    let idx = senv_lookup name ctx in
    let vf = (make_var name idx loc) in

    (* consume Arrows and args together *)
    let rec get_return_type ltp args =
        match ltp, args with
            | _, [] -> ltp
            | Arrow(_, _, _, _, ltp), hd::tl -> (get_return_type ltp tl)
            | _, _ -> lexp_warning loc "Too many args"; ltp in

    let ret_type = get_return_type ltp new_args in

    (* Is the function built-in ? *)
    (* built-in cannot be partially applied that us why we can get_return_type *)
    (* they can only if you redefine the operation *)
    if (is_lbuiltin idx ctx) then (
        match env_lookup_expr ctx ((loc, name), idx) with
            | None -> lexp_error loc "Unknown builtin";
                Call(vf, new_args), ret_type
            | Some e -> Call(e, new_args), ret_type
    )
    else Call(vf, new_args), ret_type

    with Not_found ->
        (*  Don't stop even if an error was found *)
        lexp_error loc ("The function \"" ^ name ^ "\" was not defined");
        let vf = (make_var name (-1) loc) in
            Call(vf, new_args), ltp end

(*  Read a pattern and create the equivalent representation *)
and lexp_read_pattern pattern exp target ctx:
          ((string * location * (arg_kind * vdef) option list) * lexp_context) =

    match pattern with
        | Ppatany (loc) ->            (* Catch all expression nothing to do  *)
            ("_", loc, []), ctx

        | Ppatvar ((loc, name) as var) ->(
            try(
                let idx = senv_lookup name ctx in
                match (env_lookup_expr ctx ((loc, name), idx)) with
                    (* We are matching a constructor *)
                    | Some Cons _ ->
                        (name, loc, []), ctx

                    (* name is defined but is not a constructor  *)
                    (* it technically could be ... (expr option) *)
                    (* What about Var -> Cons ?                  *)
                    | _ -> let nctx = env_extend ctx var (Some target) dltype in
                        (name, loc, []), nctx)

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
    let lexp_parse p ctx = _lexp_p_infer p ctx (i + 1) in

    let make_args (args:(arg_kind * pvar option * pexp) list) ctx
        : (arg_kind * vdef option * ltype) list =
        let rec loop args acc ctx =
            match args with
                | [] -> (List.rev acc)
                | hd::tl -> begin
                    match hd with
                    | (kind, var, exp) ->
                       let lxp, _ = lexp_parse exp ctx in
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
and lexp_p_decls decls ctx = _lexp_decls decls ctx 1
and _lexp_decls decls ctx i: (((vdef * lexp * ltype) list) * lexp_context) =

    let ctx = ref ctx in
    let idx = ref 0 in

    (* Merge Type info and declaration together
     * merge using a map to guarantee uniqueness. *)
    let rec merge_decls (decls: (pvar * pexp * bool) list) merged acc:
                ((location * pexp option * pexp option * int) SMap.t * string list)  =

        (*  we cant evaluate here because variable are not in the environment *)
        match decls with
            | [] -> merged, (List.rev acc)
            | hd::tl ->
                match hd with
                (*  Type Info: Var:Type *)
                | ((loc, name), type_info, true) -> begin
                    try let (l, inst, _, i) = SMap.find name merged in
                        let new_decl = (l, inst, Some type_info, i) in
                        let nmerged = SMap.add name new_decl merged in
                            (merge_decls tl nmerged acc)

                    with Not_found ->
                        (* add variable to ctx *)
                        let new_decl = (loc, None, Some type_info, !idx) in
                        let nmerged = SMap.add name new_decl merged in
                            idx := !idx + 1;
                            ctx := env_extend (!ctx) (loc, name) None dltype;
                            (merge_decls tl nmerged (name::acc)) end

                (* Instruction: Var = expr *)
                | ((loc, name), inst, false) -> begin
                    try let (l, _, tp, i) = SMap.find name merged in
                        let new_decl = (l, Some inst, tp, i) in
                        let nmerged = SMap.add name new_decl merged in
                            (merge_decls tl nmerged acc)

                    with Not_found ->
                        (* add variable to ctx *)
                        let new_decl = (loc, Some inst, None, !idx) in
                        let nmerged = SMap.add name new_decl merged in
                            idx := !idx + 1;
                            ctx := env_extend (!ctx) (loc, name) None dltype;
                            (merge_decls tl nmerged (name::acc)) end in

    let mdecls, ord = merge_decls decls SMap.empty [] in

    (* cast map to list to preserve declaration order *)
    let ndecls = List.map (fun name ->
            let (l, inst, tp, _) = SMap.find name mdecls in
                ((l, name), inst, tp) ) ord in

    (* This is required for later *)
    let ctx = !ctx in
    let lst = ref [] in
    let n = ref ((List.length ndecls) - 1) in
        (* for each declaration lexp their rhs *)
        List.iter (fun ((loc, name), opxp, otpxp) ->
                let vdef = (loc, name) in
                let vref = (vdef, !n) in
                    n := !n - 1;

                match opxp, otpxp with
                    | Some pxp, Some tpxp ->
                        (* Add type first (for recursive definition) *)
                        let ltp, _ = _lexp_p_infer tpxp ctx (i + 1) in
                            (env_set_var_info ctx vref None ltp);

                        let lxp, _ = _lexp_p_infer pxp ctx (i + 1) in
                            (env_set_var_info ctx vref (Some lxp) ltp);

                            lst := (vdef, lxp, ltp)::!lst

                    | Some pxp, None ->
                        let lxp, ltp = _lexp_p_infer pxp ctx (i + 1) in
                            (env_set_var_info ctx vref (Some lxp) ltp);
                            lst := (vdef, lxp, ltp)::!lst

                    | None, _ -> lexp_warning loc "Unused Variable"
            )
        ndecls;

        List.rev (!lst), ctx

and _lexp_parse_all (p: pexp list) (ctx: lexp_context) i : lexp list =

    let rec loop (plst: pexp list) ctx (acc: lexp list) =
        match plst with
            | [] -> (List.rev acc)
            | _  -> let lxp, _ = _lexp_p_infer (List.hd plst) ctx (i + 1) in
                    (loop (List.tl plst) ctx (lxp::acc)) in

    (loop p ctx [])

(*  Print context  *)
and print_lexp_ctx ctx =
    let ((n, map), env, f) = ctx in

    print_string (make_title " LEXP CONTEXT ");

    make_rheader [
        (Some ('l', 10), "NAME");
        (Some ('l',  7), "INDEX");
        (Some ('l', 10), "NAME");
        (Some ('l', 36), "VALUE:TYPE")];

    print_string (make_sep '-');

    (* it is annoying to print according to StringMap order *)
    (* let's use myers list order *)
    let rec extract_names lst acc =
        match lst with
            | Mnil-> acc
            | Mcons (hd, tl, _, _) ->
                let (_, (_, name), _, _) = !hd in
                    extract_names tl (name::acc) in

    let ord = extract_names env [] in

    let rec _print idx ord =
        match ord with
            | [] -> ()
            | hd::tl ->(
        let idx2 = StringMap.find hd map in

        (if idx2 != idx then ());

        print_string "    | ";  lalign_print_string hd 10;
        print_string    " | ";  lalign_print_int (n - idx - 1) 7;
        print_string    " | ";

        try let (_, (_, name), exp, tp) = env_lookup_by_index (n - idx - 1) ctx in

            (*  Print env Info *)
            lalign_print_string name 10; (*   name must match *)
            print_string " | ";

            let _ = (match exp with
                | None -> print_string "<var>"
                | Some exp -> lexp_print exp) in

            print_string ": "; lexp_print tp; print_string "\n";

            _print (idx + 1) tl

        with Not_found ->
            (print_string "Not_found  |\n"; _print (idx + 1) tl)) in

    _print 0 ord;

    print_string (make_sep '=')

and print_lexp_trace () =
    print_trace " LEXP TRACE " 50 pexp_to_string pexp_print !_global_lexp_trace

(*  Only print var info *)
and lexp_print_var_info ctx =
    let ((m, _), env, _) = ctx in
    let n = Myers.length env in

    for i = 0 to n - 1 do (
        let (_, (_, name), exp, tp) = Myers.nth i env in
        print_int i; print_string " ";
        print_string name; (*   name must match *)
        print_string " = ";
         (match exp with
             | None -> print_string "<var>"
             | Some exp -> lexp_print exp);
        print_string ": ";
        lexp_print tp;
        print_string "\n")
    done;
;;


let lexp_parse_all p ctx = _lexp_parse_all p ctx 1;;


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
    let pxps = _pexp_expr_str str tenv grm limit in
        lexp_parse_all pxps ctx
;;

(* specialized version *)
let lexp_expr_str str lctx =
    _lexp_expr_str str default_stt default_grammar (Some ";") lctx
;;

let _lexp_decl_str (str: string) tenv grm limit ctx =
    let pxps = _pexp_decl_str str tenv grm limit in
        lexp_p_decls pxps ctx
;;

(* specialized version *)
let lexp_decl_str str lctx =
    _lexp_decl_str str default_stt default_grammar (Some ";") lctx
;;


(*  Eval String
 * ---------------------- *)
(* Because we cant include lparse in eval.ml *)

let _eval_expr_str str lctx rctx silent =
    let lxps = lexp_expr_str str lctx in
        (eval_all lxps rctx silent)
;;

let eval_expr_str str lctx rctx = _eval_expr_str str lctx rctx false

let eval_decl_str str lctx rctx =
    let lxps, lctx = lexp_decl_str str lctx in
        (eval_decls lxps rctx), lctx
;;