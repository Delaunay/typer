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
 *          Simple interpreter
 *
 * --------------------------------------------------------------------------- *)

open Util
open Fmt

open Sexp
open Pexp       (* Arg_kind *)
open Lexp

open Builtin
open Grammar

open Debruijn
open Env

(* eval error are always fatal *)
let eval_error loc msg =
    msg_error "EVAL" loc msg;
    raise (internal_error msg)
;;

let eval_fatal = msg_fatal "EVAL"

let dloc = dummy_location
let eval_warning = msg_warning "EVAL"

let _global_eval_trace = ref []
let _global_eval_ctx = ref make_runtime_ctx
let _eval_max_recursion_depth = ref 255
let reset_eval_trace () = _global_eval_trace := []


(* This is an internal definition
 * 'i' is the recursion depth used to print the call trace *)
let rec _eval lxp ctx i: (value_type) =
    let tloc = lexp_location lxp in

    (if i > (!_eval_max_recursion_depth) then
        eval_fatal tloc "Recursion Depth exceeded");

    _global_eval_ctx := ctx; (*  Allow us to print the latest used environment *)
    _global_eval_trace := (i, tloc, lxp)::!_global_eval_trace;

    match lxp with
        (*  Leafs           *)
        (* ---------------- *)
        | Imm(v) -> Value(lxp)
        | Inductive (_, _, _, _) as e -> Value(e)
        | Cons (_, _) as e -> Value(e)

        (* Lambda's body is evaluated when called   *)
        | Lambda (_, _, _, lxp) -> Closure(lxp, ctx)

        (*  Return a value stored in the env        *)
        | Var((loc, name), idx) as e -> eval_var ctx e ((loc, name), idx)

        (*  Nodes           *)
        (* ---------------- *)
        | Let(_, decls, inst) ->
            let nctx = _eval_decls decls ctx i in
                _eval inst nctx (i + 1)

        (* I don't really know why Built-in is ever evaluated... but it is sometimes *)
        | Builtin _ -> Vdummy

        (* Built-in Function *)
        | Call(Builtin(btype, str, ltp), args)->
            (* built-in does not have location info. So we extract it from args *)
            let tloc = match args with
                | (_, hd)::tl -> lexp_location hd
                | _ -> dloc in
            let args_val = List.map (fun (k, e) -> _eval e ctx (i + 1)) args in
                (get_builtin_impl btype str ltp tloc) tloc args_val ctx

        (* Function call *)
        | Call (lname, args) as call -> eval_call ctx i lname args call

        (* Case *)
        | Case (loc, target, _, pat, dflt) -> (eval_case ctx i loc target pat dflt)


        | _ -> print_string "debug catch-all eval: ";
            lexp_print lxp; Value(Imm(String(dloc, "eval Not Implemented")))

and eval_var ctx lxp v =
    let ((loc, name), idx) = v in
    try get_rte_variable (Some name) (idx) ctx
    with e ->
        eval_error loc ("Variable: " ^ name ^ (str_idx idx) ^ " was not found ")

and eval_call ctx i lname args call =
    (* create a clean environment *)
    let args_val = List.map (fun (k, e) -> _eval e ctx (i + 1)) args in
    let clean_ctx = temp_ctx ctx in

    (* get function body *)
    let body = _eval lname ctx (i + 1) in

    let rec eval_call body args ctx =
        match body, args with
            (* first lambda *)
            | Value (lxp), hd::tl -> (match lxp with
                | Cons _ ->
                    let cons_args = List.map (fun g ->
                        (Aexplicit, (get_value_lexp g)))  args_val in
                            Value(Call(lname, (cons_args)))
                | _ ->
                    (* Push first arg *)
                    let nctx = add_rte_variable None hd ctx in
                    (* eval first lambda *)
                    let ret = _eval lxp nctx (i + 1) in

                        eval_call ret tl nctx)

            (* we add an argument to the closure *)
            | Closure (lxp, ctx), hd::tl ->
                let nctx = add_rte_variable None hd ctx in
                let ret = _eval lxp nctx (i + 1) in
                    eval_call ret tl nctx

            (* No more arguments *)
            | Closure (_, _), [] -> body
            | _, [] -> body
            | _ -> value_print body;
                eval_error dloc "Cannot eval function" in

        eval_call body args_val clean_ctx

and eval_case ctx i loc target pat dflt =
    (* Eval target *)
    let v = (get_value_lexp (_eval target ctx (i + 1))) in

    let (_, (osize, _)) = ctx in    (* number of variable declared outside *)
    let csize = get_rte_size ctx in (* current size                        *)
    let offset = csize - osize in

    (* Get inductive type from a constructor *)
    let get_inductive_ref lxp =
        match lxp with
            | Cons(((_, vname), idx), (_, cname)) ->(
                let info = (get_value_lexp
                                (get_rte_variable (Some vname) (idx + offset) ctx)) in
                let ctor_def = match info with
                    | Inductive(_, _, _, c) -> c
                    | _ -> eval_error loc "Not an Inductive Type" in
                    info, ctor_def)
            | _ -> eval_error loc "Target is not a Constructor" in

    (* I think checks should be in lexp not done during eval *)
    (* check if a constructor 'cname' exist                  *)
    let check_ctor cname cargs ctor_def =
        try let targs = (SMap.find cname ctor_def) in
            let n_targs = List.length targs in
            let n_cargs = List.length cargs in

            match (n_targs - n_cargs) with
                | 0 -> cname, cargs
                | _ -> eval_error loc ("Constructor not applied. " ^
                    cname ^ " expected " ^ (string_of_int n_targs) ^ " arg(s)." ^
                    " Given " ^ (string_of_int n_cargs) ^ " arg(s).")

        with Not_found ->
            eval_error loc ("Constructor \"" ^ cname ^ "\" does not exist") in

    (* extract constructor name and check its validity *)
    let ctor_name, args = match v with
        | Call(Var((_, cname), tp), args) ->(
            (* Don't check the constructor this job will be done in lexping *)
                cname, args)

            (* get constructor * )
            try let ctor = get_rte_variable None (tp + offset) ctx in
                let idt, ctor_def = get_inductive_ref ctor in
                    check_ctor cname args ctor_def

            (* currently we have a little bug with ctor checking *)
            with e -> cname, args) *)

        | Cons(((_, vname), idx), (_, cname)) as ctor ->
            let idt, ctor_def = get_inductive_ref ctor in
                check_ctor cname [] ctor_def

        | _ -> lexp_print target; print_string "\n";
            lexp_print v; print_string "\n";
            eval_error loc "Target is not a Constructor" in

    (*  Check if a default is present *)
    let run_default df =
        match df with
        | None -> eval_error loc "Match Failure"
        | Some lxp -> _eval lxp ctx (i + 1) in

    let ctor_n = List.length args in

    (*  Build a filter option *)
    let is_true key value =
        let (_, pat_args, _) = value in
        let pat_n = List.length pat_args in
            (* FIXME: Shouldn't pat_n != ctor_n cause an error ? *)
            if pat_n = ctor_n && ctor_name = key then
                true
            else
                false in

    (* if the argument is a reference to a variable its index need to be
     * shifted  *)
    let arg_shift xp offset =
        match xp with
            | Var(a, idx) -> Var(a, idx + offset)
            | _ -> xp in

    (*  Search for the working pattern *)
    let sol = SMap.filter is_true pat in
        if SMap.is_empty sol then
            run_default dflt
        else
            (*  Get working pattern *)
            let key, (_, pat_args, exp) = SMap.min_binding sol in

            (* count the number of declared variables *)
            let case_offset = List.fold_left (fun i g ->
                match g with None -> i | _ -> i + 1)
                0 pat_args in

            let toffset = case_offset + offset in

            (* build context *)
            let nctx = List.fold_left2 (fun nctx pat arg ->
                match pat with
                    | None -> nctx
                    | Some (_, (_, name)) ->
                        let (_, xp) = arg in
                        let xp = (arg_shift xp toffset) in
                            add_rte_variable (Some name) (Value(xp)) nctx)

                ctx pat_args args in
                    (* eval body *)
                    _eval exp nctx (i + 1)

and build_arg_list args ctx i =
    (*  _eval every args *)
    let arg_val = List.map (fun (k, e) -> _eval e ctx (i + 1)) args in

    (*  Add args inside context *)
    List.fold_left (fun c v -> add_rte_variable None v c) ctx arg_val

and eval_decls decls ctx = _eval_decls decls ctx 1
and _eval_decls (decls: ((vdef * lexp * ltype) list))
               (ctx: runtime_env) i: runtime_env =

    (* Read declarations once and push them *)
    let ctx = List.fold_left (fun ctx ((_, name), lxp, ltp) ->
        add_rte_variable (Some name) (Value(lxp)) ctx)
        ctx decls in

    (* local ctx saves the number of declared variable inside ctx      *)
    (* This is used to remove temporary variables when entering a Call *)
    let ctx = local_ctx ctx in
    let n = (List.length decls) - 1 in

    (* Read declarations once and push them *)
    let _, ctx = List.fold_left (fun (idx, ctx) ((_, name), lxp, ltp) ->

        let lxp = _eval lxp ctx (i + 1) in
        let ctx = set_rte_variable idx (Some name) lxp ctx in
        (idx - 1, ctx))
        (n, ctx) decls in

        ctx

and print_eval_result i lxp =
    print_string "     Out[";
    ralign_print_int i 2;
    print_string "] >> ";
    value_print lxp; print_string "\n";


and print_eval_trace () =
    print_trace " EVAL TRACE " 50 lexp_to_string lexp_print !_global_eval_trace
;;

let eval lxp ctx =
    _eval lxp ctx 1

let debug_eval lxp ctx =
    try
        eval lxp ctx
    with e -> (
        print_rte_ctx (!_global_eval_ctx);
        print_eval_trace ();
        raise e)
;;

(*  Eval a list of lexp *)
let eval_all lxps rctx silent =
    let evalfun = if silent then eval else debug_eval in
    List.map (fun g -> evalfun g rctx) lxps;;


(* build a rctx from a lctx *)
let from_lctx (ctx: lexp_context): runtime_env =
    let ((_, _), env, _) = ctx in
    let rctx = ref (default_rctx ()) in

    (* Skip builtins *)
    let bsize = List.length typer_builtins in
    let csize = get_size ctx in

    (* add all variables *)
    for i = bsize to csize do
        let (_, (_, name), _, _) = !(Myers.nth (csize - i) env) in
        rctx := add_rte_variable (Some name) Vdummy (!rctx)
    done;

    let diff = csize - bsize in

    (* process all of them *)
    for i = 0 to diff do
        let j = diff - i (* - 1 *) in
        let (_, (_, name), exp, _) = !(Myers.nth j env) in

        let vxp = match exp with
            | Some lxp -> (eval lxp !rctx)
            | None -> Vdummy in

                rctx := set_rte_variable j (Some name) vxp (!rctx)
    done;
        !rctx




