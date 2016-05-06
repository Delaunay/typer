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
        | Imm(Integer (_, i))       -> Vint(i)
        | Imm(String (_, s))        -> Vstring(s)
        | Imm(sxp)                  -> Vsexp(sxp)
        | Inductive (_, _, _, _)    -> Vdummy
        | Cons (_, label)           -> Vcons (label, [])
        | Lambda (_, _, _, lxp)     -> Closure(lxp, ctx)
        | Builtin (btype, str, _)   -> Vbuiltin(btype, str)

        (*  Return a value stored in env        *)
        | Var((loc, name), idx) as e -> eval_var ctx e ((loc, name), idx)

        (*  Nodes           *)
        (* ---------------- *)
        | Let(_, decls, inst) ->
            let nctx = _eval_decls decls ctx i in
                _eval inst nctx (i + 1)

        (* Function call *)
        | Call (lname, args) -> eval_call ctx i lname args

        (* Case *)
        | Case (loc, target, _, _, pat, dflt)
          -> (eval_case ctx i loc target pat dflt)

        | _ -> print_string "debug catch-all eval: ";
            lexp_print lxp; Vstring("eval Not Implemented")

and eval_var ctx lxp v =
    let ((loc, name), idx) = v in
    try get_rte_variable (Some name) (idx) ctx
    with e ->
        eval_error loc ("Variable: " ^ name ^ (str_idx idx) ^ " was not found ")

and eval_call ctx i lname args =
    let loc = lexp_location lname in
    let args = List.map (fun (k, e) -> _eval e ctx (i + 1)) args in
    let f = _eval lname ctx (i + 1) in

    (*
    let eval_call' f arg =
        match f with
            | Vcons(label, fields) ->
                Vcons (label, arg::fields)

            | Closure (lxp, ctx) ->
                _eval lxp (add_rte_variable None arg ctx) (i + 1)

            | Vbuiltin (btype, str) ->
                (get_builtin_impl btype str loc) loc [] (add_rte_variable None arg ctx)

            | _ -> value_print f;
                    eval_error loc "Cannot eval function" in

        List.fold_left eval_call' f args *)

    let rec eval_call f args ctx =
        match f, args with
            (* | Vcons ((_, "quote"), _), [vsxp] -> vsxp *)
            | Vcons (n, []), _ -> Vcons(n, args)

            (* we add an argument to the closure *)
            | Closure (lxp, ctx), hd::tl ->
                let nctx = add_rte_variable None hd ctx in
                let ret = _eval lxp nctx (i + 1) in
                    eval_call ret tl nctx

            | Vbuiltin (btype, str), args ->
                (* lookup the built-in implementation and call it *)
                (get_builtin_impl btype str loc) loc args ctx

            (* return result of eval *)
            | Closure (_, _), [] -> f
            | _, [] -> f

            | _ -> value_print f;
                eval_error loc "Cannot eval function" in

        eval_call f args ctx

and eval_case ctx i loc target pat dflt =
    (* Eval target *)
    let v = _eval target ctx (i + 1) in

    (* extract constructor name and arguments *)
    let ctor_name, args = match v with
        (* | Call(Var((_, cname), tp), args) -> cname, args *)
        | Vcons((_, cname), args)  -> cname, args

        | _ ->
            (* -- Debug print -- *)
            lexp_print target; print_string "\n";
            value_print v;     print_string "\n";
            (* -- Crash -- *)
            eval_error loc "Target is not a Constructor" in

    (* let ctor_n = List.length args in *)

    (*  Check if a default is present *)
    let run_default df =
        match df with
            | Some lxp -> _eval lxp ctx (i + 1)
            | None ->
                (* -- Debug print -- *)
                lexp_print target; print_string "\n";
                value_print v;     print_string "\n";
                (* -- Crash -- *)
                eval_error loc "Match Failure" in

    (*  Build a filter option *)
    let is_true key (_, pat_args, _) =
        (*let pat_n = List.length pat_args in (pat_n = ctor_n) &&  *)
            (ctor_name = key) in

    (*  Search for the working pattern *)
    let sol = SMap.filter is_true pat in
    if SMap.is_empty sol then
        run_default dflt
    else(
        (*  Get working pattern *)
        let key, (_, pat_args, exp) = SMap.min_binding sol in

        (* build context (List.fold2 has problem with some cases)  *)
        (* This is more robust                                     *)
        let rec fold2 nctx pats args =
            match pats, args with
                | (Some (_, (_, name)))::pats, arg::args ->
                    let nctx = add_rte_variable (Some name) arg nctx in
                        fold2 nctx pats args
                | None::pats, arg::args ->  fold2 nctx pats args
                (* Errors *)
                | _::_, [] -> eval_warning loc "a) Eval::Case Pattern Error"; nctx
                | [], _::_ -> eval_warning loc "b) Eval::Case Pattern Error"; nctx
                (* Normal case *)
                | [], [] -> nctx in

        let nctx = fold2 ctx pat_args args in
            _eval exp nctx (i + 1))

and build_arg_list args ctx i =
    (*  _eval every args *)
    let arg_val = List.map (fun (k, e) -> _eval e ctx (i + 1)) args in

    (*  Add args inside context *)
    List.fold_left (fun c v -> add_rte_variable None v c) ctx arg_val

and eval_decls decls ctx = _eval_decls decls ctx 0
and _eval_decls (decls: ((vdef * lexp * ltype) list))
               (ctx: runtime_env) i: runtime_env =

    (* Read declarations once and push them *)
    let ctx = List.fold_left (fun ctx ((_, name), lxp, ltp) ->
        add_rte_variable (Some name) Vdummy ctx)
        ctx decls in

    let n = (List.length decls) - 1 in

    (* Read declarations once and push them *)
    let _, ctx = List.fold_left (fun (idx, ctx) ((_, name), lxp, ltp) ->
        _global_eval_trace := [];
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
    _global_eval_trace := [];
    _eval lxp ctx 1

let debug_eval lxp ctx =
    try
        _global_eval_trace := [];
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
    let rctx = ref make_runtime_ctx in

    (* Skip builtins: They are already in default_rctx()  *)
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
            | Some lxp -> (try (eval lxp !rctx)
                with e -> lexp_print lxp; raise e)

            | None -> Vdummy in

                rctx := set_rte_variable j (Some name) vxp (!rctx)
    done;
        !rctx
