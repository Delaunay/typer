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
open Pexp       (* Arg_kind *)
open Lexp
open Lparse
open Myers
open Sexp
open Fmt
open Debruijn
open Grammar


let eval_error loc msg =
    msg_error "EVAL" loc msg;
    raise (internal_error msg)
;;

let dloc = dummy_location
let eval_warning = msg_warning "EVAL"

let print_myers_list l print_fun =
    let n = (length l) - 1 in

    print_string (make_title " ENVIRONMENT ");
    make_rheader [(None, "INDEX");
        (None, "VARIABLE NAME"); (Some ('l', 48), "VALUE")];
    print_string (make_sep '-');

    for i = 0 to n do
    print_string "    | ";
        ralign_print_int (n - i) 5;
        print_string " | ";
        print_fun (nth (n - i) l);
    done;
    print_string (make_sep '=');
;;

let print_rte_ctx ctx =
    let (l, b) = ctx in
    print_myers_list l
    (fun (n, g) ->
        let _ =
        match n with
            | Some m -> lalign_print_string m 12; print_string "  |  "
            | None -> print_string (make_line ' ' 12); print_string "  |  " in
        lexp_print g; print_string "\n")
;;


let get_int lxp =
    match lxp with
        | Imm(Integer(_, l)) -> Some l
        | _ -> None
;;

(* Offset is used when we eval declaration one by one                    *)
(* i.e not everything is present so we need to account for missing decls *)
type decls_offset = int

(*  Runtime Environ *)
type runtime_env = ((string option * lexp) myers) * (int * int * decls_offset)

let make_runtime_ctx = (nil, (0, 0, 0));;

let add_rte_variable name x ctx =
    let (l, b) = ctx in
    let lst = (cons (name, x) l) in
        (lst, b);;

let get_rte_variable (name: string option) (idx: int) (ctx: runtime_env): lexp =
    let (l, (_, _, offset)) = ctx in
    let idx = if idx >= offset then idx - offset else idx in
    let (tn, x) = (nth idx l) in
    match (tn, name) with
        | (Some n1, Some n2) -> (
            if n1 = n2 then
                x
            else (
            eval_error dloc
                ("Variable lookup failure. Expected: \"" ^
                n2 ^ "[" ^ (string_of_int idx) ^ "]" ^ "\" got \"" ^ n1 ^ "\"")))

        | _ -> x (* can't check variable's name (call args do not have names) *)
;;

let get_rte_size (ctx: runtime_env): int = let (l, _) = ctx in length l;;

(* This function is used when we enter a new scope *)
(* it allow us to removed temporary variables when we enter temporary scope *)
let local_ctx ctx =
    let (l, (_, _, off)) = ctx in
    let osize = length l in
        (l, (osize, 0, off))
;;

let select_n ctx n =
    let (l, a) = ctx in
    let r = ref nil in
    let s = (length l) - 1 in

    for i = 0 to n - 1 do
        r := (cons (nth (s - i) l) (!r));
    done;

    ((!r), a)

let temp_ctx ctx =
    let (l, (osize, _, _)) = ctx in
    let tsize = length l in
        (* Check if temporary variables are present *)
        if tsize != osize then
            (* remove temp var *)
            (select_n ctx osize)
        else
            ctx
;;

let nfirst_rte_var n ctx =
    let rec loop i acc =
        if i < n then
            loop (i + 1) ((get_rte_variable None i ctx)::acc)
        else
            List.rev acc in
    loop 0 []
;;

let _global_eval_trace = ref []
let _global_eval_ctx = ref (nil, (0, 0, 0))
let _eval_max_recursion_depth = ref 255
let reset_eval_trace () = _global_eval_trace := []

(*  currently, we don't do much *)
type value_type = lexp

(* This is an internal definition
 * 'i' is the recursion depth used to print the call trace *)
let rec _eval lxp ctx i: (value_type) =
    let tloc = lexp_location lxp in
    let str_idx idx = "[" ^ (string_of_int idx) ^ "]" in

    (if i > (!_eval_max_recursion_depth) then
        raise (internal_error "Recursion Depth exceeded"));

    _global_eval_ctx := ctx;  (*  Allow us to print the latest used environment *)
    _global_eval_trace := (i, tloc, lxp)::!_global_eval_trace;

    match lxp with
        (*  Leafs           *)
        (* ---------------- *)
        | Imm(v) -> lxp
        | Inductive (_, _, _, _) as e -> e
        | Cons (_, _) as e -> e

        (* Lambda's body is evaluated when called *)
        | Lambda _ -> lxp

        (*  Return a value stored in the environ *)
        | Var((loc, name), idx) as e ->(
            (* find variable binding i.e we do not want a another variable *)
             (* (-3) represent a variable which should not be replaced *)
            let rec var_crawling expr k =
                (if k > 255 then(
                    lexp_print expr; print_string "\n"; flush stdout;
                    eval_error tloc "Variable lookup failed"));
                match expr with
                    | Var(_, j) when j = (-3)-> e
                    | Var((_, name2), j) ->
                        let p = (get_rte_variable (Some name2) j ctx) in
                            var_crawling p (k + 1)
                    | _ -> expr in

            try (var_crawling e 0)
            with Not_found ->
                eval_error tloc ("Variable: " ^
                                      name ^ (str_idx idx) ^ " was not found "))

        (*  Nodes           *)
        (* ---------------- *)
        (*  this works for non recursive let *)
        | Let(_, decls, inst) ->
            (*  First we _evaluate all declaration then we eval the instruction *)
            let nctx = build_ctx decls ctx i in
                _eval inst (local_ctx nctx) (i + 1)

        (* Built-in Function * )
        | Call(Builtin(v, name, ltp), args) ->
            let nctx = build_arg_list args ctx i in *)

        (*  Function call *)
        | Call (lname, args) -> eval_call ctx i lname args

        (* Case *)
        | Case (loc, target, _, pat, dflt) -> (eval_case ctx i loc target pat dflt)

        | _ -> Imm(String(dloc, "eval Not Implemented"))

and eval_call ctx i lname args =
    (* create a clean environment *)
    let tloc = lexp_location lname in
    let clean_ctx = temp_ctx ctx in
    let args_n = List.length args in

    (*  To handle partial call we need to consume args and   *)
    (*  lambdas together an return the remaining lambda      *)
    (*  Call by name: replace variables then eval            *)
    let rec consume_args (ctx: runtime_env) (lxp: lexp) args (k: int): value_type =
        match lxp, args with
            (* Base Case*)
            | Lambda(_, (_, name), _, body), arg::tl ->
                let ctx = add_rte_variable (Some name) arg ctx in
                    consume_args ctx body tl (k + 1)

            (* Partial Application *)
            (* In truth we don't really stop here. We push missing args *)
            (* as such that missing args will be replaced by themselves *)
            (* when the full eval will be called                        *)
            | Lambda(kind, (loc, name), l, body), [] ->
                let ctx = add_rte_variable (Some name) (Var((loc, name), -3)) ctx in
                let b = consume_args ctx body [] (k + 1) in
                    Lambda(kind, (loc, name), l, b)

            (* Full Eval *)
            | _, [] ->
                _eval lxp ctx (k + i)

            (* Too many args *)
            | _, _ ->
                eval_error tloc ("Wrong Number of arguments. " ^
                        " Got:" ^ (string_of_int args_n) ^ " arg(s) " ^
                        " Expected: " ^ (string_of_int k) ^ " arg(s) ") in

    match lname with
        (*  Hardcoded functions *)
        (* FIXME: These should not be hardcoded here, but should be
         * stuffed into the "initial environment", i.e. the value of
         * `ctx` used at top-level.  *)

        (* + is read as a nested binary operator *)
        | Var((_, name), _) when name = "_+_" ->
            let nctx = build_arg_list args ctx i in

            let llxp = (get_rte_variable (None) 0 nctx) in
            let rlxp = (get_rte_variable (None) 1 nctx) in
            let l = get_int llxp in
            let r = get_int rlxp in

            (* if l and r are not ints this is a partial eval *)
            if l = None || r = None then
                Call(lname, [(Aexplicit, llxp); (Aexplicit, rlxp)])
            else (
                let v, w = match l, r with
                    | Some v, Some w -> v, w
                    | _, _ -> (-40), (-40) in
                Imm(Integer(dloc, v + w)))

        (* _*_ is read as a single function with x args *)
        | Var((_, name), _) when name = "_*_" ->
            let nctx = build_arg_list args ctx i in

            let vint = (nfirst_rte_var args_n nctx) in
            let varg = List.map (fun g -> get_int g) vint in

            let (partial, prod) = List.fold_left (fun a g ->
                let (partial, prod) = a in
                    match g with
                        | Some v  -> (partial, v * prod)
                        | None -> (true, 0))
                (false, 1) varg in

            if partial then
                let args = List.map (fun g -> (Aexplicit, g)) vint in
                    Call(lname, args)
            else
                Imm(Integer(dloc, prod))

        (* This is a named function call *)
        | Var((_, name), idx) -> (
            (*  get function's body from current context *)
            let body = get_rte_variable (Some name) idx ctx in

            (*  _eval every args using current context *)
            let arg_val = List.map (fun (k, e) -> _eval e ctx (i + 1)) args in
            let arg_val2 = List.map (fun (k, e) -> e) args in

            match body with
                (* If 'cons', build it back with evaluated args *)
                | Cons _ ->
                    Call(lname, (List.map (fun g -> (Aexplicit, g)) arg_val))

                | Lambda _ ->
                    (consume_args clean_ctx body arg_val 0)

                | _ ->
                (*  Add args inside our clean context *)
                let nctx = List.fold_left (fun c v -> add_rte_variable None v c)
                    clean_ctx arg_val in
                    _eval body nctx (i + 1))

        (* TODO Everything else                 *)
        (*  Which includes a call to a lambda   *)
        | _ -> Imm(String(dloc, "Funct Not Implemented"))

and eval_case ctx i loc target pat dflt =
    (* Eval target *)
    let v = _eval target ctx (i + 1) in

    let (_, (osize, _, _)) = ctx in
    let csize = get_rte_size ctx in
    let offset = csize - osize in

    (*  V must be a constructor Call *)
    let ctor_name, args = match v with
        | Call(lname, args) -> (match lname with
            (* FIXME we should check that ctor_name is an existing
             * constructor with the correct number of args          *)
            | Var((_, ctor_name), _) -> ctor_name, args
            | _ -> eval_error loc "Target is not a Constructor" )

        | Cons(((_, vname), idx), (_, cname)) -> begin
            (*  retrieve type definition *)
            let info = get_rte_variable (Some vname) (idx + offset) ctx in
            let ctor_def = match info with
                | Inductive(_, _, _, c) -> c
                | _ -> eval_error loc "Not an Inductive Type" in

            try match SMap.find cname ctor_def with
                | [] -> cname, []
                | carg ->
                    let ctor_n = List.length carg in
                    eval_error loc ("Constructor not applied. " ^
                         "Constructor name: \"" ^ cname ^
                         "\": " ^ (string_of_int ctor_n) ^
                         " argument(s) expected")
            with
                Not_found ->
                    eval_error loc "Constructor does not exist" end

        | _ -> lexp_print target; print_string "\n";
            lexp_print v; print_string "\n";
            eval_error loc "Can't match expression" in

    (*  Check if a default is present *)
    let run_default df =
        match df with
        | None -> Imm(String(loc, "Match Failure"))
        | Some lxp -> _eval lxp ctx (i + 1) in

    let ctor_n = List.length args in

    (*  Build a filter option *)
    let is_true key value =
        let (_, pat_args, _) = value in
        let pat_n = List.length pat_args in
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
                            add_rte_variable (Some name) xp nctx)

                ctx pat_args args in
                    (* eval body *)
                    _eval exp nctx (i + 1)

and build_arg_list args ctx i =
    (*  _eval every args *)
    let arg_val = List.map (fun (k, e) -> _eval e ctx (i + 1)) args in

    (*  Add args inside context *)
    List.fold_left (fun c v -> add_rte_variable None v c) ctx arg_val

and build_ctx decls ctx i =
    let f nctx e =
        let (v, exp, tp) = e in
        let value = _eval exp ctx (i + 1) in
            add_rte_variable None value nctx in

    List.fold_left f ctx decls

and eval_decls decls ctx = _eval_decls decls ctx 1
and _eval_decls (decls: ((vdef * lexp * ltype) list))
               (ctx: runtime_env) i: runtime_env =

    let set_offset ctx off =
        let (l, (a, b, c)) = ctx in
            (l , (a, b, off)) in

    let n = (List.length decls) - 1 in

    try

    let dctx, _ = List.fold_left (fun (ctx, k) g ->
        let ((_, name), lxp, _) = g in
        let lxp = _eval lxp ctx (i + 1) in
        let ctx = set_offset ctx (n - k) in
        let ctx = add_rte_variable (Some name) lxp ctx in
            (ctx, k + 1))
        (ctx, 0) decls in

    let dctx = set_offset dctx 0 in
        (local_ctx dctx)

    with e ->(
        print_rte_ctx (!_global_eval_ctx);
        print_eval_trace ();
        raise e
    )


and print_eval_result i lxp =
    print_string "     Out[";
    ralign_print_int i 2;
    print_string "] >> ";
    match lxp with
        | Imm(v) -> sexp_print v; print_string "\n"
        | e ->  lexp_print e; print_string "\n"

and print_eval_trace () =
    print_trace " EVAL TRACE " 50 lexp_to_string lexp_print !_global_eval_trace
;;

let eval lxp ctx =
    _global_eval_trace := [];
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

(*  Eval String
 * ---------------------- *)
let _eval_expr_str str lctx rctx silent =
    let lxps = lexp_expr_str str lctx in
        (eval_all lxps rctx silent)
;;

let eval_expr_str str lctx rctx = _eval_expr_str str lctx rctx false

let eval_decl_str str lctx rctx =
    let lxps, lctx = lexp_decl_str str lctx in
        (eval_decls lxps rctx), lctx
;;
