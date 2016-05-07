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

open Prelexer
open Lexer

open Sexp
open Pexp
open Lexp

open Env
open Debruijn
open Eval

open Grammar
open Builtin

(* Shortcut => Create a Var *)
let make_var name index loc =
    Var(((loc, name), index))

let dlxp = type0
let dltype = type0
let dloc = dummy_location

let lexp_warning = msg_warning "LPARSE"
let lexp_error = msg_error "LPARSE"
let lexp_fatal = msg_fatal "LPARSE"

let _global_lexp_ctx = ref make_lexp_context
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
                | Float _   -> type_float
                | String _  -> type_string;
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

        (* ------------------------------------------------------------------ *)
        | Parrow (kind, ovar, tp, loc, expr) ->
            let ltp, _ = lexp_infer tp ctx in
            let ctx = match ovar with
                | None -> ctx
                | Some var ->  env_extend ctx var None ltp in

            let lxp, _ = lexp_infer expr ctx in
            let v = Arrow(kind, ovar, ltp, tloc, lxp) in
                v, type0

        (* Pinductive *)
        | Pinductive (label, formal_args, ctors) ->
            let ctx = ref ctx in
            (* (arg_kind * pvar * pexp option) list *)
            let formal = List.map (fun (kind, var, opxp) ->
                let ltp, _ = match opxp with
                    | Some pxp -> _lexp_p_infer pxp !ctx (i + 1)
                    | None -> dltype, dltype in

                ctx := env_extend !ctx var None dltype;
                    (kind, var, ltp)
                ) formal_args in
            (* (arg_kind * vdef * ltype) list *)

            (* -- Should I do that ?? --* )
            let rec make_type args tp =
                match args with
                    | (kind, (loc, n), ltp)::tl ->
                        make_type tl (Arrow(kind, Some (loc, n), ltp, loc, tp))
                    | [] -> tp in *)

            let ctx = !ctx in
            let map_ctor = lexp_parse_inductive ctors ctx i in
            let v = Inductive(tloc, label, formal, map_ctor) in
                v, type0

        (* This case can be inferred *)
        | Plambda (kind, var, optype, body) ->
            let ltp, _ = match optype with
                | Some ptype -> lexp_infer ptype ctx
                (* This case must have been lexp_p_check *)
                | None -> lexp_error tloc "Lambda require type annotation";
                    dltype, dltype in

            let nctx = env_extend ctx var None ltp in
            let lbody, lbtp = lexp_infer body nctx in

            let lambda_type = Arrow(kind, None, ltp, tloc, lbtp) in
                Lambda(kind, var, ltp, lbody), lambda_type

        | Pcall (fname, _args) ->
            lexp_call fname _args ctx i

        (* Pcons *)
        | Pcons(vr, sym) -> (
            let (loc, type_name) = vr in
            let (_, cname) = sym in

            (*  An inductive type named type_name must be in the environment *)
            try let idx = senv_lookup type_name ctx in
                (*  Check if the constructor exists *)
                let idt = env_lookup_expr ctx (vr, idx) in

                (* make Base type *)
                let inductive_type = Var((loc, type_name), idx) in

                (* Get constructor args *)
                let args = match idt with
                    | Some Inductive(_, _, _, ctor_def) -> (
                        try (SMap.find cname ctor_def)
                        with Not_found ->
                            lexp_error loc
                                ("Constructor \"" ^ cname ^ "\" does not exist");
                                [])

                    | _ -> lexp_error loc "Not an Inductive Type"; [] in

                (* build Arrow type *)
                let cons_type = List.fold_left (fun ltp (kind, v, tp) ->
                    Arrow(kind, v, tp, loc, ltp)) inductive_type (List.rev args) in

                Cons((vr, idx), sym), cons_type

            with Not_found ->
                lexp_error loc
                ("The inductive type: " ^ type_name ^ " was not declared");
                Cons((vr, -1), sym), dltype)

        (* Pcase: we can infer iff `patterns` is not empty *)
        | Pcase (loc, target, patterns) ->
            lexp_case None (loc, target, patterns) ctx i

        | Phastype (_, pxp, ptp) ->
            let ltp, _ = lexp_infer ptp ctx in
                (_lexp_p_check pxp ltp ctx (i + 1)), ltp

        | _ -> pexp_print p; print_string "\n";
            lexp_fatal tloc "Unhandled Pexp"

and _lexp_p_check (p : pexp) (t : ltype) (ctx : lexp_context) i: lexp =
    let tloc = pexp_location p in

    _global_lexp_ctx := ctx;
    _global_lexp_trace := (i, tloc, p)::!_global_lexp_trace;

    match p with
        (* This case cannot be inferred *)
        | Plambda (kind, var, None, body) ->(
            (* Read var type from the provided type *)
            let ltp, lbtp = match t with
                | Arrow(kind, _, ltp, _, lbtp) -> ltp, lbtp
                | _ -> lexp_error tloc "Type does not match"; dltype, dltype in

            let nctx = env_extend ctx var None ltp in
            let lbody = _lexp_p_check body lbtp nctx (i + 1) in

                Lambda(kind, var, ltp, lbody))

        (* This is mostly for the case where no branches are provided *)
        | Pcase (loc, target, patterns) ->
            let lxp, _ = lexp_case (Some t) (loc, target, patterns) ctx i in
                lxp

        | _ -> let (e, inferred_t) = _lexp_p_infer p ctx (i + 1) in
            (* FIXME: check that inferred_t = t!  *)
            e

(* Lexp.case cam be checked and inferred *)
and lexp_case (rtype: lexp option) (loc, target, patterns) ctx i =
    (* FIXME: check if case is exhaustive  *)
    (* Helpers *)
    let lexp_infer p ctx = _lexp_p_infer p ctx (i + 1) in

    let rtype = ref rtype in

    let type_check ltp =
        match !rtype with
            (* FIXME: check if branch returns correct type *)
            | Some rltp -> true
             (* if rtype was not provided then we use the first branch as reference *)
            | None -> rtype := (Some ltp); true in

    let uniqueness_warn name =
        lexp_warning loc ("Pattern " ^ name ^ " is a duplicate." ^
                          " It will override previous pattern.") in

    let check_uniqueness loc name map =
        try let _ = SMap.find name map in uniqueness_warn name
            with e -> () in

    (* get target and its type *)
    let tlxp, tltp = lexp_infer target ctx in

    (* make a list of all branches return type *)
    let texp = ref [] in

    (*  Read patterns one by one *)
    let fold_fun (merged, dflt) (pat, exp) =
        (*  Create pattern context *)
        let (name, iloc, arg), nctx = lexp_read_pattern pat exp tlxp ctx in

        (*  parse using pattern context *)
        let exp, ltp = lexp_infer exp nctx in
            texp := ltp::!texp;

        (* Check ltp type. Must be similar to rtype *)
        (if type_check ltp then ()
            else lexp_error iloc "Branch return type mismatch");

        if name = "_" then (
            (if dflt != None then uniqueness_warn name);
                merged, (Some exp))
        else (
            check_uniqueness iloc name merged;
            let merged = SMap.add name (iloc, arg, exp) merged in
                merged, dflt) in

    let (lpattern, dflt) =
        List.fold_left fold_fun (SMap.empty, None) patterns in

    let return_type = match (!texp), (!rtype) with
        | hd::_, _ -> hd
        | _    , Some v -> v

        (* This is impossible *)
        | _, None -> typer_unreachable "The case has no return type info" in

    Case (loc, tlxp, tltp, return_type, lpattern, dflt), return_type

(*  Identify Call Type and return processed call *)
and lexp_call (fun_name: pexp) (sargs: sexp list) ctx i =
    let loc = pexp_location fun_name in

    (*  Process Arguments *)
    let pargs = List.map pexp_parse sargs in
    let largs = _lexp_parse_all pargs ctx i in
    let new_args = List.map (fun g -> (Aexplicit, g)) largs in

    let from_lctx ctx = try (from_lctx ctx)
        with e ->
            lexp_fatal loc "Could not convert lexp context into rte context" in

    (* consume Arrows and args together *)
    let rec get_return_type name i ltp args =
        match ltp, args with
            | _, [] -> ltp
            | Arrow(_, _, _, _, ltp), hd::tl -> (get_return_type name (i + 1) ltp tl)
            | _, _ -> lexp_warning loc
                (name ^ " was provided with too many args. Expected: " ^
                            (string_of_int i)); ltp in

    (*  Vanilla     : sqr is inferred and (lambda x -> x * x) is returned
     *  Macro       : sqr is returned
     *  Constructor : a constructor is returned
     *  Anonymous   : lambda                                                  *)

    (* retrieve function's body *)
    let body, ltp = _lexp_p_infer fun_name ctx (i + 1) in
    (* let ret_type = get_return_type 0 ltp new_args in *)

    let handle_named_call (loc, name) =
        try (*  Check if the function was defined *)
            let idx = senv_lookup name ctx in
            let vf = (make_var name idx loc) in

            (* Replace a built-in name by builtin so they can be recognized
             * during eval         *)
            if (is_lbuiltin idx ctx) then (
                match env_lookup_expr ctx ((loc, name), idx) with
                    | None -> lexp_error loc "Unknown builtin";
                        let ret_type = get_return_type name 0 ltp new_args in
                            Call(vf, new_args), ret_type

                    | Some Builtin((_, "Built-in"), ltp) ->(
                        match largs with
                            | [Imm (String (_, str)) ] ->
                                Builtin((loc, str), ltp), ltp
                            | _ -> typer_unreachable "cannot be reached")

                    (* a builtin functions *)
                    | Some Builtin((_, name), ltp) ->
                        (* We keep loc info *)
                        Call(Builtin((loc, name), ltp), new_args), ltp

                    | _ -> typer_unreachable "ill formed Builtin"
            )
            else
            let ret_type = get_return_type name 0 ltp new_args in
                Call(vf, new_args), ret_type

        with Not_found ->
            lexp_error loc ("The function \"" ^ name ^ "\" was not defined");
            let vf = (make_var name (-1) loc) in
                Call(vf, new_args), ltp in

    let handle_macro_call (loc, name) =
        (* look up for definition *)
        let idx = try senv_lookup name ctx
            with Not_found ->
                lexp_fatal loc ("Could not find Variable: " ^ name) in

        (* Get the macro *)
        let lxp = try match env_lookup_expr ctx ((loc, name), idx) with
            | None -> lexp_fatal loc "The macro cannot be expanded";
            | Some e -> e
            with Not_found ->
                lexp_fatal loc (name ^ " was found but " ^ (string_of_int idx) ^
                    " is not a correct index.") in

        let sxp = match eval lxp (from_lctx ctx) with
            (* (Macro_ sexp) is returned *)
            | Vcons(_, [Vsexp(sxp)]) -> sxp
            | v -> value_print v; print_string "\n";
                lexp_fatal loc "Macro_ expects sexp" in

        let pxp = pexp_parse sxp in
        (* Generated Code *)
        let lxp, ltp = _lexp_p_infer pxp ctx (i + 1) in
            Call(lxp, new_args), ltp in

    (*
    let handle_qq loc =
        (* In quasi quote we need to traverse the sexp tree and evaluate
         * (uq) calls                                                         *)

        let rec seek_n_replace sxp =
            match sxp with
                (* Unquote *)
                | Node (Symbol(_, "uquote"), [arg]) ->(
                     let parg = pexp_parse arg in
                     let larg, _ = _lexp_p_infer parg ctx i in
                     let vsxp = eval larg (from_lctx ctx) in
                        match vsxp with
                            | Vint    (i)   -> Integer(loc, i)
                            | Vstring (s)   -> String (loc, s)
                            | Vsexp(sxp)    -> sxp
                            | _ ->
                                value_print vsxp;
                                lexp_warning loc "Sexp was expected"; Epsilon)

                | Node (op, lst)     -> Node(op, (List.map seek_n_replace lst))
                | _ -> sxp in

        let sxp = match sargs with
            | [sxp] -> seek_n_replace sxp
            | _ -> lexp_error loc "qquote expects a sexp"; Epsilon in
                Imm(sxp), type_sexp in *)

    (* determine function type *)
    match fun_name, ltp with
        (* Anonymous *)
        | ((Plambda _), _) -> Call(body, new_args), ltp

        (* Call to a macro *)
        | (Pvar (l, n), Builtin((_, "Macro"), _)) ->
             handle_macro_call (l, n)

        (*
        | (Pvar (l, "qquote"), _) -> handle_qq l *)

        (* Call to quote * )
        | (Pvar (l, "'"), _) -> (match (handle_named_call (l, "'")), sargs with
            | (Call (n, _), ltp), [sxp] -> Call(n, [(Aexplicit, Imm(sxp))]), ltp
            | e, _ -> lexp_warning loc "quote operator expects one argument"; e) *)

        (* Call to Vanilla or constructor *)
        | (Pvar v, _) -> handle_named_call v

        (* Constructor. This case is rarely used *)
        | (Pcons(_, v), _) -> handle_named_call v

        | e, _ -> lexp_fatal (pexp_location e) "This expression cannot be called"


(*  Read a pattern and create the equivalent representation *)
and lexp_read_pattern pattern exp target ctx:
          ((string * location * (arg_kind * vdef option) list) * lexp_context) =

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
                   (((arg_kind * vdef option) list) * lexp_context)=

    let rec loop args acc ctx =
        match args with
            | [] -> (List.rev acc), ctx
            | hd::tl -> (
                let (_, pat) = hd in
                match pat with
                    (* Nothing to do *)
                    | Ppatany (loc) -> loop tl ((Aexplicit, None)::acc) ctx
                    | Ppatvar ((loc, name) as var) ->
                        (*  Add var *)
                        let nctx = env_extend ctx var None dltype in
                        let nacc = (Aexplicit, Some var)::acc in
                            loop tl nacc nctx
                    | _ -> lexp_error dloc "Constructor inside a Constructor";
                           loop tl ((Aexplicit, None)::acc) ctx)

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
and lexp_p_decls decls ctx = _lexp_decls decls ctx 0
and _lexp_decls decls ctx i: (((vdef * lexp * ltype) list) * lexp_context) =
    (* (pvar * pexp * bool) list *)

    let ctx = ref ctx in
    let idx = ref 0 in

    (* Merge Type info and declaration together
     * merge using a map to guarantee uniqueness. *)
    let rec merge_decls (decls: (pvar * pexp * bool) list) merged acc:
                ((location * pexp option * pexp option * int) SMap.t * string list)  =

        (*  we cant evaluate here because variables are not in the environment *)
        match decls with
            | [] -> merged, (List.rev acc)
            | ((loc, name), pxp, bl)::tl ->
                let (l, opxp, optp, i), acc = try (SMap.find name merged), acc
                    with Not_found ->
                        idx := !idx + 1;
                        ctx := env_extend (!ctx) (loc, name) None dltype;
                        (loc, None, None, !idx - 1), (name::acc) in

                let new_decl = match bl with
                    | true  -> (l, opxp, Some pxp, i)
                    | false -> (l, Some pxp, optp, i) in

                let nmerged = SMap.add name new_decl merged in
                    (merge_decls tl nmerged acc) in

    let mdecls, ord = merge_decls decls SMap.empty [] in

    (* cast map to list to preserve declaration order *)
    let ndecls = List.map (fun name ->
            let (l, inst, tp, _) = SMap.find name mdecls in
                ((l, name), inst, tp) ) ord in

    (* This is required for later *)
    let ctx = !ctx in
    let lst = ref [] in

    (* Doing types and expressions separately allow us to use        *)
    (* all typing information when lexp_parsing recursive definition *)
    (* The price of this is iterating twice over declarations        *)
    (* + now we need to lookup type info                             *)

    (* Process types once *)
    let n = ref ((List.length ndecls) - 1) in
        (* for each declaration lexp their types *)
        List.iter (fun ((loc, name), opxp, otpxp) ->
            let vdef = (loc, name) in
            let vref = (vdef, !n) in
                n := !n - 1;

            match opxp, otpxp with
                | _, Some tpxp -> let ltp, _ = _lexp_p_infer tpxp ctx (i + 1) in
                    (env_set_var_info ctx vref None ltp);
                | _ -> ())
        ndecls;

    (* Process declaration in itself*)
    let n = ref ((List.length ndecls) - 1) in
        List.iter (fun ((loc, name), opxp, otpxp) ->
            let vdef = (loc, name) in
            let vref = (vdef, !n) in
                n := !n - 1;

            match opxp, otpxp with
                | Some pxp, Some ptp ->
                    let ltp = env_lookup_type ctx vref in
                    let lxp = _lexp_p_check pxp ltp ctx (i + 1) in
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

        let ptr_str = "" in (*"    |            |         |            | " in *)

        try let (_, (_, name), exp, tp) = env_lookup_by_index (n - idx - 1) ctx in

            (*  Print env Info *)
            lalign_print_string name 10; (*   name must match *)
            print_string " | ";

            let _ = (match exp with
                | None -> print_string "<var>"
                | Some exp -> lexp_print exp)
                    (* let str = _lexp_to_str (!debug_ppctx) exp in
                    let str = (match str_split str '\n' with
                        | hd::tl -> print_string (hd ^ "\n"); tl
                        | _ -> []) in

                        List.iter (fun elem ->
                            print_string (ptr_str ^ elem ^ "\n")) str) *)in

            print_string (ptr_str ^ ": "); lexp_print tp; print_string "\n";

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
    done


let lexp_parse_all p ctx = _lexp_parse_all p ctx 1


(* add dummy definition helper *)
let add_def name ctx =
    let var = (dloc, name) in
    let ctx = senv_add_var var ctx in
    env_add_var_info (0, var, None, dlxp) ctx

(*      Default context with builtin types
 * --------------------------------------------------------- *)

(* Make lxp context with built-in types *)
let default_lctx () =
    (* Empty context *)
    let lctx = make_lexp_context in
    let lxp = Builtin((dloc, "Built-in"), type0) in
    let lctx = env_extend lctx (dloc, "Built-in") (Some lxp) type0 in

    (* Read BTL files *)
    let pres = prelex_file "./btl/types.typer" in
    let sxps = lex default_stt pres in
    let nods = sexp_parse_all_to_list default_grammar sxps (Some ";") in

    let pxps = pexp_decls_all nods in
    let _, lctx = lexp_p_decls pxps lctx in
        lctx
;;

(* Make runtime context with built-in types *)
let default_rctx () =
    try (from_lctx (default_lctx ()))
        with e ->
            lexp_fatal dloc "Could not convert lexp context into rte context"


(*      String Parsing
 * --------------------------------------------------------- *)

(* Lexp helper *)
let _lexp_expr_str (str: string) (tenv: bool array)
            (grm: grammar) (limit: string option) (ctx: lexp_context) =
    let pxps = _pexp_expr_str str tenv grm limit in
        lexp_parse_all pxps ctx

(* specialized version *)
let lexp_expr_str str lctx =
    _lexp_expr_str str default_stt default_grammar (Some ";") lctx

let _lexp_decl_str (str: string) tenv grm limit ctx =
    let pxps = _pexp_decl_str str tenv grm limit in
        lexp_p_decls pxps ctx

(* specialized version *)
let lexp_decl_str str lctx =
    _lexp_decl_str str default_stt default_grammar (Some ";") lctx



(*  Eval String
 * --------------------------------------------------------- *)
(* Because we cant include lparse in eval.ml *)

let _eval_expr_str str lctx rctx silent =
    let lxps = lexp_expr_str str lctx in
        (eval_all lxps rctx silent)

let eval_expr_str str lctx rctx = _eval_expr_str str lctx rctx false

let eval_decl_str str lctx rctx =
    let lxps, lctx = lexp_decl_str str lctx in
        (eval_decls lxps rctx), lctx
