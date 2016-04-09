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
open Eval
open Builtin

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
                (lexp_error loc ("The Variable: \"" ^ name ^ "\" was not declared");
                (* Error recovery. The -1 index will raise an error later on *)
                (make_var name (-1) loc))  end

        (*  Let, Variable declaration + local scope *)
        | Plet(loc, decls, body) ->
            let decl, nctx = _lexp_decls decls ctx i in
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
            let (_, cname) = sym in

            (*  An inductive type named type_name must be in the environment *)
            try let idx = senv_lookup type_name ctx in
                (*  Check if the constructor exists *)
                let idt = env_lookup_type ctx (vr, idx) in

                let _ = match idt with
                    | Inductive(_, _, _, ctor_def) -> (
                        try let _ = (SMap.find cname ctor_def) in ()
                        with Not_found ->
                            lexp_error loc
                                ("Constructor \"" ^ cname ^ "\" does not exist"))

                    | _ -> lexp_error loc "Not an Inductive Type" in

                Cons((vr, idx), sym)
            with Not_found ->
                lexp_error loc
                ("The inductive type: " ^ type_name ^ " was not declared");
                Cons((vr, -1), sym))

        (* Pcase *)
        | Pcase (loc, target, patterns) ->

            let lxp = lexp_parse target ctx in
            let ltp = UnknownType(loc) in

            let uniqueness_warn name =
                lexp_warning loc ("Pattern " ^ name ^ " is a duplicate." ^
                                       " It will override previous pattern.") in

            let check_uniqueness loc name map = (
                try let _ = SMap.find name map in uniqueness_warn name
                with e -> ()) in

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

                        if name = "_" then (
                            (if dflt != None then uniqueness_warn name);
                            loop tl merged (Some exp))
                        else (
                            check_uniqueness iloc name merged;
                            let merged = SMap.add name (iloc, arg, exp) merged in
                            loop tl merged dflt) in

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

            (* Is the function builtin ? *)
            if (is_lbuiltin idx ctx) then (
                match env_lookup_expr ctx ((loc, name), idx) with
                    | None -> lexp_error loc "Unknown builtin"; Call(vf, new_args)
                    | Some e -> Call(e, new_args)
            )
            else Call(vf, new_args)

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
and lexp_p_decls decls ctx = _lexp_decls decls ctx 1
and _lexp_decls decls ctx i: (((vdef * lexp * ltype) list) * lexp_context) =
    let lexp_parse v c = _lexp_parse v c (i + 1) in
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
            | (var, _, _) -> senv_add_var var ctx)
        ctx decls in

    let n = (List.length decls) - 1 in

    (*  Add Variable info *)
    let rec process_var_info dcl_lst ctx acc m =
        match dcl_lst with
            | [] -> (List.rev acc), ctx
            | hd::tl ->
                match hd with
                    | ((loc, name), Some pinst, None) ->(
                        let lxp, ltp = lexp_p_infer pinst ctx in
                        let nacc = ((loc, name), lxp, ltp)::acc in
                        let ctx = env_add_var_info (0, (loc, name),
                                                     Some lxp, ltp) ctx in
                            process_var_info tl ctx nacc (m - 1))

                    | ((loc, name), Some pinst, Some ptype) ->(
                        let linst  = lexp_parse pinst ctx in
                        let ltyp = lexp_parse ptype ctx in
                        let nacc = ((loc, name), linst, ltyp)::acc in
                        let ctx = env_add_var_info (0, (loc, name),
                                                     Some linst, ltyp) ctx in
                            process_var_info tl ctx nacc (m - 1))

                    (* Skip the variable *)
                    | ((loc, name), None, _) -> (lexp_warning loc "Unused Variable";
                            process_var_info tl ctx acc m) in

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
and lexp_p_infer (p : pexp) (env : lexp_context): lexp * ltype =

    (* Parse expr *)
    let tloc = pexp_location p in
    let lxp = lexp_parse p env in

    let consume_args args lxp ctx =
        let arg_n = List.length args in
        let rec _implt args lxp i = match args, lxp with
            (* No args left, return the remaining type *)
            | [], _ -> lxp
            | _, UnknownType _ -> lxp

            (* Basic case consume an arg and an arrow *)
            | hd::tl, Arrow(_, _, ltp, _, ret_type) ->
                (* FIXME: Check hd and ltp are of the same type *)
                _implt tl ret_type (i + 1)

            (* We still have args to consume but type is not an arrow *)
            | (_, hd)::tl, tp ->
                lexp_error tloc ("Number of Arg mismatch. Expected: " ^
                    (string_of_int i) ^ " arg(s). Got " ^ (string_of_int arg_n));
                tp  in
        _implt args lxp 0 in

    let is_type lxp =
        match lxp with
            | Inductive _ -> true
            | _ -> false in

    let rec get_type lxp ctx =
        match lxp with
            (* Leafs        *)
            (* ------------ *)

            (* Why don't we always return tp ? We want to be able to use    *)
            (* type aliases     Nat = inductive_                            *)
            (* We want the type to be inferred as 'Nat' not 'inductive_'... *)
            (* But sometimes we need tp to be returned                      *)
            | Var vrf -> (try let tp = env_lookup_type ctx vrf in
                (if (is_type tp) then lxp else tp)
                with e ->
                    UnknownType(dloc))

            (* I am not sure we should consider a constructor as a function   *)
            (* Another way to do what is done here is to handle cons in Call  *)
            | Cons (vrf, (_, n)) ->(
                let rec build_arrow_type args acc =
                    match args with
                        | [] -> acc
                        | (kind, var, ltp)::tl ->
                            build_arrow_type tl (Arrow(kind, var, ltp, dloc, acc))
                            in

                match env_lookup_type ctx vrf with
                    | Inductive(_, _, _, ctor_map) -> (
                        try match SMap.find n ctor_map with
                            (* No Args *)
                            | [] -> Var(vrf)  (* return its inductive type *)
                            (* Return a Constructor function *)
                            | args -> build_arrow_type (List.rev args) (Var(vrf))

                        with Not_found ->
                            (lexp_error tloc ("Constructor " ^ n ^
                                                     " does not exist"); dltype))
                    | _ -> (lexp_error tloc "Inductive type was expected"; dltype))

            | Imm sxp -> (match sxp with
                | Integer _ -> let idx = senv_lookup "Int" ctx in
                        env_lookup_type ctx ((dloc, "Int"), idx)
                | Float _ -> let idx = senv_lookup "Float" ctx in
                        env_lookup_type ctx ((dloc, "Float"), idx)
                | _ -> lexp_error tloc "Could not infer type"; dltype)

            (* Types by definition *)
            | Inductive _ -> lxp
            | Builtin (_, _, ltp) -> ltp
            | Arrow _ -> lxp
            | UnknownType _ -> lxp

            (* Nodes        *)
            (* ------------ *)
            | Let (_, _, body) -> (get_type body ctx)
            | Call(f, args) ->
                (consume_args args (get_type f ctx) ctx)

            | Case (_, _, _, branches, dflt) ->
                (* we need to check that all branches return the same type *)
                let lst = SMap.bindings branches in
                let types = List.map
                    (fun (_, (_, args, body)) ->
                        (* FIXME: We need to lookup arg type *)
                        let nctx = List.fold_left (fun c v ->
                            match v with
                                | None -> c
                                | Some (_, arg) -> env_extend ctx arg None dltype)
                            ctx args in
                            get_type body nctx) lst in

                let types = match dflt with
                    | None -> types
                    | Some expr -> (get_type expr ctx)::types in
                let tp = List.hd types in
                    (* FIXME: do type checking *)
                    tp

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
             | Some exp -> lexp_print exp);
            print_string ": ";
            _lexp_print (!debug_ppctx) tp;
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

let _eval_expr_str str lctx rctx silent =
    let lxps = lexp_expr_str str lctx in
        (eval_all lxps rctx silent)
;;

let eval_expr_str str lctx rctx = _eval_expr_str str lctx rctx false

let eval_decl_str str lctx rctx =
    let lxps, lctx = lexp_decl_str str lctx in
        (eval_decls lxps rctx), lctx
;;