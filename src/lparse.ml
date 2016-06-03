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

module TC = Typecheck
module EL = Elexp
module SU = Subst

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
let _parsing_internals = ref false
let _shift_glob = ref 0
let btl_folder = ref "./btl/"

(* This is used to make Type annotation and inferred type having the same index *)
(* since inferred type might need to parse a lambda var to infer the type *)

let _type_shift tp i =
    match tp with
        | Var(v, idx) -> Var(v, idx)
        | expr -> expr

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


let build_var name ctx =
    let type0_idx = senv_lookup name ctx in
        Var((dloc, name), type0_idx)

(* build type0 from ctx *)
let get_type0 ctx = build_var "Type" ctx
let get_int ctx = build_var "Int" ctx

(* shift all variables by an offset *)
let senv_lookup name ctx =
  senv_lookup name ctx + !_shift_glob

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
                | Integer _ -> get_int ctx
                | Float _   -> type_float
                | String _  -> type_string;
                | _ -> lexp_error tloc "Could not find type";
                        pexp_print p; print_string "\n"; dltype)

        (*  Symbol i.e identifier *)
        | Pvar (loc, name) ->(
            try let idx = (senv_lookup name ctx) in
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
            let decls, nctx = _lexp_decls decls ctx i in
            let bdy, ltp = lexp_infer body nctx in
                (lexp_let_decls decls bdy nctx i), ltp

        (* ------------------------------------------------------------------ *)
        | Parrow (kind, ovar, tp, loc, expr) ->
            let ltp, _ = lexp_infer tp ctx in
            let nctx, sh = match ovar with
                | None -> ctx, 0
                | Some var -> (env_extend ctx var Variable ltp), 1 in

            let lxp, _ = lexp_infer expr nctx in
            let lxp = _type_shift lxp sh in

            let v = Arrow(kind, ovar, ltp, tloc, lxp) in
                v, (get_type0 ctx)

        (* Pinductive *)
        | Pinductive (label, formal_args, ctors) ->
            let type0 = get_type0 ctx in
            let nctx = ref ctx in
            (* (arg_kind * pvar * pexp option) list *)
            let formal = List.map (fun (kind, var, opxp) ->
                let ltp, _ = match opxp with
                    | Some pxp -> _lexp_p_infer pxp !nctx (i + 1)
                    | None -> dltype, dltype in

                nctx := env_extend !nctx var Variable ltp;
                    (kind, var, ltp)
                ) formal_args in

            let nctx = !nctx in
            let ltp = List.fold_left (fun tp (kind, _, _) ->
                (Arrow(kind, None, type0, tloc, tp))) type0 formal in

            let map_ctor = lexp_parse_inductive ctors nctx i in
            let v = Inductive(tloc, label, formal, map_ctor) in
                v, ltp

        (* This case can be inferred *)
        | Plambda (kind, var, optype, body) ->
            let ltp, _ = match optype with
                | Some ptype -> lexp_infer ptype ctx
                (* This case must have been lexp_p_check *)
                | None -> lexp_error tloc "Lambda require type annotation";
                    dltype, dltype in

            let nctx = env_extend ctx var Variable ltp in
            let lbody, lbtp = lexp_infer body nctx in
            (* We added one variable in the ctx * )
            let lbtp = _type_shift lbtp 1 in *)

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
                let formal, args = match unsusp_all idt with
                    | Inductive(_, _, formal, ctor_def) -> (
                        try formal, (SMap.find cname ctor_def)
                        with Not_found ->
                            lexp_error loc
                                ("Constructor \"" ^ cname ^ "\" does not exist");
                                [], [])

                    | _ -> lexp_error loc "Not an Inductive Type"; [], [] in

                (* build Arrow type *)
                let cons_type = List.fold_left (fun ltp (kind, v, tp) ->
                    Arrow(kind, v, tp, loc, ltp)) inductive_type (List.rev args) in

                (* Add Aerasable argument *)
                let cons_type = List.fold_left (fun ltp (kind, v, tp) ->
                    Arrow(Aerasable, Some v, tp, loc, ltp)) cons_type (List.rev formal) in

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

and lexp_p_check (p : pexp) (t : ltype) (ctx : lexp_context): lexp =
  _lexp_p_check p t ctx 1

and _lexp_p_check (p : pexp) (t : ltype) (ctx : lexp_context) i: lexp =
    let tloc = pexp_location p in

    _global_lexp_ctx := ctx;
    _global_lexp_trace := (i, tloc, p)::!_global_lexp_trace;

    match p with
        (* This case cannot be inferred *)
        | Plambda (kind, var, None, body) ->(
            (* Read var type from the provided type *)
            let ltp, lbtp = match unsusp_all t with
                | Arrow(kind, _, ltp, _, lbtp) -> ltp, lbtp
                | _ -> lexp_error tloc "Type does not match"; dltype, dltype in

            let nctx = env_extend ctx var Variable ltp in
            let lbody = _lexp_p_check body lbtp nctx (i + 1) in

                Lambda(kind, var, ltp, lbody))

        (* This is mostly for the case where no branches are provided *)
        | Pcase (loc, target, patterns) ->
            let lxp, _ = lexp_case (Some t) (loc, target, patterns) ctx i in
                lxp

        | _ -> let (e, inferred_t) = _lexp_p_infer p ctx (i + 1) in
            e (*
            match e with
                (* Built-in is a dummy function with no type. We cannot check
                 * Built-in *)
                | Builtin _ -> e
                | _ ->
            (if TC.conv_p inferred_t t then () else debug_msg (
                print_string "1 exp "; lexp_print e; print_string "\n";
                print_string "2 inf "; lexp_print inferred_t; print_string "\n";
                print_string "3 Ann "; lexp_print t; print_string "\n";
                lexp_warning tloc "Type Mismatch inferred != Annotation"));
                e*)

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
    let ctx_len = get_size ctx in

    (*  Read patterns one by one *)
    let fold_fun (merged, dflt) (pat, exp) =
        (*  Create pattern context *)
        let (name, iloc, arg), nctx = lexp_read_pattern pat exp tlxp ctx in
        let nctx_len = get_size nctx in

        (*  parse using pattern context *)
        let exp, ltp = lexp_infer exp nctx in
            (* we added len(arg) variable int the context *)
            texp := (_type_shift ltp (nctx_len - ctx_len))::!texp;

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

    let from_lctx ctx = try (from_lctx ctx)
        with e ->(
            lexp_error loc "Could not convert lexp context into rte context";
            print_eval_trace ();
            raise e) in

    (* consume Arrows and args together *)
    let rec get_return_type name i ltp args =
        match (unsusp_all ltp), args with
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
    let ltp = unsusp_all ltp in

    let handle_named_call (loc, name) =
        (*  Process Arguments *)
        let pargs = List.map pexp_parse sargs in
        let largs = _lexp_parse_all pargs ctx i in
        let new_args = List.map (fun g -> (Aexplicit, g)) largs in

        try (*  Check if the function was defined *)
            let idx = senv_lookup name ctx in
            let vf = (make_var name idx loc) in

                match unsusp_all (env_lookup_expr ctx ((loc, name), idx)) with
                    | Builtin((_, "Built-in"), _) ->(
                        (* ------ SPECIAL ------ *)
                        match !_parsing_internals, largs with
                            | true, [Imm(String (_, str))] ->
                                Builtin((loc, str), ltp), ltp

                            | true, [Imm(String (_, str)); ltp] ->
                                Builtin((loc, str), ltp), ltp

                            | true, _ ->
                                lexp_error loc "Wrong Usage of \"Built-in\"";
                                    dlxp, dltype

                            | false, _ ->
                                lexp_error loc "Use of \"Built-in\" in user code";
                                    dlxp, dltype)

                    | e ->
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
        let lxp = try env_lookup_expr ctx ((loc, name), idx) (* with
            | e -> e
            | _ -> lexp_fatal loc "The macro cannot be expanded"; *)
          with Not_found ->
            lexp_fatal loc (name ^ " was found but " ^ (string_of_int idx) ^
                  " is not a correct index.") in

        let lxp = match unsusp_all lxp with
            | Call(Var((_, "Macro_"), _), [(_, fct)]) -> fct
            | _ ->
              print_string "\n";
              print_string (lexp_to_string lxp); print_string "\n";
              lexp_print lxp; print_string "\n";
              lexp_fatal loc "Macro is ill formed" in

        (* Build function to be called *)
        let arg = olist2tlist_lexp sargs ctx in

        let lxp = Call(lxp, [(Aexplicit, arg)]) in
        let elexp = EL.erase_type lxp in
        let rctx = (from_lctx ctx 0) in

        (*
        let rargs = eval (EL.erase_type arg) rctx in
        let  rctx = add_rte_variable None rargs rctx in

        let lxp = Susp(lxp, (SU.shift 1)) in
        let body = eval (EL.erase_type lxp) rctx in

        print_string "HERE2\n";
        value_print body; *)
        (*

        print_string "\n\n";
        lexp_print lxp; print_string "\n\n"; *)

        (* print_string "DH: ";
           value_print (eval (EL.erase_type arg) rctx);  print_string "\n"; *)
        (*
         print_rte_ctx rctx; print_string "\n";
         print_lexp_ctx ctx; print_string "\n";*)

        _global_eval_trace := [];

        let vxp = try eval elexp rctx
          with e ->
            print_eval_trace ();
            raise e in

          let sxp = match vxp with
              | Vsexp(sxp) -> sxp
              (* Those are sexp converted by the eval function *)
              | Vint(i)    -> Integer(dloc, i)
              | Vstring(s) -> String(dloc, s)
              | Vfloat(f)  -> Float(dloc, f)
              (* I have vdum here WHY *)
              | v -> debug_msg (value_print v);
                  lexp_fatal loc "Macro_ expects '(List Sexp) -> Sexp'" in


        let pxp = pexp_parse sxp in
            _lexp_p_infer pxp ctx (i + 1)  in

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
        | ((Plambda _), _) ->
            (*  Process Arguments *)
            let pargs = List.map pexp_parse sargs in
            let largs = _lexp_parse_all pargs ctx i in
            let new_args = List.map (fun g -> (Aexplicit, g)) largs in
                Call(body, new_args), ltp

        | (Pvar (l, n), Var((_, "Macro"), _)) ->
            (* FIXME: check db_idx points too a Macro type *)
            handle_macro_call (l, n)

        (* Call to Vanilla or constructor *)
        | (Pvar v, _) -> handle_named_call v

        (* Constructor. This case is rarely used *)
        | (Pcons(_, v), _) -> handle_named_call v

        | Pcall(fct, sargs2), ltp ->
            let pargs = List.map pexp_parse sargs in
            let largs = _lexp_parse_all pargs ctx i in
            let new_args = List.map (fun g -> (Aexplicit, g)) largs in
            let body, ltp = lexp_call fct sargs2 ctx (i + 1) in
              Call(body, new_args), ltp

        | e, _ ->
        pexp_print e; print_string "\n";
        print_string ((pexp_to_string e) ^ "\n");
        lexp_fatal (pexp_location e) "This expression cannot be called"


(*  Read a pattern and create the equivalent representation *)
and lexp_read_pattern pattern exp target ctx:
          ((string * location * (arg_kind * vdef option) list) * lexp_context) =

    match pattern with
        | Ppatany (loc) ->            (* Catch all expression nothing to do  *)
            ("_", loc, []), ctx

        | Ppatvar ((loc, name) as var) ->(
            try(
                let idx = senv_lookup name ctx in
                match unsusp_all (env_lookup_expr ctx ((loc, name), idx)) with
                    (* We are matching a constructor *)
                    | Cons _ -> (name, loc, []), ctx

                    (* name is defined but is not a constructor  *)
                    (* it technically could be ... (expr option) *)
                    (* What about Var -> Cons ?                  *)
                    | _ -> let nctx = env_extend ctx var (LetDef target) dltype in
                        (name, loc, []), nctx)

            (* would it not make a default match too? *)
            with Not_found ->
                (* Create a variable containing target *)
                let nctx = env_extend ctx var (LetDef target) dltype in
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
                        let nctx = env_extend ctx var Variable dltype in
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
                            let nctx = env_extend ctx var Variable dltype in
                            loop tl ((kind, Some var, lxp)::acc) nctx
                  end in
        loop args [] ctx in

    List.fold_left
      (fun lctors ((_, name), args) ->
        SMap.add name (make_args args ctx) lctors)
      SMap.empty ctors

(* Macro declaration handling, return a list of declarations
 * to be processed *)
and lexp_decls_macro (loc, mname) sargs ctx: pdecl list =
  (* lookup for mname_  *)
  let _ = try senv_lookup mname ctx
    with Not_found ->
      lexp_warning loc ("Macro \"" ^ mname ^ "\" was not found!"); 0 in
    (* FIXME *)
    (* (eval macro) -> Sexp *)
    (* pexp_decls -> [pdecl] *)

    lexp_warning loc "Macro decls are not implemented yet!";
    []

(*  Parse let declaration *)
and lexp_p_decls decls ctx = _lexp_decls decls ctx 0

and lexp_let_decls decls (body: lexp) ctx i =
  (* build the weird looking let *)
  let decls = List.rev decls in
    List.fold_left (fun lxp decls ->
      Let(dloc, decls, lxp)) body decls

and _lexp_decls decls ctx i: (((vdef * lexp * ltype) list list) * lexp_context) =

  let names = ref [] in (* decls name in correct order *)
  let glob = ref SMap.empty in
  let mut = ref [] in
  let offset = ref 1 in
  let last_decls = ref "" in
  let recursive_mode = ref false in

  let ctx = List.fold_left (fun vctx expr ->
    _global_lexp_trace := [];
    match expr with
      | Pexpr((l, s), pxp) as e ->(
        try let idx = senv_lookup s vctx in
            let ltp = env_lookup_type vctx ((l, s), idx) in
            let lxp = lexp_p_check pxp ltp vctx in
              (* update declaration *)
              glob := SMap.add s (l, s, Some lxp, ltp) !glob;

            (* check if recursive definition *)
            (if !last_decls = s && !recursive_mode then
              (
                (* print_string "RECURSIVE END\n"; *)
                (* push every variable with the correct offset *)
                let d = List.rev !mut in
                let length = (List.length d) + 1 in
                let j = ref 0 in

                let vctx =
                List.fold_left (fun vctx n ->
                  let (l, s, lxp, ltp) = SMap.find n !glob in
                  let lxp = match lxp with
                    | Some lxp -> LetDef lxp
                    | None -> lexp_warning dloc "ForwardRef are not allowed";
                      ForwardRef in

                    j := !j + 1;
                    replace_by vctx s (length - !j, Some (l, s), lxp, ltp)) vctx d

                  in

                (* Clean everything *)
                mut := [];
                last_decls := "";
                recursive_mode := false;
                vctx
              )
            else
              (
                (if !recursive_mode then offset := !offset + 1);
                (* update context *)
                replace_by vctx s (1, Some (l, s), (LetDef lxp), ltp);
              ));

        with Not_found ->
          (* Add dummy first *)
          let tctx = env_extend vctx (l, s) ForwardRef dltype in
          let lxp, ltp = lexp_p_infer pxp tctx in

            names := [s]::!names;

            (if !recursive_mode then (
              offset := !offset + 1;
              mut := s::!mut));

            glob := SMap.add s (l, s, Some lxp, ltp) !glob;

            env_extend vctx (l, s) (LetDef lxp) ltp)

      | Ptype((l, s), ptp) as e ->
          (if !recursive_mode then () else
            last_decls := s;
            offset := 1);

          recursive_mode := true;
          names := [s]::!names;
          mut := s::!mut;

          (* get type *)
          let ltp, _ = lexp_p_infer ptp vctx in
          (* push *)
          glob := SMap.add s (l, s, None, ltp) !glob;
            env_extend vctx (l, s) ForwardRef ltp

      | Pmcall((l, n), sargs) ->
          let pdecls = lexp_decls_macro (l, n) sargs vctx in
            vctx

      | _ -> vctx) ctx decls in

  (*
  (if List.length !mut != 0 then names := !mut::!names); *)

  (* return a list containing mutually recursive def *)
  let merge_list names =
    List.fold_left (fun acc key ->
      let (l, s, lxp, ltp) = SMap.find key !glob in
      let lxp = match lxp with
        | Some lxp -> lxp
        | None -> dltype in

      (*
      let ltp = unsusp_all ltp in
      let lxp = unsusp_all lxp in *)
          ((l, s), lxp, ltp)::acc) [] names in

  let decls = List.map (fun names ->
    merge_list names) (List.rev !names) in

        decls, ctx

and lexp_decls_toplevel decls ctx =
  _lexp_decls decls ctx 1

  (* let names = ref [] in
  let offset = ref 0 in
  let merged = ref SMap.empty in
  let acc = ref [] in

  let ctx = List.fold_left (fun vctx expr ->
    match expr with
      | Pexpr ((l, s), pxp) ->(
        try let idx = senv_lookup s vctx in
          let ltp = env_lookup_type vctx ((l, s), idx) in
          let lxp = lexp_p_check pxp ltp vctx in
          let (_, _, _, ltp) = SMap.find s !merged in
          merged := SMap.add s (l, s, Some lxp, ltp) !merged;
          let r = !offset in
          let r = if r = 0 then 1 else r in
            offset := 0;
            replace_by vctx s (r, Some (l, s), (LetDef lxp), ltp);

        with Not_found ->
          (* Add dummy first *)
          let tctx = env_extend vctx (l, s) ForwardRef dltype in
          let lxp, ltp = lexp_p_infer pxp tctx in
            names := s::!names;
            merged := SMap.add s (l, s, Some lxp, ltp) !merged;
            env_extend vctx (l, s) (LetDef lxp) ltp)

      | Ptype ((l, s), ptp) ->
        offset := !offset + 1;
        let ltp, _ = lexp_p_infer ptp vctx in
          names := s::!names;
          merged := SMap.add s (l, s, None, ltp) !merged;
          env_extend vctx (l, s) ForwardRef ltp

      | _ -> vctx) ctx decls in

    (* merge type and expr *)
    let decls = List.fold_left (fun acc key ->
      let (l, s, lxp, ltp) = SMap.find key !merged in
      let lxp = match lxp with
        | Some lxp -> lxp
        | None -> dltype in
      let ltp = unsusp_all ltp in
      let lxp = unsusp_all lxp in
          ((l, s), lxp, ltp)::acc) [] !names in

    decls, ctx *)

and _lexp_parse_all (p: pexp list) (ctx: lexp_context) i : lexp list =

    let rec loop (plst: pexp list) ctx (acc: lexp list) =
        match plst with
            | [] -> (List.rev acc)
            | _  -> let lxp, _ = _lexp_p_infer (List.hd plst) ctx (i + 1) in
                    (loop (List.tl plst) ctx (lxp::acc)) in

    (loop p ctx [])

(*  Print context  *)
and print_lexp_ctx (ctx : lexp_context) =
    let ((n, map), env, f) = ctx in

    print_string (make_title " LEXP CONTEXT ");

    make_rheader [
        (Some ('l', 10), "NAME");
        (Some ('l',  7), "INDEX");
        (Some ('l', 10), "NAME");
        (Some ('l',  4), "OFF");
        (Some ('l', 29), "VALUE:TYPE")];

    print_string (make_sep '-');

    (* it is annoying to print according to StringMap order *)
    (* let's use myers list order *)
    let rec extract_names (lst: env_type) acc =
        match lst with
            | Mnil-> acc
            | Mcons (hd, tl, _, _) ->
                let name = match hd with
                  | (_, Some (_, name), _, _) -> name
                  | _ -> "" in
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

        try let r, name, exp, tp =
              match env_lookup_by_index (n - idx - 1) ctx with
                | (r, Some (_, name), LetDef exp, tp) -> r, name, Some exp, tp
                | _ -> 0, "", None, dltype in

            (*  Print env Info *)
            lalign_print_string name 10; (*   name must match *)
            print_string " | ";
             lalign_print_int r 4;
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


(*      Default context with builtin types
 * --------------------------------------------------------- *)

(* Make lxp context with built-in types *)
let empty_lctx =
    let lctx = make_lexp_context in
    let lxp = Builtin((dloc, "Built-in"), type0) in
      env_extend lctx (dloc, "Built-in") (LetDef lxp) type0

let default_lctx =

      (* Empty context *)
      let lctx = make_lexp_context in
      let lxp = Builtin((dloc, "Built-in"), type0) in
      let lctx = env_extend lctx (dloc, "Built-in") (LetDef lxp) type0 in

      (* Read BTL files *)
      let pres = prelex_file (!btl_folder ^ "types.typer") in
      let sxps = lex default_stt pres in
      let nods = sexp_parse_all_to_list default_grammar sxps (Some ";") in
      let pxps = pexp_decls_all nods in

      _parsing_internals := true;
          let d, lctx = lexp_p_decls pxps lctx in
      _parsing_internals := false;

      (* dump grouped decls * )
      List.iter (fun decls ->
        print_string "[";
        List.iter (fun ((_, s), _, _) ->
          print_string (s ^ ", ")) decls; print_string "] \n") d; *)

      (* Once default builtin are set we can populate the predef table *)
      try
          List.iter (fun name ->
              let idx = senv_lookup name lctx in
              let v = Var((dloc, name), idx) in (*
              let value = (env_lookup_expr lctx v) in *)
              set_predef name (Some v)) predef_name;
      (* -- DONE -- *)
          lctx
      with e ->
        lctx


(* Make runtime context with built-in types *)
let default_rctx =
     (* Empty context *)
      let lctx = make_lexp_context in
      let lxp = Builtin((dloc, "Built-in"), type0) in
      let lctx = env_extend lctx (dloc, "Built-in") (LetDef lxp) type0 in

      (* Read BTL files *)
      let pres = prelex_file (!btl_folder ^ "types.typer") in
      let sxps = lex default_stt pres in
      let nods = sexp_parse_all_to_list default_grammar sxps (Some ";") in
      let pxps = pexp_decls_all nods in

      _parsing_internals := true;
          let d, lctx = lexp_p_decls pxps lctx in
      _parsing_internals := false;

      let rctx = make_runtime_ctx in
        eval_decls_toplevel (EL.clean_toplevel d) rctx
    (*
    try (from_lctx (default_lctx))
        with e ->(
            print_eval_trace ();
            lexp_error dloc "Could not convert lexp context into rte context";
            raise e) *)


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
    let elxps = List.map EL.erase_type lxps in
        (eval_all elxps rctx silent)

let eval_expr_str str lctx rctx = _eval_expr_str str lctx rctx false

let eval_decl_str str lctx rctx =
    let lxps, lctx = lexp_decl_str str lctx in
    let elxps = (EL.clean_toplevel lxps) in
        (eval_decls_toplevel elxps rctx), lctx

