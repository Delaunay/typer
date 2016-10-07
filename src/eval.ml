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
open Lexp       (* Varbind *)

open Elexp
open Builtin
open Grammar
open Debruijn
open Env
module OL = Opslexp


(* eval error are always fatal *)
let eval_error loc msg =
    msg_error "EVAL" loc msg;
    raise (internal_error msg)

let eval_fatal = msg_fatal "EVAL"

let dloc = dummy_location
let eval_warning = msg_warning "EVAL"

let _global_eval_trace = ref []
let _global_eval_ctx = ref make_runtime_ctx
let _eval_max_recursion_depth = ref 255
let reset_eval_trace () = _global_eval_trace := []
let _builtin_lookup = ref SMap.empty

(* Print value name followed by the value in itself, finally throw an exception *)
let value_debug_message loc vxp message =
  print_string "\n";
  print_string (value_name vxp); print_string ": "; value_print vxp; print_string "\n";
  eval_fatal loc message

(* This is an internal definition
 * 'i' is the recursion depth used to print the call trace *)
let rec _eval lxp (ctx : Env.runtime_env) i: (value_type) =
  Debug_fun.do_debug (fun () ->
      prerr_endline ("[StackTrace] ------------------------------------------");
      prerr_endline ("[StackTrace] let rec _eval lxp ctx i");
      prerr_endline ("[StackTrace] lxp = " ^ Elexp.elexp_string lxp);
      prerr_endline ("[StackTrace] ctx = ???");
      prerr_endline ("[StackTrace] i   = " ^ (string_of_int i));
      prerr_endline ("[StackTrace] ------------------------------------------");
    ());
    let tloc = elexp_location lxp in

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
        | Inductive (_, _)          -> Vdummy
        | Cons (label)              -> Vcons (label, [])
        | Lambda ((_, n), lxp)      -> Closure(n, lxp, ctx)
        | Builtin ((_, str))        -> Vbuiltin(str)

        (* Return a value stored in env *)
        | Var((loc, name), idx) as e ->
          eval_var ctx e ((loc, name), idx)

        (*  Nodes           *)
        (* ---------------- *)
        | Let(_, decls, inst) ->
            let nctx = _eval_decls decls ctx i in
                _eval inst nctx (i + 1)

        (* Function call *)
        | Call (lname, args) -> eval_call ctx i lname args

        (* Case *)
        | Case (loc, target, pat, dflt)
          -> (eval_case ctx i loc target pat dflt)

        | Type -> Vcons((tloc, "Unit"), [])


and get_predef_eval name ctx =
  let r = (get_rte_size ctx) - !builtin_size in
  let v = mkSusp (get_predef_raw name) (S.shift r) in
    _eval (OL.erase_type v) ctx 0

and eval_var ctx lxp v =
    let ((loc, name), idx) = v in
  Debug_fun.do_debug (fun () ->
      prerr_endline ("[StackTrace] ------------------------------------------");
      prerr_endline ("[StackTrace] let eval_var ctx lxp v");
      prerr_endline ("[StackTrace] lxp = " ^ Elexp.elexp_string lxp);
      prerr_endline ("[StackTrace] ctx = ???");
      prerr_endline ("[StackTrace] v   = ((?loc?, " ^ name ^ "), " ^ (string_of_int idx) ^ ")");
      prerr_endline ("[StackTrace] ------------------------------------------");
    ());
    Debug_fun.do_debug (fun () ->
        prerr_endline ("index not shifted " ^ (string_of_int idx));
        prerr_endline ("ctx size          " ^ (string_of_int (get_rte_size ctx)));
        ()
      );
    try get_rte_variable (Some name) (idx) ctx
    with e ->
      eval_error loc ("Variable: " ^ name ^ (str_idx idx) ^ " was not found ")

and eval_call ctx i lname eargs =
    let loc = elexp_location lname in
    let f = _eval lname ctx (i + 1) in

    (* standard function *)
    let rec eval_call f args ctx =
      match f, args with
        | Vcons (n, []), _ ->
          let e = Vcons(n, args) in
            (* value_print e; print_string "\n"; *) e

        (* we add an argument to the closure *)
        | Closure (n, lxp, ctx), hd::tl ->
            let nctx = add_rte_variable (Some n) hd ctx in
            let ret = _eval lxp nctx (i + 1) in
                eval_call ret tl nctx

        | Vbuiltin (str), args ->
            (* lookup the built-in implementation and call it *)
            (get_builtin_impl str loc) loc (i + 1) args ctx

        (* return result of eval *)
        | _, [] -> f

        | _ -> debug_msg (value_print f);
            eval_error loc "Cannot eval function" in

    (* eval function here *)
    let args = List.map (fun e -> _eval e ctx (i + 1)) eargs in
      eval_call f args ctx

and eval_case ctx i loc target pat dflt =
    (* Eval target *)
    let v = _eval target ctx (i + 1) in

    (* extract constructor name and arguments *)
    let ctor_name, args = match v with
        | Vcons((_, cname), args)  -> cname, args
        | _ -> elexp_debug_message loc target "Target is not a Constructor" in

    (*  Get working pattern *)
    try let (_, pat_args, exp) = SMap.find ctor_name pat in
        (* build context (List.fold2 has problem with some cases)  *)
        (* This is more robust                                     *)
        let rec fold2 nctx pats args =
            match pats, args with
                | (Some (_, name))::pats, arg::args ->
                    let nctx = add_rte_variable (Some name) arg nctx in
                        fold2 nctx pats args
                | (None)::pats, arg::args ->  fold2 nctx pats args
                (* Errors: those should not happen but they might  *)
                (* List.fold2 would complain. we print more info   *)
                | _::_, [] -> eval_warning loc "a) Eval::Case Pattern Error"; nctx
                | [], _::_ -> eval_warning loc "b) Eval::Case Pattern Error"; nctx
                (* Normal case *)
                | [], [] -> nctx in

        let nctx = fold2 ctx pat_args args in
            _eval exp nctx (i + 1)

    (* Run default *)
    with Not_found -> (match dflt with
        | Some lxp -> _eval lxp ctx (i + 1)
        | _ -> eval_error loc "Match Failure")

and build_arg_list args ctx i =
    (*  _eval every args *)
    let arg_val = List.map (fun (k, e) -> _eval e ctx (i + 1)) args in

    (*  Add args inside context *)
    List.fold_left (fun c v -> add_rte_variable None v c) ctx arg_val

and eval_decls decls ctx = _eval_decls decls ctx 0
and _eval_decls (decls: (vdef * elexp) list)
                        (ctx: runtime_env) i: runtime_env =

    let n = (List.length decls) - 1 in

    (* Read declarations once and push them *)
    let nctx = List.fold_left (fun ctx ((_, name), _) ->
      add_rte_variable (Some name) Vdummy ctx) ctx decls in

    List.iteri (fun idx ((_, name), lxp) ->
      let v = _eval lxp nctx (i + 1) in
      let offset = n - idx in
        ignore (set_rte_variable offset (Some name) v nctx)) decls;

        nctx
and eval_decls_toplevel (decls: (vdef * elexp) list list) ctx =
  (* Add toplevel decls function *)
  List.fold_left (fun ctx decls ->
    eval_decls decls ctx) ctx decls

(* -------------------------------------------------------------------------- *)
(*              Builtin Implementation  (Some require eval)                   *)

and typer_builtins_impl = [
    ("_+_"           , iadd_impl);
    ("_*_"           , imult_impl);
    ("block_"        , make_block);
    ("symbol_"       , make_symbol);
    ("string_"       , make_string);
    ("integer_"      , make_integer);
    ("float_"        , make_float);
    ("node_"         , make_node);
    ("sexp_dispatch_", sexp_dispatch);
    ("string_eq"     , string_eq);
    ("int_eq"        , int_eq);
    ("sexp_eq"       , sexp_eq);
    ("eval_"         , typer_eval);
    ("open"          , open_impl);
    ("bind"          , bind_impl);
    ("run-io"        , run_io);
    ("read"          , read_impl);
    ("write"         , write_impl);
]

and bind_impl loc depth args_val ctx =

  let io, cb = match args_val with
    | [io; callback] -> io, callback
    | _ -> eval_error loc "bind expects two arguments" in

  (* build Vcommand from io function *)
  let cmd = match io with
    | Vcommand (cmd) -> cmd
    | _ -> eval_error loc "bind first arguments must be a monad" in

  (* bind returns another Vcommand *)
  Vcommand (fun () ->
    (* get callback *)
    let body, ctx = match cb with
      | Closure(_, body, ctx) -> body, ctx
      | _ -> eval_error loc "A Closure was expected" in

    (* run given command *)
    let underlying = cmd () in

    (* add evaluated IO to arg list *)
    let nctx = add_rte_variable None underlying ctx in

    (* eval callback *)
    _eval body nctx depth)

and run_io loc depth args_val ctx =

  let io, ltp = match args_val with
    | [io; ltp] -> io, ltp
    | _ -> eval_error loc "run-io expects 2 arguments" in

  let cmd = match io with
    | Vcommand (cmd) -> cmd
    | _ -> eval_error loc "run-io expects a monad as first argument" in

  (* run given command *)
  let _ = cmd () in

  (* return given type *)
    ltp

and typer_eval loc depth args ctx =
    let arg = match args with
        | [a] -> a
        | _ -> eval_error loc "eval_ expects a single argument" in
    (* I need to be able to lexp sexp but I don't have lexp ctx *)
    match arg with
        (* Nodes that can be evaluated *)
        | Closure (_, body, ctx) -> _eval body ctx depth
        (* Leaf *)
        | _ -> arg

and get_builtin_impl str loc =
    (* Make built-in lookup table *)
    (match (SMap.is_empty !_builtin_lookup) with
        | true ->
            _builtin_lookup := (List.fold_left (fun lkup (name, f) ->
                SMap.add name f lkup) SMap.empty typer_builtins_impl)
        | _ -> ());

    try SMap.find str !_builtin_lookup
    with Not_found ->
        eval_error loc ("Requested Built-in \"" ^ str ^ "\" does not exist")

(* Sexp -> (Sexp -> List Sexp -> Sexp) -> (String -> Sexp) ->
    (String -> Sexp) -> (Int -> Sexp) -> (Float -> Sexp) -> (List Sexp -> Sexp)
        ->  Sexp *)
and sexp_dispatch loc depth args ctx =
    let eval a b = _eval a b 1 in
    let sxp, nd, sym, str, it, flt, blk, rctx = match args with
        | [sxp; Closure(_, nd, rctx); Closure(_, sym, _);
                Closure(_, str, _); Closure(_, it, _);
                Closure(_, flt, _); Closure(_, blk, _)] ->
            sxp, nd, sym, str, it, flt, blk, rctx
        | _ ->  eval_error loc "sexp_dispatch expects 7 arguments" in

    let sxp = match sxp with
        | Vsexp(sxp)   -> sxp
        | _ -> debug_msg ( print_string "\n";
                    value_print sxp; print_string "\n");
            eval_error loc "sexp_dispatch expects a Sexp as 1st arg" in

    match sxp with
        | Node    (op, s)    ->(
            let rctx = add_rte_variable None (Vsexp(op)) rctx in
            let rctx = add_rte_variable None (olist2tlist_rte s) rctx in
                match eval nd rctx with
                    | Closure(_, nd, _) -> eval nd rctx
                    | _ -> eval_error loc "Node has 2 arguments")

        | Symbol  (_ , s)    ->
             eval sym (add_rte_variable None (Vstring(s)) rctx)
        | String  (_ , s)    ->
             eval str (add_rte_variable None (Vstring(s)) rctx)
        | Integer (_ , i)    ->
             eval it (add_rte_variable None (Vint(i)) rctx)
        | Float   (_ , f)    ->
             eval flt (add_rte_variable None (Vfloat(f)) rctx) (*
        | Block   (_ , s, _) ->
             eval blk (add_rte_variable None (olist2tlist_rte s)) *)
        | _ -> eval_error loc "sexp_dispatch error"

(* -------------------------------------------------------------------------- *)
and print_eval_result i lxp =
    print_string "     Out[";
    ralign_print_int i 2;
    print_string "] >> ";
    value_print lxp; print_string "\n";


and print_eval_trace () =
    print_trace " EVAL TRACE " 50 elexp_name elexp_print !_global_eval_trace

let eval lxp ctx =
    _eval lxp ctx 1

let debug_eval lxp ctx =
  Debug_fun.do_debug (fun () ->
      prerr_endline ("[StackTrace] ------------------------------------------");
      prerr_endline ("[StackTrace] let debug_eval lxps rctx silent");
      prerr_endline ("[StackTrace] lxp = " ^ Elexp.elexp_string lxp);
      prerr_endline ("[StackTrace] ctx = ???");
      prerr_endline ("[StackTrace] ------------------------------------------");
    ());
    try
        _global_eval_trace := [];
        eval lxp ctx
    with e -> (
        print_rte_ctx (!_global_eval_ctx);
        print_eval_trace ();
        raise e)

(*  Eval a list of lexp *)
let eval_all lxps rctx silent =
  Debug_fun.do_debug (fun () ->
      prerr_endline ("[StackTrace] ------------------------------------------");
      prerr_endline ("[StackTrace] let eval_all lxps rctx silent");
      prerr_endline ("[StackTrace] lxps = ???");
      prerr_endline ("[StackTrace] rctx = ???");
      prerr_endline ("[StackTrace] silent = " ^ string_of_bool silent);
      prerr_endline ("[StackTrace] ------------------------------------------");
    ());
    let evalfun = if silent then eval else debug_eval in
    List.map (fun g -> evalfun g rctx) lxps


let varname s = match s with Some (_, v) -> v | _ -> "<anon>"

(* build a rctx from a lctx.  *)
let from_lctx (ctx: elab_context): runtime_env =
    let (_, lctx, _) = ctx in
    let rctx : runtime_env
      = M.map (fun (_, oname, _, _)
               -> (match (oname : symbol option) with
                  | Some (_, name) -> Some name
                  | _ -> None),
                 ref Vdummy)
              lctx in

    (* Then fill each slot in turn.  *)
    let _, evals
      = M.fold_left
          (fun (i, evals) (o, oname, def, _)
           -> match def with
             | LetDef lxp
               -> (let elxp = OL.erase_type lxp in
                  let (_, valcell) = M.nth i rctx in
                  let octx = M.nthcdr (i - o + 1) rctx in
                  (i + 1, (valcell, elxp, octx) :: evals))
             | _
               (* FIXME: We should stop right here if this variable is
                * actually used (e.g. if this type's variable is ∀t.t).  *)
               -> eval_warning dloc ("No definition to compute the value of `"
                                    ^ varname oname ^ "`");
                 (i + 1, evals))
          (0, []) lctx in
    (* The evaluations have to be done "from the end of the list".  *)
    List.iter (fun (valcell, elxp, octx)
               -> try valcell := eval elxp octx
                 with e -> (* print_lexp_ctx (ectx_to_lctx ctx); *)
                          print_string "eval-in-from_lctx failed on: ";
                          (* lexp_print lxp; print_string "\nerased to: "; *)
                          elexp_print elxp;
                          print_string "\n"; raise e)
              evals;

    rctx
