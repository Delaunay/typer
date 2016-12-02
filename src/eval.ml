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
open Printf           (* IO Monad *)
module OL = Opslexp


type eval_debug_info = elexp list * elexp list

let dloc = dummy_location
let _global_eval_trace = ref ([], [])
let _global_eval_ctx = ref make_runtime_ctx
let _eval_max_recursion_depth = ref 255

let builtin_functions
  = ref (SMap.empty : ((location -> eval_debug_info
                        -> value_type list -> value_type)
                       (* The primitive's arity.  *)
                       * int) SMap.t)

let add_builtin_function name f arity =
  builtin_functions := SMap.add name (f, arity) (!builtin_functions)

let append_eval_trace trace (expr : elexp) =
  let (a, b) = trace in
  let r = expr::a, b in
    _global_eval_trace := r; r

let append_typer_trace trace (expr : elexp) =
  let (a, b) = trace in
  let r = (a, expr::b) in
    _global_eval_trace := r; r

let get_trace () = !_global_eval_trace

let rec_depth trace =
  let (a, b) = trace in
    List.length b

(* eval error are always fatal *)
let error loc msg =
    msg_error "EVAL" loc msg;
    flush stdout;
    raise (internal_error msg)

let fatal = msg_fatal "EVAL"
let warning = msg_warning "EVAL"

(*  Print a message that look like this:
 *
 * [Ln   8, cl   6] ./samples/error.typer
 *   [X] Fatal     EVAL     MESSAGE
 *       > ....
 *       > ....
 *
 *)

let debug_messages error_type loc message messages =
  let msg = List.fold_left (fun str msg ->
    str ^ "\n        > " ^ msg) message messages in
      error_type loc (msg ^ "\n")

let root_string () =
  let a, _ = !_global_eval_trace in
  match List.rev a with
    | [] -> ""
    | e::_ -> elexp_string e

let debug_message error_type type_name type_string loc expr message =
  debug_messages error_type loc
    message [
      (type_name expr) ^ ": " ^ (type_string expr);
      "Root: " ^ (root_string ());
    ]

(* Print value name followed by the value in itself, finally throw an exception *)
let value_fatal = debug_message fatal value_name value_string
let value_error = debug_message error value_name value_string
let elexp_fatal = debug_message fatal elexp_name elexp_string


(*
 *                  Builtins
 *)
(* Builtin of builtin * string * ltype *)
let add_binary_iop name f =
  let name = "Int." ^ name in
  let f loc (depth : eval_debug_info) (args_val: value_type list) =
    match args_val with
    | [Vint(v); Vint(w)] -> Vint (f v w)
    | _ -> error loc ("`" ^ name ^ "` expects 2 Integers arguments") in
  add_builtin_function name f 2


let _ = add_binary_iop "+"  (+);
        add_binary_iop "-"  (-);
        add_binary_iop "*" ( * );
        add_binary_iop "/"  (/)

let make_symbol loc depth args_val  =
    (* symbol is a simple string *)
    let lxp = match args_val with
        | [r] -> r
        | _ -> error loc ("symbol_ expects 1 argument") in

        match lxp with
            | Vstring(str) -> Vsexp(Symbol(loc, str))
            | _ -> value_error loc lxp "symbol_ expects one string as argument"

let make_node loc depth args_val    =

    let op, tlist = match args_val with
        | [Vsexp(op); lst] -> op, lst
        | op::_  -> value_error loc op "node_ expects one 'Sexp' got: "
        | _ -> typer_unreachable "-" in

    (* value_print tlist; print_string "\n"; *)

    let args = v2o_list tlist in

    let s = List.map (fun g -> match g with
        | Vsexp(sxp)  -> sxp
        (* eval transform sexp into those... *)
        | Vint (i)    -> Integer(dloc, i)
        | Vstring (s) -> String(dloc, s)
        | _ ->
          (* print_rte_ctx ctx; *)
          value_error loc g "node_ expects 'List Sexp' second as arguments") args in

        Vsexp(Node(op, s))

let make_string loc depth args_val  =
    let lxp = match args_val with
        | [r] -> r
        | _ -> error loc "string_ expects 1 argument" in

        match lxp with
            | Vstring(str) -> Vsexp(String(loc, str))
            | _ -> value_error loc lxp "string_ expects one string as argument"

let make_integer loc depth args_val =
    let lxp = match args_val with
        | [r] -> r
        | _ -> error loc "integer_ expects 1 argument" in

        match lxp with
            | Vint(str) -> Vsexp(Integer(loc, str))
            | _ -> value_error loc lxp "integer_ expects one string as argument"

let make_float loc depth args_val   = Vdummy
let make_block loc depth args_val   = Vdummy

(* FIXME: We're not using predef here.  This will break if we change
 * the definition of `Bool` in builtins.typer.  *)
let ttrue = Vcons ((dloc, "true"), [])
let tfalse = Vcons ((dloc, "false"), [])
let o2v_bool b = if b then ttrue else tfalse

let string_eq loc depth args_val =
    match args_val with
        | [Vstring(s1); Vstring(s2)] -> o2v_bool (s1 = s2)
        | _ -> error loc "string_eq expects 2 strings"

let int_eq loc depth args_val =
    match args_val with
        | [Vint(s1); Vint(s2)] -> o2v_bool (s1 = s2)
        | _ -> error loc "int_eq expects 2 integer"

let sexp_eq loc depth args_val =
    match args_val with
    | [Vsexp (s1); Vsexp (s2)] -> o2v_bool (sexp_equal s1 s2)
    | _ -> error loc "sexp_eq expects 2 sexp"

let open_impl loc depth args_val =

  let file, mode = match args_val with
    | [Vstring(file_name); Vstring(mode)] -> file_name, mode
    | _ -> error loc "open expects 2 strings" in

   (* open file *) (* return a file handle *)
   Vcommand(fun () ->
      match mode with
        | "r" -> Vin(open_in file)
        | "w" -> Vout(open_out file)
        | _ -> error loc "wrong open mode")

let read_impl loc depth args_val =

  let channel = match args_val with
    | [Vin(c); _] -> c
    | _ ->
      List.iter (fun v -> value_print v; print_string "\n") args_val;
        error loc "read expects an in_channel" in

  let line = input_line channel in
    Vstring(line)

let write_impl loc depth args_val =

  let channel, msg = match args_val with
    | [Vout(c); Vstring(msg)] -> c, msg
    | _ ->
      List.iter (fun v -> value_print v) args_val;
        error loc "read expects an out_channel" in

    fprintf channel "%s" msg;
      Vdummy

let rec _eval lxp (ctx : Env.runtime_env) (trace : eval_debug_info): (value_type) =

    let trace = append_eval_trace trace lxp in
    let tloc = elexp_location lxp in
    let eval lxp ctx = _eval lxp ctx trace in

    (if (rec_depth trace) > (!_eval_max_recursion_depth) then
        fatal tloc "Recursion Depth exceeded");

    (* Save current trace in a global variable. If an error occur,
       we will be able to retrieve the most recent trace and context *)
    _global_eval_ctx := ctx;
    _global_eval_trace := trace;

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
          let nctx = _eval_decls decls ctx trace in
            eval inst nctx

        (* Function call *)
        | Call (f, args) ->
          (* we need to keep the trace from f and args evaluation
           * else the trace will be truncated.
           * we use _global_eval_trace to keep in memory previous steps *)
          let ef = _eval f ctx trace in
          let eargs = (List.map (fun e -> _eval e ctx (get_trace ())) args) in
            eval_call (elexp_location f) f (get_trace ())
                      ef
                      eargs

        (* Case *)
        | Case (loc, target, pat, dflt)
          -> (eval_case ctx trace loc target pat dflt)

        | Type -> Vcons((tloc, "Unit"), [])


and eval_var ctx lxp v =
    let ((loc, name), idx) = v in
    try get_rte_variable (Some name) (idx) ctx
    with e ->
      elexp_fatal loc lxp
        ("Variable: " ^ name ^ (str_idx idx) ^ " was not found ")

(* unef: unevaluated function (to make the trace readable) *)
and eval_call loc unef i f args =
  match f, args with
  (* return result of eval *)
  | _, [] -> f

  | Vcons (n, fields), _
    -> Vcons (n, List.append fields args)

  | Closure (x, e, ctx), v::vs
    -> let rec bindargs e vs ctx = match (vs, e) with
       | (v::vs, Lambda ((_, x), e))
         (* "Uncurry" on the fly.  *)
         -> bindargs e vs (add_rte_variable (Some x) v ctx)
       | ([], _) ->
        let trace = append_typer_trace i unef in
        _eval e ctx trace
       | _ -> eval_call loc unef i (_eval e ctx i) vs in
     bindargs e vs (add_rte_variable (Some x) v ctx)

  | Vbuiltin (name), args
    -> (try let (builtin, arity) = SMap.find name !builtin_functions in
           let nargs = List.length args in
           if nargs = arity then
             builtin loc i args        (* Fast common case.  *)
           else if nargs > arity then
             let rec split n vs acc = match (n, vs) with
               | 0, _ -> let v = eval_call loc unef i f (List.rev acc) in
                        eval_call loc unef i v vs
               | _, (v::vs) -> split (n - 1) vs (v::acc)
               | _ -> error loc "Impossible!"
             in split nargs args []
           else
             let rec buildctx args ctx = match args with
               | [] -> ctx
               | arg::args -> buildctx args (add_rte_variable None arg ctx) in
             let rec buildargs n =
               if n >= 0
               then (Var ((loc, "<dummy>"), n))::buildargs (n - 1)
               else [] in
             let rec buildbody n =
               if n > 0 then
                 Lambda ((loc, "<dummy>"), buildbody (n - 1))
               else Call (Builtin (dloc, name), buildargs (arity - 1)) in
             Closure ("<dummy>",
                      buildbody (arity - nargs - 1),
                      buildctx args Myers.nil)

       with Not_found ->
            error loc ("Requested Built-in `" ^ name ^ "` does not exist")
          | e -> error loc ("Exception thrown from primitive `" ^ name ^"`"))

  | _ -> value_fatal loc f "Trying to call a non-function!"

and eval_case ctx i loc target pat dflt =
    (* Eval target *)
    let v = _eval target ctx i in

    (* extract constructor name and arguments *)
    let ctor_name, args = match v with
        | Vcons((_, cname), args)  -> cname, args
        | _ -> elexp_fatal loc target "Target is not a Constructor" in

    (*  Get working pattern *)
    try let (_, pat_args, exp) = SMap.find ctor_name pat in
        (* build context (List.fold2 has problem with some cases)  *)
        (* This is more robust                                     *)
        let rec fold2 nctx pats args =
            match pats, args with
            | pat::pats, arg::args
              -> let nctx = add_rte_variable (match pat with
                                             | Some (_, name) -> Some name
                                             | _ -> None) arg nctx in
                fold2 nctx pats args
            (* Errors: those should not happen but they might  *)
            (* List.fold2 would complain. we print more info   *)
            | _::_, [] -> warning loc "a) Eval::Case Pattern Error"; nctx
            | [], _::_ -> warning loc "b) Eval::Case Pattern Error"; nctx
            (* Normal case *)
            | [], [] -> nctx in

        let nctx = fold2 ctx pat_args args in
            _eval exp nctx i

    (* Run default *)
    with Not_found -> (match dflt with
        | Some (var, lxp)
          -> let var' = match var with None -> None | Some (_, n) -> Some n in
            _eval lxp (add_rte_variable var' v ctx) i
        | _ -> error loc "Match Failure")

and build_arg_list args ctx i =
    (*  _eval every args *)
    let arg_val = List.map (fun (k, e) -> _eval e ctx i) args in

    (*  Add args inside context *)
    List.fold_left (fun c v -> add_rte_variable None v c) ctx arg_val

and _eval_decls (decls: (vdef * elexp) list)
                        (ctx: runtime_env) i: runtime_env =

    let n = (List.length decls) - 1 in

    (* Read declarations once and push them *)
    let nctx = List.fold_left (fun ctx ((_, name), _) ->
      add_rte_variable (Some name) Vdummy ctx) ctx decls in

    List.iteri (fun idx ((_, name), lxp) ->
      let v = _eval lxp nctx i in
      let offset = n - idx in
        ignore (set_rte_variable offset (Some name) v nctx)) decls;

        nctx

(* -------------------------------------------------------------------------- *)
(*              Builtin Implementation  (Some require eval)                   *)

and bind_impl loc depth args_val =
  let trace_dum = (Var ((loc, "<dummy>"), -1)) in

  match args_val with
  | [Vcommand (cmd); callback]
    -> (* bind returns another Vcommand *)
     Vcommand (fun () -> eval_call loc trace_dum depth callback [cmd ()])
  | _ -> error loc "Wrong number of args or wrong first arg value in `bind`"

and run_io loc depth args_val =

  let io, ltp = match args_val with
    | [io; ltp] -> io, ltp
    | _ -> error loc "run-io expects 2 arguments" in

  let cmd = match io with
    | Vcommand (cmd) -> cmd
    | _ -> error loc "run-io expects a monad as first argument" in

  (* run given command *)
  let _ = cmd () in

  (* return given type *)
    ltp

(* Sexp -> (Sexp -> List Sexp -> Sexp) -> (String -> Sexp) ->
    (String -> Sexp) -> (Int -> Sexp) -> (Float -> Sexp) -> (List Sexp -> Sexp)
        ->  Sexp *)
and sexp_dispatch loc depth args =
    let eval a b = _eval a b depth in
    let sxp, nd, sym, str, it, flt, blk, rctx = match args with
        | [sxp; Closure(_, nd, rctx); Closure(_, sym, _);
                Closure(_, str, _); Closure(_, it, _);
                Closure(_, flt, _); Closure(_, blk, _)] ->
            sxp, nd, sym, str, it, flt, blk, rctx
        | _ ->  error loc "sexp_dispatch expects 7 arguments" in

    let sxp = match sxp with
        | Vsexp(sxp)   -> sxp
        | _ -> value_fatal loc sxp "sexp_dispatch expects a Sexp as 1st arg" in

    match sxp with
        | Node    (op, s)    ->(
            let rctx = add_rte_variable None (Vsexp(op)) rctx in
            let rctx = add_rte_variable None (o2v_list s) rctx in
                match eval nd rctx with
                    | Closure(_, nd, _) -> eval nd rctx
                    | _ -> error loc "Node has 2 arguments")

        | Symbol  (_ , s)    ->
             eval sym (add_rte_variable None (Vstring(s)) rctx)
        | String  (_ , s)    ->
             eval str (add_rte_variable None (Vstring(s)) rctx)
        | Integer (_ , i)    ->
             eval it (add_rte_variable None (Vint(i)) rctx)
        | Float   (_ , f)    ->
             eval flt (add_rte_variable None (Vfloat(f)) rctx) (*
        | Block   (_ , s, _) ->
             eval blk (add_rte_variable None (o2v_list s)) *)
        | _ -> error loc "sexp_dispatch error"

(* -------------------------------------------------------------------------- *)
and print_eval_result i lxp =
    print_string "     Out[";
    ralign_print_int i 2;
    print_string "] >> ";
    value_print lxp; print_string "\n";

and print_typer_trace' trace =

  let trace = List.rev trace in

  print_string (Fmt.make_title "Typer Trace");
  print_string (Fmt.make_sep '-');

  let _ = List.iteri (fun i expr ->
    print_string "    ";
    Fmt._print_ct_tree i; print_string "+- ";
    print_string ((elexp_string expr) ^ "\n")) trace in

  print_string (Fmt.make_sep '=')

and print_typer_trace trace =
  match trace with
    | Some t -> print_typer_trace' t
    | None -> let (a, b) = !_global_eval_trace in
      print_typer_trace' b

and print_trace title trace default =
  (* If no trace is provided take the most revent one *)
  let trace = match trace with
    | Some trace -> trace
    | None -> default in

  (* Trace is upside down by default *)
  let trace = List.rev trace in

  (* Now eval trace and lparse trace are the same *)
  let print_trace = (fun type_name type_string type_loc i expr ->
    (* Print location info *)
    print_string ("    [" ^ (loc_string (type_loc expr)) ^ "] ");

    (* Print call trace visualization *)
    Fmt._print_ct_tree i; print_string "+- ";

    (* Print element *)
    print_string ((type_name expr) ^ ": " ^ (type_string expr) ^ "\n")
  ) in

  let elexp_trace = print_trace elexp_name elexp_string elexp_location in

  (* Print the trace*)
  print_string (Fmt.make_title title);
  print_string (Fmt.make_sep '-');
  let _ = List.iteri elexp_trace trace in
  print_string (Fmt.make_sep '=')

and print_eval_trace trace =
    let (a, b) = !_global_eval_trace in
      print_trace " EVAL TRACE " trace a

let _ = List.iter (fun (name, f, arity) -> add_builtin_function name f arity)
                  [
                    ("block_"        , make_block, 1);
                    ("symbol_"       , make_symbol, 1);
                    ("string_"       , make_string, 1);
                    ("integer_"      , make_integer, 1);
                    ("float_"        , make_float, 1);
                    ("node_"         , make_node, 2);
                    ("sexp_dispatch_", sexp_dispatch, 7);
                    ("string_eq"     , string_eq, 2);
                    ("int_eq"        , int_eq, 2);
                    ("sexp_eq"       , sexp_eq, 2);
                    ("open"          , open_impl, 2);
                    ("bind"          , bind_impl, 2);
                    ("run-io"        , run_io, 2);
                    ("read"          , read_impl, 2);
                    ("write"         , write_impl, 2);
                  ]

let eval lxp ctx = _eval lxp ctx ([], [])

let debug_eval lxp ctx =
    try eval lxp ctx
    with e -> (
        print_rte_ctx (!_global_eval_ctx);
        print_eval_trace None;
        raise e)


let eval_decls decls ctx = _eval_decls decls ctx ([], [])

let eval_decls_toplevel (decls: (vdef * elexp) list list) ctx =
  (* Add toplevel decls function *)
  List.fold_left (fun ctx decls ->
    eval_decls decls ctx) ctx decls

(*  Eval a list of lexp *)
let eval_all lxps rctx silent =
    let evalfun = if silent then eval else debug_eval in
    List.map (fun g -> evalfun g rctx) lxps


let varname s = match s with Some (_, v) -> v | _ -> "<anon>"

(* build a rctx from a lctx.  *)
(* FIXME: `eval` with a disabled runIO, and then memoize, memoize, ...  *)
let from_lctx (ctx: elab_context): runtime_env =
    let (_, lctx) = ctx in
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
               -> warning dloc ("No definition to compute the value of `"
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
