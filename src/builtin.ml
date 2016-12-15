(* builtin.ml --- Infrastructure to define built-in primitives
 *
 *      Copyright (C) 2016  Free Software Foundation, Inc.
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
 * There are several different issues with how to make the compiler's code
 * interact with code defined in Typer:
 *
 * ** Exporting primitives
 *
 * I.e. how to give a name and a type to a primitive implemented in OCaml
 *
 * There are several conflicting desires, here: we'd generally want the name,
 * the type (and the association) to be close to the primitive's definition, so
 * that adding a new primitive doesn't require changes in many files.
 *
 * But it's also good to have the type written in some Typer file, both for
 * the convenience of writing the code in Typer syntax with typer-mode support,
 * and also because error messages can easily refer to that file, so it can be
 * used for user-documentation.
 *
 * ** Importing definitions
 *
 * Sometimes we want some part of the core to be defined in Typer and used
 * from OCaml.  Examples are the type `Macro` along with the `expand-macro`
 * function or the type Bool/true/false used with various primitives.
 *
 * ** Intertwined dependencies
 *
 * The various importing/exporting might need to be interlaced.  Some exported
 * functions's types will want to refer to imported types, while some imported
 * definitions may want to refer to exported definitions.  So we'd like to be
 * able to do them in "any" order.
 *
 * ---------------------------------------------------------------------------*)

open Util

open Sexp   (* Integer/Float *)
open Pexp   (* arg_kind *)
module L = Lexp
module OL = Opslexp
open Lexp

module DB = Debruijn
module E = Env

let error loc msg = msg_error "BUILT-IN" loc msg; raise (internal_error msg)
let warning loc msg = msg_warning "BUILT-IN" loc msg

let predef_name = [
    "cons";
    "nil";
    "true";
    "false";
    "Macro";
    "expand_macro_";
]

(* FIXME: Actually, we should map the predefs to *values* since that's
 * where they're really needed!  *)
let predef_map : lexp SMap.t ref
  (* Pre-fill "Macro" with a dummy value, to avoid errors while reading
   * the builtins.typer file.  *)
  = ref (SMap.add "Macro" impossible SMap.empty)

let get_predef (name: string) (ctx: DB.elab_context) =
  try let r = (DB.get_size ctx) - !builtin_size - 0 in
      let p = SMap.find name (!predef_map) in
      mkSusp p (S.shift r)
  with Not_found -> error dummy_location ("\""^ name ^ "\" was not predefined")

let set_predef name lexp
  = predef_map := SMap.add name lexp (!predef_map)

(*                Builtin types               *)
let dloc    = DB.dloc

let op_binary t = mkArrow (Aexplicit, None, t, dloc,
                           mkArrow (Aexplicit, None, t, dloc, t))

let type_eq =
  let lv = (dloc, "l") in
  let tv = (dloc, "t") in
  mkArrow (Aerasable, Some lv,
           DB.type_level, dloc,
           mkArrow (Aerasable, Some tv,
                    mkSort (dloc, Stype (Var (lv, 0))), dloc,
                    mkArrow (Aexplicit, None,
                             Var (tv, 0), dloc,
                             mkArrow (Aexplicit, None,
                                      mkVar (tv, 1), dloc,
                                      mkSort (dloc, Stype (Var (lv, 3)))))))

let o2l_bool ctx b = get_predef (if b then "true" else "false") ctx

(* lexp Imm list *)
let o2l_list ctx lst =
    let tcons = get_predef "cons" ctx in
    let tnil  = get_predef "nil" ctx in

    let rlst = List.rev lst in
        List.fold_left (fun tail elem ->
            mkCall(tcons, [(Aexplicit, (Imm (elem)));
                           (Aexplicit, tail)])) tnil rlst

(* typer list as seen during runtime *)
let o2v_list lst =
  (* FIXME: We're not using predef here.  This will break if we change
   * the definition of `List` in builtins.typer.  *)
  List.fold_left (fun tail elem
                  -> E.Vcons ((dloc, "cons"), [E.Vsexp (elem); tail]))
                 (E.Vcons ((dloc, "nil"), []))
                 (List.rev lst)


(* Typer list to Ocaml list *)
let v2o_list v =
  let rec v2o_list acc v =
    match v with
    | E.Vcons ((_, "cons"), [hd; tl]) -> v2o_list (hd::acc) tl
    | E.Vcons ((_, "nil"), []) -> List.rev acc
    | _ -> print_string (E.value_name v); print_string "\n";
          E.value_print v;
          error dloc "List conversion failure'" in
  v2o_list [] v

(* Map of lexp builtin elements accessible via (## <name>).  *)
let lmap = ref (SMap.empty : (lexp * ltype) SMap.t)

let add_builtin_cst (name : string) (e : lexp)
  = let map = !lmap in
    assert (not (SMap.mem name map));
    let t = OL.check VMap.empty Myers.nil e in
    lmap := SMap.add name (e, t) map

let new_builtin_type name kind =
  let t = mkBuiltin ((dloc, name), kind, None) in
  add_builtin_cst name t;
  t

let register_builtin_csts () =
  add_builtin_cst "TypeLevel" DB.type_level;
  add_builtin_cst "TypeLevel.z" DB.level0;
  add_builtin_cst "Type" DB.type0;
  add_builtin_cst "Type1" DB.type1;
  add_builtin_cst "Int" DB.type_int;
  add_builtin_cst "Float" DB.type_float;
  add_builtin_cst "String" DB.type_string

let register_builtin_types () =
  let _ = new_builtin_type "Sexp" DB.type0 in
  let _ = new_builtin_type
            "IO" (mkArrow (Aexplicit, None, DB.type0, dloc, DB.type0)) in
  let _ = new_builtin_type "FileHandle" DB.type0 in
  let _ = new_builtin_type "Eq" type_eq in
  ()

let _ = register_builtin_csts ();
        register_builtin_types ()
