(* typecheck.ml --- Check a Lexp expression's type

Copyright (C) 2011-2016  Free Software Foundation, Inc.

Author: Stefan Monnier <monnier@iro.umontreal.ca>
Keywords: languages, lisp, dependent types.

This file is part of Typer.

Typer is free software; you can redistribute it and/or modify it under the
terms of the GNU General Public License as published by the Free Software
Foundation, either version 3 of the License, or (at your option) any
later version.

Typer is distributed in the hope that it will be useful, but WITHOUT ANY
WARRANTY; without even the implied warranty of MERCHANTABILITY or FITNESS
FOR A PARTICULAR PURPOSE.  See the GNU General Public License for
more details.

You should have received a copy of the GNU General Public License along with
this program.  If not, see <http://www.gnu.org/licenses/>.  *)

open Util
open Lexer
open Sexp
open Pexp
open Myers
(* open Grammar *)
open Lexp
(* open Unify *)

let conv_erase = true              (* If true, conv ignores erased terms. *)

let rec lexp_conv_arglist_p s1 s2 args1 args2 : bool =
  List.fold_left2
    (fun eqp (ak1,_,t1) (ak2,_,t2) ->
      eqp && ak1 = ak2 && lexp_conv_p s1 t1 s2 t2)
    true args1 args2

(* Returns true if e₁ and e₂ are equal (upto alpha/beta/...).  *)
and lexp_conv_p (s1:subst) (s2:subst) e1 e2 : bool =
  (* e1 == e2    !! Looks obvious, but can fail because of s1 and s2 !!  *)
  match (e1, e2) with
    | (Imm (Integer (_, i1)), Imm (Integer (_, i2))) -> i1 = i2
    | (Imm (Float (_, i1)), Imm (Float (_, i2))) -> i1 = i2
    | (Imm (String (_, i1)), Imm (String (_, i2))) -> i1 = i2
    (* | (Var (_, v1), Var (_, v2)) ->
     *    v1 = v2
     *    || (match try fst (VMap.find v1 env) with _ -> None with
     *       | Some e1 -> lexp_conv_p e1 e2
     *       | None -> match try fst (VMap.find v2 env) with _ -> None with
     *                | Some e2 -> lexp_conv_p e1 e2
     *                | None -> v2 = VMap.find v1 s)
     * | (Var (_, v1), _)
     *   -> (match try fst (VMap.find v1 env) with _ -> None with
     *       | Some e1 -> lexp_conv_p e1 e2
     *       | None -> false)
     *  | (_, Var (_, v2))
     *    -> (match try fst (VMap.find v2 env) with _ -> None with
     *       | Some e2 -> lexp_conv_p e1 e2
     *       | None -> false)
     *  | (Cons (t1, (_, tag1)), Cons (t2, (_, tag2)))
     *    -> tag1 = tag2 && lexp_conv_p t1 t2
     *  | (Case (_,e1,t1,branches1,default1), Case (_,e2,t2,branches2,default2))
     *    -> lexp_conv_p e1 e2
     *      && (match (default1, default2) with
     *         | (None, None) -> true
     *         | (Some e1, Some e2) -> lexp_conv_p e1 e2
     *         | _ -> false)
     *      && (conv_erase || lexp_conv_p t1 t2)
     *      && SMap.equal
     *          (fun (_, args1, e1) (_, args2, e2)
     *           -> lexp_conv_p e1 e2)
     *          branches1 branches2
     *  | (Inductive (_, id1, args1, cases1), Inductive (_, id2, args2, cases2))
     *    -> id1 = id2
     *      && lexp_conv_arglist_p args1 args2
     *      && SMap.equal lexp_conv_arglist_p
     *                   cases1 cases2
     *  | (Lambda (Aerasable,_,_,e1), Lambda (Aerasable,_,_,e2)) when conv_erase
     *    -> lexp_conv_p e1 e2
     *  | (Lambda (ak1,(_,v1),t1,e1), Lambda (ak2,(_,v2),t2,e2))
     *    -> ak1 = ak2
     *      && (conv_erase || lexp_conv_p t1 t2)
     *      && lexp_conv_p e1 e2
     *  | (Call (f1, args1), Call (f2, args2))
     *    -> lexp_conv_p f1 f2
     *      && List.length args1 = List.length args2
     *      && List.fold_left2 (fun eqp (ak1,a1) (ak2,a2) ->
     *                         eqp && ak1 = ak2
     *                         && ((conv_erase && ak1 = Aerasable)
     *                            || lexp_conv_p a1 a2))
     *                        true args1 args2
     *  | (Arrow (ak1,v1,t11,_,t21), Arrow (ak2,v2,t12,_,t22))
     *    -> ak1 = ak2
     *      && lexp_conv_p t11 t12
     *      && lexp_conv_p t21 t22
     *  | (Let (_,decls1,body1), Let (_,decls2,body2))
     *    -> List.length decls1 = List.length decls2
     *      && List.fold_left2
     *          (fun eqp (_,e1,t1) (_,e2,t2) ->
     *            eqp
     *            && lexp_conv_p e1 e2
     *            && lexp_conv_p t1 t2)
     *          (lexp_conv_p body1 body2)
     *          decls1 decls2 *)
     | (_, _) -> false

(* "lexp_check ctx e t" should be read as "Δ ⊢ e : τ"  *)
let rec lexp_check ctx e t =
  match e with
  | _ -> ()
