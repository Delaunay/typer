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
(* open Lexer *)
open Sexp
(* open Pexp *)
(* open Myers *)
(* open Grammar *)
open Lexp
open Builtin        (* type_float *)
(* open Unify *)
module S = Subst
module L = List

let conv_erase = true              (* If true, conv ignores erased terms. *)

let rec conv_arglist_p s1 s2 args1 args2 : bool =
  List.fold_left2
    (fun eqp (ak1,t1) (ak2,t2) ->
      eqp && ak1 = ak2 && conv_p' s1 s2 t1 t2)
    true args1 args2

(* Returns true if e₁ and e₂ are equal (upto alpha/beta/...).  *)
and conv_p' (s1:S.subst) (s2:S.subst) e1 e2 : bool =
  let conv_p = conv_p' s1 s2 in
  (* e1 == e2    !! Looks obvious, but can fail because of s1 and s2 !!  *)
  match (e1, e2) with
    | (Imm (Integer (_, i1)), Imm (Integer (_, i2))) -> i1 = i2
    | (Imm (Float (_, i1)), Imm (Float (_, i2))) -> i1 = i2
    | (Imm (String (_, i1)), Imm (String (_, i2))) -> i1 = i2
    | (SortLevel (sl1), SortLevel (sl2)) -> sl1 == sl2
    | (Sort (_, s1), Sort (_, s2)) -> s1 == s2
    | (Builtin (b1, s1, _), Builtin (b2, s2, _)) -> b1 == b2 && s1 == s2
    | (Var (_, v1), Var (_, v2)) -> S.apply s1 v1 = S.apply s2 v2
    | (Susp (s1', e1), e2) -> conv_p' (S.compose s1 s1') s2 e1 e2
    | (e1, Susp (s2', e2)) -> conv_p' s1 (S.compose s2 s2') e1 e2
    | (Arrow (ak1, vd1, t11, _, t12), Arrow (ak2, vd2, t21, _, t22))
      -> ak1 == ak2 && conv_p t11 t21
        && conv_p' (match vd1 with None -> s1 | _ -> S.sink s1)
                  (match vd2 with None -> s2 | _ -> S.sink s2)
                  t12 t22
    | (Lambda (ak1, _, t1, e1), Lambda (ak2, _, t2, e2))
      -> ak1 == ak2 && conv_p t1 t2 && conv_p' (S.sink s1) (S.sink s2) e1 e2
    | (Call (f1, args1), Call (f2, args2))
      -> conv_p f1 f2 && conv_arglist_p s1 s2 args1 args2
    | (Inductive (_, l1, args1, cases1), Inductive (_, l2, args2, cases2))
      -> let rec conv_args s1 s2 args1 args2 =
          match args1, args2 with
          | ([], []) -> true
          | ((ak1,_,t1)::args1, (ak2,_,t2)::args2)
            -> ak1 == ak2 && conv_p' s1 s2 t1 t2
              && conv_args (S.sink s1) (S.sink s2) args1 args2
          | _,_ -> false in
        let rec conv_fields s1 s2 fields1 fields2 =
          match fields1, fields2 with
          | ([], []) -> true
          | ((ak1,vd1,t1)::fields1, (ak2,vd2,t2)::fields2)
            -> ak1 == ak2 && conv_p' s1 s2 t1 t2
              && conv_fields (match vd1 with None -> s1 | _ -> S.sink s1)
                            (match vd2 with None -> s2 | _ -> S.sink s2)
                            fields1 fields2
          | _,_ -> false in
        l1 == l2 && conv_args s1 s2 args1 args2
        && SMap.equal (conv_fields s1 s2) cases1 cases2
    | (Cons (v1, l1), Cons (v2, l2)) -> l1 == l2 && conv_p (Var v1) (Var v2)
    (* FIXME: Various missing cases, such as Let, Case, and beta-reduction.  *)
    | (_, _) -> false

and conv_p e1 e2 = conv_p' S.identity S.identity e1 e2

type varbind =
  | Variable
  | ForwardRef
  | LetDef of lexp

let lookup_type ctx vref =
  let (_, i) = vref in
  let (_, _, _, t) = Myers.nth i ctx in
  Susp (S.shift (i + 1), t)

let assert_type e t t' =
  if conv_p t t' then ()
  else msg_error "TC" (lexp_location e) "Type mismatch"; ()

(* "check ctx e" should return τ when "Δ ⊢ e : τ"  *)
let rec check ctx e =
  (* let mustfind = assert_type e t in *)
  match e with
  | Imm (Float (_, _)) -> type_float
  | Imm (Integer (_, _)) -> type_int
  | SortLevel (_) -> type_level
  | Sort (l, Stype (SortLevel (SLn n)))
    -> Sort (l, Stype (SortLevel (SLn (1 + n))))
  | Builtin (_, _, t) -> t
  | Var v -> lookup_type ctx v
  | Susp (_, _) -> internal_error "Don't know how to check Susp"
  | Let (_, defs, e)
    -> let tmp_ctx =
        L.fold_left (fun ctx (v, e, t)
                     -> Myers.cons (0, Some v, ForwardRef, t) ctx)
                    ctx defs in
      let (new_ctx, _) =
        L.fold_left (fun (ctx,recursion_offset) (v, e, t)
                     -> let t' = check tmp_ctx e in
                       assert_type e t t';
                       (Myers.cons (recursion_offset, Some v, LetDef e, t) ctx,
                        recursion_offset - 1))
                    (ctx, L.length defs)
                    defs in
      check new_ctx e
  | Arrow (ak, v, t1, l, t2)
    -> (let k1 = check ctx t1 in
       let k2 = check (Myers.cons (0, v, Variable, t1) ctx) t2 in
       match k1, k2 with
       | (Sort (_, Stype (SortLevel (SLn n1))),
          Sort (_, Stype (SortLevel (SLn n2))))
         (* Basic predicativity rule.  *)
         -> Sort (l, Stype (SortLevel (SLn (max n1 n2))))
       | ( (Sort (_, StypeLevel), Sort (_, Stype (SortLevel (SLn _))))
         | (Sort (_, StypeLevel), Sort (_, StypeOmega))
         (* | (Sort (_, Stype (SortLevel (SLn _))), Sort (_, StypeOmega)) *))
         -> Sort (l, StypeOmega)
      )
  | Lambda (ak, ((l,_) as v), t, e)
    -> (match check ctx t with
       | Sort _ -> Arrow (ak, Some v, t, l,
                         check (Myers.cons (0, Some v, Variable, t) ctx) e))
  (* | _ -> let t' = check ctx e in
   *       if conv_p t t' then ()
   *       else msg_error "TC" (lexp_location e) "Type mismatch"; () *)

