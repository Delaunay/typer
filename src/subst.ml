(* subst.ml --- Substitutions for Lexp

Copyright (C) 2016  Free Software Foundation, Inc.

Author: Stefan Monnier <monnier@iro.umontreal.ca>

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

module U = Util


(* Suspensions definitions.
 *
 *   ol: old embedding level ('associate' level, length with environement)
 *   nl: new ....
 *
 *   n: A Natural Number
 *   i: A positive integer
 *
 *  t ::= c             :
 *       #i             : Debruijn Index variable bound by the ith abstraction
 *       (t, t)         : Applications
 *       (λ t)          : Abstractions
 *       [t, n, n, e]   : Suspensions
 *
 *                                length                    level
 *  e ::= nil               : 0                       : 0
 *       (t, n)::e          : n + len(e)              : n
 *       {e1, nl, ol, e2}   : len(e1) + len(e2) - nl  : lev(e1) + nl - ol
 *
 *       level is the dbi index ?
 *
 * Substitutions Compositions definitions.
 *
 * a ::= 1
 *       a b
 *       (λ a)    :
 *       a[s]     :
 *
 * s ::= id       : identity
 *       a . s    : cons replace dbi_idx = 0 by a use s for the rest
 *       s o t    : Composition
 *       shift    : dbi_index + 1
 *)
(* Substitutions.
 *
 * There are many different ways to implement a calculus with explicit
 * substitutions, with tradeoffs between complexity of implementation,
 * performance etc...
 *
 * The "fine-grained notation" version of the suspension calculus uses
 * The following special rules:
 *
 *    (λ [t₁, ol+1, nl+1, @nl::e]) t₂     ==>   [t₁, ol+1, nl, (t₂,nl)::e]
 *    [[t, ol, nl, e], 0, nl', nil]  ==>   [t, ol, nl+nl', e]
 *
 * Alternate rules:
 *
 *    [(λ t₁), ol, nl, e]) t₂        ==>   [t₁, ol+1, nl, (t₂,nl)::e]
 *
 * The normal beta rule is:
 *
 *    (λ t₁) t₂                      ==>   [t₁, 1, 0, (t₂,0) :: nil]
 *
 * which would be instantiated to
 *
 *    (λ [t₁, ol, nl, e]) t₂    ==>   [[t₁, ol, nl, e], 1, 0, (t₂,0) :: nil]
 *
 * So we could do it as follows:
 *
 *    (λ [t₁ σ₁]) t₂   ==>  [t₁ ((1, 0, (t₂::nil)) ∘ σ₁)]
 *    ((1, 0, (t₂::nil)) ∘ (ol+1, nl+1, e)  ==> (ol₁, nl, (t₂,nl)::e)
 *
 * Rules used in the "no merging" version:
 *
 *    (λ t₁) t₂                      ==>   [t₁, 1, 0, (t₂,0) :: nil]
 *    (λ [t₁, ol+1, nl+1, @nl::e]) t₂  ==>   [t₁, ol+1, nl, (t₂,nl)::e]
 *    [t, 0, 0, nil]                 ==>   t
 *    [#i, ol, nl, e]                ==>   #(i-ol+nl)    if i>ol
 *    [#i, ol, nl, e]                ==>   #(nl - j)     if e.i = @j'
 *    [#i, ol, nl, e]          ==> [t, 0, nl - j, nil]   if e.i = (t,j)
 *    [λt, ol, nl, e]                ==>   λ[t, ol+1, nl+1, @nl :: e]
 *    [[t, ol, nl, e], 0, nl', nil]  ==>   [t, ol, nl+nl', e]
 *
 * First simplification: get rid of `ol`!
 *
 *    (λ t₁) t₂               ==>   [t₁, 0, (t₂,0)::nil]
 *    [#i, nl, e]             ==>   [t, nl - j, nil]     if e.i = (t,j)
 *    [λt, nl, e]             ==>   λ[t, nl+1, @nl::e]
 *
 *    (λ [t₁, nl+1, @nl::e]) t₂  ==>   [t₁, nl, (t₂,nl)::e]
 *    [(λ t₁), nl, e]) t₂     ==>   [t₁, nl, (t₂,nl)::e]
 *    [[t, nl, e], nl', nil]  ==>   [t, nl+nl', e]
 *
 *    [t, 0, nil]             ==>   t
 *    [#i, nl, e]             ==>   #(i-len(e)+nl)       if i>len(e)
 *    [#i, nl, e]             ==>   #(nl - j)            if e.i = @j'
 *
 * Re-introduce subst-merging.  So we currently have two merging rules:
 *
 *    ((0, (t₂::nil)) ∘ (nl+1, e)  ==>  (nl, (t₂,nl)::e)    if e≠nil
 *    (nl, e) ∘ (nl', nil)         ==>  (nl+nl', e)
 *
 * What do these substitutions mean?
 *
 *    (N, nil)  ==  shift N
 *    (0, e)    ==  replace nearest N vars with values from `e`
 *    (nl+1, @nl::e)  ==  lift e
 *    (nl, e)  ==  shift (nl - ol) (ol, e)   if ol = lvl(e)
 *
 * Another way to look at it:
 *
 *    (λ t₁) t₂               ==>   [t₁, t₂::nil]
 *    [λt, σ]                 ==>   λ[t, lift σ]
 *
 *    (λ [t₁, lift σ]) t₂     ==>   [t₁, t₂::σ]
 *    [(λ t₁), σ]) t₂         ==>   [t₁, t₂::σ]
 *    [[t, σ], shift n nil]   ==>   [t, shift n σ]
 *
 *    [t, id]                 ==>   t
 *    [#0, t::σ]              ==>   t
 *    [#i, t::σ]              ==>   [#i-1, σ]
 *    [#0, lift σ]            ==>   #0
 *    [#i, lift σ]            ==>   [[#i-1, σ], shift 1 nil]
 *    [#i, shift N σ]         ==>   [[#i, σ], shift N nil]
 *
 * I guess I'm leaning towards a kind of λσ, but with
 *
 *    σ = nil | σ ↑n | a·σ
 *
 * where lift σ  ==  #0·(σ ∘ nil ↑)  == #0·(σ ↑)
 *   and   σ ↑n  ==  (σ ∘ ↑n)
 *   and     #n  ==  [#0, ↑n]
 *
 *    (λt₁)t₂       ==>  [t₁, t₂·nil]
 *    [λt, σ]       ==>  λ[t, lift σ]
 *    [t, nil]      ==>  t
 *    [#0, t·σ]     ==>  t
 *    [#i+1, t·σ]   ==>  [#i, σ]    (because => [[#i, ↑] t·σ] => [#i, ↑ ∘ t·σ])
 *    [#i, σ ↑n]    ==>  [[#i, σ], ↑n]
 *
 * Merging rules:
 *
 *    nil ∘ σ             ==>  σ
 *    σ ∘ nil             ==>  σ
 *    (σ ↑n₂) ↑n₁         ==>  σ ↑(n₁+n₂)
 *    σ ↑n₁ ∘ nil ↑n₂     ==>  σ ↑(n₁+n₂)
 *    σ₁ ↑n₁ ∘ (a·σ₂) ↑n₂ ==>  σ₁ ↑(n₁-1) ∘ σ₂ ↑n₂
 *    σ₁ ↑n ∘ a·σ₂        ==>  σ₁ ↑(n-1) ∘ σ₂
 *    a·σ₁ ∘ σ₂ ↑n        ==>  (a·σ₁ ∘ σ₂) ↑n
 *    a·σ₁ ∘ σ₂           ==>  [a, σ₂]·(σ₁ ∘ σ₂)
 *
 *    σ ∘ nil ↑n          ==>  σ ↑n
 *
 * The optimisations used in FLINT would translate to:
 *
 *    [λt₁, σ] t₂         ==> (λ[t₁, lift σ]) t₂
 *                        ==> [t₁, (lift σ) ∘ t₂·nil]
 *                        ==> [t₁, #0·(σ ↑) ∘ t₂·nil]
 *                        ==> [t₁, [#0, t₂·nil]·(σ ↑ ∘ t₂·nil)]
 *                        ==> [t₁, t₂·σ]
 *    [[t, σ], nil ↑n]    ==> [t, σ ∘ nil ↑n]
 *                        ==> [t, σ ↑n]
 *
 * Confluence:
 *
 *    a·σ₁ ∘ σ₂ ↑n        ==>  (a·σ₁ ∘ σ₂) ↑n
 *    a·σ₁ ∘ σ₂ ↑n        ==>  [a, σ₂ ↑n]·(σ₁ ∘ σ₂ ↑n)
 *
 * so we also need a rule
 *
 *     (a·σ₁ ∘ σ₂) ↑n    <==>  [a, σ₂ ↑n]·(σ₁ ∘ σ₂ ↑n)
 *
 * for confluence
 *)

(* We define here substitutions which take a variable within a source context
 * Δₛ and should return an expression valid in target context Δₜ.
 *
 * The current implementation only handles a very limited subset of such
 * substitutions.  One of the many limitations is that we can only encode
 * substitutions which map variables to variables.
 *)

type db_index = int             (* DeBruijn index.  *)
type db_offset = int            (* DeBruijn index offset.  *)

(* Substitution, i.e. a mapping from db_index to 'a
 * In practice, 'a is always lexp, but we keep it as a paramter:
 * - for better modularity of the code.
 * - to break a mutual dependency between the Lexp and the Subst modules.  *)
type 'a subst = (* lexp subst *)
  (* Lift (n,m) increases indices≥N by M.
   * IOW, it takes variables from a source context Δₛ₁Δₛ₂ to a destination
   * context Δₛ₁ΔₜΔₛ₂ where Δₛ₂ has size N and Δₜ has size M.  *)
  | Identity
  | Cons of 'a * 'a subst
  | Shift of db_offset * 'a subst
  (* | Lift of db_index * db_offset *)

(* Apply a substitution.  Also called `lookup`.  *)
let apply (mkVar : 'b -> db_index -> 'a)
          (mkShift: db_offset -> 'a -> 'a)
          (s: 'a subst) (l : 'b) (v:db_index) : 'a =
  let rec apply' (o:db_offset) (s: 'a subst) (v:db_index) : 'a =
    match s with
    | Identity -> mkVar l (v+o)
    | Shift (o', s) -> apply' (o+o') s v
    | Cons (e, s) -> if v>0 then apply' o s (v-1)
                    else mkShift o e
  in apply' 0 s v

let mkShift (m:db_offset) s =
  match s with Shift (n, s') -> Shift (n+m, s')
             | _ -> if m>0 then Shift (m, s) else s

(* A substitution which adds M to every deBruijn index.
 * I.e. one that takes variables from a context Δₛ to an extended
 * context ΔₛΔₜ where Δₜ has size M.  *)
let shift (m:db_offset) = mkShift m Identity

(* The trivial substitution which doesn't do anything.  *)
let identity = Identity

let identity_p s = match s with | Identity -> true | _ -> false

(* Compose two substitutions.  This implements the merging rules.
 * Returns s₁ ∘ s₂  (i.e. s₁ is applied before s₂) *)
let compose (mkSusp : 'a -> 'a subst -> 'a)
            (s1: 'a subst) (s2: 'a subst) : 'a subst =
  let rec compose' (s1: 'a subst) (s2: 'a subst) : 'a subst =
    match s1, s2 with
    | (Identity, s2) -> s2
    | (s1, Identity) -> s1
    | (Shift (o1, s1), Shift (o2, Identity)) -> Shift (o1+o2, s1)
    | (s1, Shift (o, Identity)) -> Shift (o, s1)
    | (Shift (o1, s1), Shift (o2, Cons (e, s2)))
      -> compose' (mkShift (o1-1) s1) (mkShift o2 s2)
    | (Shift (o1, s1), Cons (e, s2)) -> compose' (mkShift (o1-1) s1) s2
    | (Cons (e, s1), Shift (o2, s2)) -> Shift (o2, compose' (Cons (e, s1)) s2)
    | (Cons (e, s1), s2) -> Cons (mkSusp e s2, compose' s1 s2)
    | (_, Shift (_, Shift (_, _))) -> U.internal_error "Nested Shift!"
  in compose' s1 s2

(* Adjust a substitution for use under one more binder.
 * I.e. take a substitution from Δs to Δₜ and return a substitution
 * from Δs,x to Δₜ,x.
 * Also known as `lift`.  *)
let sink (mkVar : 'b -> db_index -> 'a) (l:'b) (s:'a subst) =
  Cons (mkVar l 0, mkShift 1 s)

(* Return a substitution which replaces #0 with `e`.  *)
let substitute e = Cons (e, Identity)
