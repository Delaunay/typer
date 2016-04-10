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

(* We define here substitutions which take a variable within a source context
 * Δₛ and should return an expression valid in target context Δₜ.
 *
 * The current implementation only handles a very limited subset of such
 * substitutions.  One of the many limitations is that we can only encode
 * substitutions which map variables to variables.
 *)

type db_index = int             (* DeBruijn index.  *)
type db_offset = int            (* DeBruijn index offset.  *)

type subst =                     (* deBruijn substitution.  *)
  (* Lift (n,m) increases indices≥N by M.
   * IOW, it takes variables from a source context Δₛ₁Δₛ₂ to a destination
   * context Δₛ₁ΔₜΔₛ₂ where Δₛ₂ has size N and Δₜ has size M.  *)
  | Lift of db_index * db_offset

(* Apply a substitution.  In theory this should return a Lexp, but
 * since we can only map variables to variables, we just return a db_index.
 * This also saves us from a mutual-recursion between the Subst and Lexp
 * modules.  *)
let apply (s:subst) (v:db_index) : db_index =
  match s with
  | Lift (n,m) -> if v >= n then v + m else v

(* A substitution which adds M to every deBruijn index.
 * I.e. one that takes variables from a context Δₛ to an extended
 * context ΔₛΔₜ where Δₜ has size M.  *)
let shift m = Lift (0, m)

(* The trivial substitution which doesn't do anything.  *)
let identity = Lift (0,0)

(* Compose two substitutions.
 * Returns s₂ ∘ s₂ (i.e. s₂ is applied before s₁).  *)
let compose s1 s2 =
  match s1, s2 with
  | (Lift (_, 0), s2) -> s2
  | (s1, Lift (_, 0)) -> s1
  | (Lift (n1, m1), Lift (n2, m2)) ->
     if n1 >= n2 && n1 <= n2 + m2 then Lift (n2, m1 + m2)
     else U.internal_error "Unable to compose subst at different indices"

(* Adjust a substitution for use under one more binder.
 * I.e. take a substitution from Δs to Δₜ and return a substitution
 * from Δs,x to Δₜ,x *)
let sink s =
  match s with | Lift (n, m) -> Lift (n + 1, m)
