(* myers.ml --- Myers's stacks, a.k.a random-access singly-linked lists

Copyright (C) 2014-2016  Free Software Foundation, Inc.

Author: Stefan Monnier <monnier@iro.umontreal.ca>
Keywords: list, containers

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

(* This package implements Eugene W. Myers's "stacks" which are like
 * standard singly-linked lists, except that they also provide efficient
 * lookup.  More specifically:
 *
 * cons and car are O(1), while (nthcdr N L) is O(min (N, log L))
 *
 * For details, see "An applicative random-access stack", Eugene W. Myers,
 * 1983, Information Processing Letters
 * http://citeseerx.ist.psu.edu/viewdoc/download?doi=10.1.1.188.9344&rep=rep1&type=pdf
 *)

type 'a myers =
  | Mnil
  (* | Mcons1 of 'a * 'a myers *)
  | Mcons of 'a * 'a myers * int * 'a myers

(* Contrary to Myers's presentation, we index from the top of the stack,
 * and we don't store the total length but the "skip distance" instead.
 * This makes `cons' slightly faster, and better matches our use for
 * debruijn environments.  *)

let nil = Mnil

let cons x l =
  match l with
  | Mcons (_, _, s1, Mcons (_, _, s2, l2)) when s1 >= s2
    -> Mcons (x, l, s1 + s2 + 1, l2)
  | _ -> Mcons (x, l, 1, l)

let car l =
  match l with
  | Mnil -> raise Not_found
  | Mcons (x, _, _, _) -> x

let cdr l =
  match l with
  | Mnil -> Mnil
  | Mcons (_, l, _, _) -> l

let case l n c =
  match l with
  | Mnil -> n ()
  | Mcons (x, l, _, _) -> c x l

let empty l = match l with | Mnil -> true | _ -> false

let rec nthcdr n l =
  match n,l with
  | 0, l -> l
  | _, Mnil -> Mnil
  | n, Mcons (_, _, s, l) when s <= n -> nthcdr (n - s) l
  | n, Mcons (_, l, _, _) -> nthcdr (n - 1) l

let nth n l = car (nthcdr n l)

(* This operation would be more efficient using Myers's choice of keeping
 * the length (instead of the skip-distance) in each node.  *)
let length l =
  let rec length' l n =
    match l with
    | Mnil -> n
    | Mcons (_, _, s, l) -> length' l (s + n)
  in length' l 0

(* Find the first element for which the predicate `p' is true.
 * "Binary" search, assuming the list is "sorted" (i.e. all elements after
 * this one also return true).  *)
let rec find p l =
  let rec find2 l1 l2 =
    match l1,l2 with
    | _, Mcons (x, l1, _, l2) when not (p x) -> find2 l1 l2
    | l, _ -> find1 l
  and find1 l =
    match l with
     | Mnil -> None
     | Mcons (x, _, _, _) when p x -> Some x
     | Mcons (_, l1, _, l2) -> find2 l1 l2
  in find1 l

(* Find the last node for which the predicate `p' is false.
 * "Binary" search, assuming the list is "sorted" (i.e. all elements after
 * this one also return true).  *)
let rec findcdr p l =
  let rec findcdr2 last l1 l2 =
    match l1,l2 with
    | _, (Mcons (x, l1, _, l2) as l) when not (p x) -> findcdr2 (Some l) l1 l2
    | l, _ -> findcdr1 last l
  and findcdr1 last l =
    match l with
     | Mnil -> last
     | Mcons (x, _, _, _) when p x -> last
     | Mcons (_, l1, _, l2) -> findcdr2 (Some l) l1 l2
  in findcdr1 None l

let rec fold_left f i l = match l with
  | Mnil -> i
  | Mcons (x, l, _, _) -> fold_left f (f i x) l

let rec fold_right f l i = match l with
  | Mnil -> i
  | Mcons (x, l, _, _) -> f x (fold_right f l i)

let map f l = fold_right (fun x l' -> cons (f x) l') l nil

let iteri f l = fold_left (fun i x -> f i x; i + 1) 0 l
