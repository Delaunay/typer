
open Lexp
open Util
module S = Subst

(** Provide inverse function for computing the inverse of a substitution
*)

(* Transformation *)

type inter_subst = lexp list (* Intermediate between "tree"-like substitution and fully flattened subsitution *)

let dummy_var = Var((dummy_location, "DummyVar"), -1)

type substIR = ((int * int) list * int)

(* toIr + flattenIr + to_list *)
(* TODO : find better name ?*)
let transfo (s: lexp S.subst) : substIR option =
  let rec transfo (s: lexp S.subst) (off_acc: int) (idx: int): substIR option =
    let valueOf (v: lexp): int =
      match v with
      | Var (_, v) -> v
      | _          -> assert false
    in let shiftVar (var: lexp) (offset: int): int = valueOf (mkSusp var (S.shift offset))
    in match s with
    | S.Cons (Var _ as v, s) ->
      (match transfo s off_acc (idx + 1) with
       | Some (tail, off) -> let newVar = shiftVar v off_acc
         in if newVar >= off then None
         else Some (((shiftVar v off_acc), idx)::tail, off)
        | None             -> None)
    | S.Shift (s, offset) -> transfo s (offset + off_acc) idx
    | S.Identity          -> Some ([], off_acc)
    | _                   -> None
  in transfo s 0 0

(* Inverse *)

(** Returns the number of element in a sequence of S.Cons
*)
let rec sizeOf (s: (int * int) list): int = List.length s

(** Returns a dummy variable with the db_index idx
*)
let mkVar (idx: int): lexp = Var((U.dummy_location, ""), idx)

(** Fill the gap between e_i in the list of couple (e_i, i) by adding
    dummy variables.
    With the exemple of the article :
    should return <code>(1,1)::(2, X)::(3,2)::(4,3)::(5, Z)::[]</code>

    @param l     list of (e_i, i) couples with gap between e_i
    @param size  size of the list to return
    @param acc   recursion accumulator
*)
let fill (l: (int * int) list) (nbVar: int) (shift: int): lexp S.subst option =
  let rec genDummyVar (beg_: int) (end_: int) (l: lexp S.subst): lexp S.subst =
    if beg_ < end_
    then S.cons (mkVar (nbVar + 1)) (genDummyVar (beg_ + 1) end_ l)
    else l
  in
  let fill_before (l: (int * int) list) (s: lexp S.subst) (nbVar: int): lexp S.subst option =
    match l with
    | []                      -> Some (genDummyVar 0 nbVar S.identity)
    | (i1, v1)::_ when i1 > 0 -> Some (genDummyVar 0 i1 s)
    | _                       -> Some s
  in let rec fill_after (l: (int * int) list) (nbVar: int) (shift: int): lexp S.subst option =
    match l with
    | (idx1, val1)::(idx2, val2)::tail when (idx1 = idx2)     -> None

    | (idx1, val1)::(idx2, val2)::tail when (idx2 - idx1) > 1 ->
      (match fill_after ((idx2, val2)::tail) nbVar shift with
        | None   -> None
        | Some s -> Some (S.cons (mkVar val1) (genDummyVar (idx1 + 1) idx2 s)))

    | (idx1, val1)::(idx2, val2)::tail                        ->
      (match fill_after ((idx2, val2)::tail) nbVar shift with
        | None   -> None
        | Some s -> Some (S.cons (mkVar val1) s))

    | (idx1, val1)::[] when (idx1 + 1) < nbVar                ->
      Some (S.cons (mkVar val1) (genDummyVar (idx1 + 1) nbVar (S.shift shift)))

    | (idx1, val1)::[]                                       ->
      Some (S.cons (mkVar val1) (S.shift shift))

    | []                                                     ->
      Some (S.shift shift)
  in match fill_after l nbVar shift with
  | None   -> None
  | Some s -> fill_before l s nbVar

(** Compute the inverse, if there is one, of the substitution.

    <code>s:S.subst, l:lexp, s':S.subst</code> where <code>l[s][s'] = l</code> and <code> inverse s = s' </code>
*)
let inverse (s: lexp S.subst) : lexp S.subst option =
  let sort = List.sort (fun (ei1, _) (ei2, _) -> compare ei1 ei2)
  in match transfo s with
  | None                   -> None
  | Some (cons_lst, shift_val) ->
    let size  = sizeOf cons_lst
    in fill (sort cons_lst) shift_val size
