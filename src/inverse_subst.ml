
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

(** Returns the db_index of the "inside" of a Var
*)
let idxOf (_, idx) = idx

(** Returns a list of couple (X, idx) where X go from beg_ to end_*)
let rec genDummyVar (beg_: int) (end_: int) (idx: int): (int * int) list =
  if beg_ < end_
  then (beg_, idx)::(genDummyVar (beg_ + 1) end_ idx)
  else []

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
let fill (l: (int * int) list) (size: int) (acc: (int * int) list): (int * int) list option =
  let genDummyVar beg_ end_ = genDummyVar beg_ end_ (size + 1)
  in
  let rec fill_before (l: (int * int) list) (size: int): (int * int) list =
    match l with
    | [] -> genDummyVar 0 size
    | (idx, val_)::tail -> (if idx > 0 then (genDummyVar 0 idx)@l
                            else l)
  and fill_after (l: (int * int) list) (size: int) (acc: (int * int) list): (int * int) list option =
    match l with
    | (idx1, val1)::(idx2, val2)::tail when (idx1 = idx2) -> None
    | (idx1, val1)::(idx2, val2)::tail ->
      let tail = (idx2, val2)::tail in
      let accu = if (idx2 - idx1) > 1
        then (acc@[(idx1, val1)]@(genDummyVar (idx1 + 1) idx2))
        else (acc@(idx1, val1)::[])
      in fill_after tail size accu
    | (idx1, val1)::[] -> if (idx1 + 1) < size
      then Some (acc@((idx1, val1)::(genDummyVar (idx1 + 1) size)))
      else Some (acc@[(idx1, val1)])
    | [] -> Some acc
  in fill_after (fill_before l size) size acc

(** Transform a (e_i, i) list to a substitution by transforming the list into Cons and
    adding a Shift.

    @param lst    list of couple (ei_, i) to transform
    @param shift  value of the shift
*)
let rec to_cons (lst: (int * int) list) (shift: int) : lexp S.subst option =
  match lst with
  | (_, i)::tail -> (match (to_cons tail shift) with
      | Some s -> Some (S.cons (mkVar i) s)
      | None -> None)
  | []           -> Some (S.shift shift)

(** Compute the inverse, if there is one, of the substitution.

    <code>s:S.subst, l:lexp, s':S.subst</code> where <code>l[s][s'] = l</code> and <code> inverse s = s' </code>
*)
let inverse (s: lexp S.subst) : lexp S.subst option =
  let sort = List.sort (fun (ei1, _) (ei2, _) -> compare ei1 ei2)
  in
  match transfo s with
  | None                   -> None
  | Some (cons_lst, shift_val) ->
    let size  = sizeOf cons_lst
    in match fill (sort cons_lst) shift_val [] with
    | None          -> None
    | Some cons_lst -> to_cons cons_lst size
