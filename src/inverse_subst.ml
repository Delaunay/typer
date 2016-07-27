
open Lexp
open Util
module S = Subst

(** Provide inverse function for computing the inverse of a substitution
*)

(* Transformation *)

type inter_subst = lexp list (* Intermediate between "tree"-like substitution and fully flattened subsitution *)

let dummy_var = Var((dummy_location, "DummyVar"), -1)

(** Make a Shift with Identity as "inner" substitution
 Returns Identity if the Shift offset is lower or equal to 0*)
let mkFinalShift (value: int): lexp S.subst =
  if value > 0
  then S.Shift (S.Identity, value)
  else S.Identity

(** Transform a subst into a more linear 'intermdiate representation':

    - a1.↑^\{x1\}(a2.↑^\{x2\}(a3.↑^\{x3\}id)) -> a1.(↑^\{x1\}a2).(↑^\{x2\}a3).↑^\{x3\}id

    or in ocaml-ish representation :

    - S.Cons(var, S.Shift(..., offset))  -> S.Cons(var, S.Shift(S.Identity, offset))::...::Identity
*)
let toIr (s: lexp S.subst) : inter_subst =
  let rec toIr s last_offset =
    match s with
    | S.Shift (s_1, offset) -> toIr s_1 (last_offset + offset)
    | S.Cons(Var _ as v, s_1) -> Susp(v, (S.mkShift S.Identity last_offset))::(toIr s_1 last_offset)
    | S.Identity -> [Susp(dummy_var, (S.mkShift S.Identity last_offset ))]
    | _ -> assert false
  in toIr s 0

(** Transform an 'intermediate representation' into a sequence of cons followed by a shift

    - a1.(↑^\{x1\}a2).(↑^\{x2\}a3).↑^\{x3\}id -> a1.a2.a3.(id ↑^\{x1+x2+x3\})

    or in ocaml-ish representation :

    - <code>S.Cons(var, S.Shift(S.Identity, offset))::...::Identity -> S.Cons(var, S.Cons(...S.Shift(S.Identity, x1+x2+x3...)))</code>
*)
let flattenIr (s: inter_subst): lexp S.subst option =
  let rec flattenCons s offset =
    match s with
    | Susp (_, S.Shift (S.Identity, o))::[] -> Some (S.Shift(S.Identity, o + offset))
    | Susp (_, S.Identity)::[] -> Some (mkFinalShift offset)
    | susp::tail -> (match flattenCons tail offset with
        | Some (s1) -> Some (S.Cons (unsusp_all susp, s1))
        | None -> None)
    | _ -> None
  in flattenCons s 0

(** Flatten a "tree"-like substitution:

    - a1.↑^\{x1\}(a2.↑^\{x2\}(a3.↑^\{x3\}id)) -> a1.(↑^\{x1\}a2).(↑^\{x2\}a3).↑^\{x3\}id -> a1.a2.a3 ↑^\{x1+x2+x3\}

    or in ocaml-ish representation :

    - <code>S.Cons(var, S.Shift(S.Identity, offset))::...::Identity -> S.Cons(var, S.Cons(...S.Shift(S.Identity, x1+x2+x3...)))</code>
*)
let flatten (s: lexp S.subst): lexp S.subst option =
  let rec check (sf: lexp S.subst): int option =
    match sf with
    | S.Identity -> Some 0
    | S.Shift(sf, o) -> (match check sf with
        | None -> None
        | Some o2 -> Some (o + o2))
    | S.Cons (Var(_, idx), sf) -> (match check sf with
      | None -> None
      | Some o -> if idx >= o then None else Some o)
    | _ -> assert false
  in
  match flattenIr (toIr s) with
  | None -> None
  | Some (sf2) as sf -> match check sf2 with
    | Some _ -> sf
    | None ->  None


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

(* With the exemple of the article :
   should return <code>(1,1)::(2, X)::(3,2)::(4,3)::(5, Z)::[]</code>
*)
let fill (l: (int * int) list) (size: int) (acc: (int * int) list): (int * int) list =
  let genDummyVar beg_ end_ = genDummyVar beg_ end_ (size + 1)
  in
  let rec fill_before (l: (int * int) list): (int * int) list =
    match l with
    | [] -> []
    | (idx, val_)::tail -> (if idx > 0 then (genDummyVar 0 idx)@l
                            else l)
  and fill_after (l: (int * int) list) (size: int) (acc: (int * int) list): (int * int) list =
    match l with
    | (idx1, val1)::(idx2, val2)::tail ->
      let tail = (idx2, val2)::tail in
      let accu = if (idx2 - idx1) > 1
        then (acc@[(idx1, val1)]@(genDummyVar (idx1 + 1) idx2))
        else (acc@(idx1, val1)::[])
      in fill_after tail size accu
    | (idx1, val1)::[] -> if (idx1 + 1) < size
      then acc@((idx1, val1)::(genDummyVar (idx1 + 1) size))
      else acc@[(idx1, val1)]
    | [] -> acc
  in fill_after (fill_before l) size acc

let to_list (s: lexp S.subst) : (((int * int) list) * int) =
  let rec as_list (s: lexp S.subst) (i: int) : (((int * int) list) * int) =
    match s with
    | S.Cons (Var(v), s1) -> let tail, o = as_list s1 (i + 1) in ((((idxOf v), i)::tail ), o)
    | S.Shift (S.Identity, shift) -> ([], shift)
    | S.Identity -> ([], 0)
    | _ -> assert false;
  in as_list s 0

let rec to_cons (lst: (int * int) list) (shift: int) : lexp S.subst option =
  match lst with
  | (_, i)::tail -> (match (to_cons tail shift) with
      | Some s -> Some (S.Cons (mkVar i, s))
      | None -> None)
  | []           -> Some (mkFinalShift shift)

(** <code>s:S.subst -> l:lexp -> s':S.subst</code> where <code>l[s][s'] = l</code>
    Return undefined result for bad input
*)
let rec inverse (subst: lexp S.subst ) : lexp S.subst option =
  let sort = List.sort (fun (ei1, _) (ei2, _) -> compare ei1 ei2)
  in
  match flatten subst with
  | None -> None
  | Some (s) ->
    let cons_lst, shift_val = to_list s
    in let size = sizeOf cons_lst
    in let cons_lst = fill (sort cons_lst) shift_val []
    in to_cons cons_lst size

