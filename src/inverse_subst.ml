
open Lexp
open Util
module S = Subst

(** Provide inverse function for computing the inverse of a substitution
*)

(* Transformation *)

(** a_0 . ↑^x1 (a_2 . ↑x2 ... ) . ↑^xn . id*)
(* type inter_subst = lexp S.subst list (* Intermediate between "tree"-like substitution and fully flattened subsitution *) *)
type inter_subst = lexp list (* Intermediate between "tree"-like substitution and fully flattened subsitution *)

(** Helper function that create a Cons(_, Shift(_)) *)
(* let mkSubstNode var offset = S.Cons (var, S.Shift(S.Identity, offset)) *)

let dummy_var = Var((dummy_location, "DummyVar"), -1)

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
    (* Assuming that a Shift always follow Cons, the case Shift should never arise *)
  in let res = toIr s 0
  in Debug_fun.do_debug ( fun () ->
      List.iter (fun i ->
          print_string (Fmt_lexp.string_of_lxp i); print_string "::";
          match i with
          | Susp _ -> assert true
          | _ -> assert false) res;
      print_newline(); print_newline(); ); res

(** Transform an 'intermediate representation' into a sequence of cons followed by a shift

    - a1.(↑^\{x1\}a2).(↑^\{x2\}a3).↑^\{x3\}id -> a1.a2.a3 ↑^\{x1+x2+x3\}

    or in ocaml-ish representation :

    - <code>S.Cons(var, S.Shift(S.Identity, offset))::...::Identity -> S.Shift(S.Cons(var, S.Cons(...)), x1+x2+x3...)</code>
*)
let flattenIr (s: inter_subst): lexp S.subst option =
  let rec flattenCons s =
    match s with
    | Susp (_, S.Shift (S.Identity, o))::[] -> Some (o, S.Identity)
    | Susp (_, S.Identity)::[] -> Some (0, S.Identity)
    | susp::tail -> (match flattenCons tail with
        | Some (o, s1) -> Some (o, (S.Cons (unsusp_all susp, s1)))
        | None -> None)
    | _ -> None
  in Debug_fun.do_debug ( fun () ->
      List.iter (fun i ->
          match i with
          | Susp _ -> assert true
          | _ -> assert false) s);
  match flattenCons s with
  | Some(offset, cons) -> Some(S.Shift(cons, offset))
  | None               -> None

(** Flatten a "tree"-like substitution:

    - a1.↑^\{x1\}(a2.↑^\{x2\}(a3.↑^\{x3\}id)) -> a1.(↑^\{x1\}a2).(↑^\{x2\}a3).↑^\{x3\}id -> a1.a2.a3 ↑^\{x1+x2+x3\}

    or in ocaml-ish representation :

    - <code>S.Cons(var, S.Shift(..., offset)) -> S.Shift(S.Cons(var, S.Cons(...)), x1+x2+x3...)</code>
*)
let flatten (s: lexp S.subst) = flattenIr (toIr s)


(* Inverse *)

(** Returns the value of the shift of a S.Shift
*)
let shiftOf s =
  match s with
  | S.Shift (_, o) -> o
  | _              -> 0

(** Returns the number of element in a sequence of S.Cons
*)
let rec sizeOf s =
  match s with
  | S.Cons(_, s1)  -> 1 + sizeOf s1
  | S.Shift(s1, _) -> sizeOf s1
  | S.Identity     -> 0

(** Returns the nth of a susbstitution,
    returns S.Identity if i > number_of_element(s)
*)
let rec nthOf s i =
  match s, i with
  | S.Cons _, 0       -> s
  | S.Shift _, 0      -> s
  | S.Identity, _     -> s
  | S.Cons(_, s1), _  -> nthOf s1 (i - 1)
  | S.Shift(s1, _), _ -> nthOf s1 (i - 1)

(** Returns the db_index of the "inside" of a Var
*)
let idxOf (_, idx) = idx

(** Returns a list of couple (X, idx) where X go from beg_ to end_*)
let rec genDummyVar beg_ end_ idx =
  if beg_ < end_
  then (beg_, idx)::(genDummyVar (beg_ + 1) end_ idx)
  else []

(** Returns a dummy variable with the db_index idx
*)
let mkVar idx = Var((U.dummy_location, ""), idx) (* not sure how to fill vdef *)

(** Map a list of tuple to a sequence of S.Cons
*)
let rec generate_s l =
  match l with
  | (_, i)::tail -> S.Cons(mkVar i, (generate_s tail))
  | []           -> S.Identity

(* With the exemple of the article :
   should return <code>(1,1)::(3,2)::(4,3)::[]</code>
*)
let rec genCons s i =
  match s with
  | S.Cons(Var(v), s1) -> ((idxOf v), i)::(genCons s1 (i + 1)) (* e_{idx_of v} = i *)
  | S.Identity -> []
  | _ -> assert false

(* With the exemple of the article :
   should return <code>(1,1)::(2, X)::(3,2)::(4,3)::(5, Z)::[]</code>
*)
let fill l size acc =
  let genDummyVar beg_ end_ = genDummyVar beg_ end_ (size + 1)
  in
  let rec fill_before l =
    match l with
    | [] -> []
    | (idx, val_)::tail -> (if idx > 0 then (genDummyVar 0 idx)@l
                            else l)
  and fill_after l size acc =
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

(** Take a "flattened" substitution and returns the inverse of the Cons
*)
let generateCons s _size shift = generate_s (fill (genCons s 0) shift [])

(** <code>s:S.subst -> l:lexp -> s':S.subst</code> where <code>l[s][s'] = l</code>
    Return undefined result for bad input
*)
let rec inverse (subst: lexp S.subst ) : lexp S.subst option =
  match flatten subst with
  | Some(S.Shift(flattened, shift)) ->
    let size = sizeOf flattened
    in Some(S.Shift((generateCons flattened size shift), size))
  | None            -> None

