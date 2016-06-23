
open Sexp
open Lexp
open Unification

open Lparse     (* add_def       *)

open Utest_lib

open Fmt

open Builtin
open Env

open Str

open Debug

type result =
  | Constraint
  | Unification
  | Equivalent
  | Nothing

type unif_res = (result * (substitution * constraints) option * lexp * lexp)

type triplet = string * string * string

let _debug = false

let do_debug func =
  if _debug then (func ()) else ()

(* String & lexp formatting *)
let rec string_of_lxp lxp =
  match lxp with
  | Imm (Integer (_, value))        -> "Integer(" ^ (string_of_int value) ^ ")"
  | Imm (String (_, value))         -> "String(" ^ value ^ ")"
  | Imm (Float (_, value))          -> "Float(" ^ (string_of_float value) ^ ")"
  | Cons (((_,name),_),_)           -> "Cons(" ^  name ^ ")"
  | Builtin ((_, name), _)          -> "Builtin(" ^ name ^ ")"
  | Let (_)                         -> "Let(..)"
  | Var ((_, name), idx)            -> "Var(" ^ name ^ ", #" ^(string_of_int idx) ^ ")"
  | Arrow (_, _, a, _, b)           -> "Arrow(" ^ (string_of_lxp a) ^ " => " ^ (string_of_lxp b) ^ ")"
  | Lambda (_,(_, name), dcl, body) -> "Lambda(" ^ name ^ " : " ^ (string_of_lxp dcl) ^ " => (" ^ (string_of_lxp body) ^ ") )"
  | Metavar (value, (_, name))      -> "Metavar(" ^ (string_of_int value) ^ ", " ^ name ^ ")"
  | Call (_)                        -> "Call(...)"
  | _                               -> "???"

let _color = false
let str_red str     = if _color then red     ^ str ^ reset else str
let str_green str   = if _color then green   ^ str ^ reset else str
let str_magenta str = if _color then magenta ^ str ^ reset else str
let str_yellow str  = if _color then yellow  ^ str ^ reset else str
let str_cyan str    = if _color then cyan    ^ str ^ reset else str

let colored_string_of_lxp lxp lcol vcol =
  match lxp with
  | Imm (Integer (_, value))        -> (lcol "Integer") ^ "("  ^ (vcol (string_of_int value)) ^ ")"
  | Imm (String (_, value))         -> (lcol "String") ^ "(" ^  (vcol value ) ^ ")"
  | Imm (Float (_, value))          -> (lcol "Float" ) ^ "(" ^ (vcol (string_of_float value)) ^ ")"
  | Cons (((_,name),_),_)           -> (lcol "Cons" ) ^ "(" ^ (vcol name) ^ ")"
  | Builtin ((_, name), _)          -> (lcol "Builtin") ^ "(" ^ (vcol name) ^ ")"
  | Let (_)                         -> (lcol "Let(..)")
  | Var ((_, name), idx)            -> (lcol "Var" ) ^ "(" ^ (vcol name ) ^ ", " ^ (vcol ("#" ^ (string_of_int idx))) ^ ")"
  | Arrow (_, _, a, _, b)           -> (lcol "Arrow(") ^ (vcol (string_of_lxp a)) ^ " => " ^ (vcol (string_of_lxp b)) ^ ")"
  | Lambda (_,(_, name), dcl, body) -> (lcol "Lambda") ^ "(" ^ (vcol name) ^ " : " ^ (vcol (string_of_lxp dcl))
                                       ^ " => (" ^ (vcol (string_of_lxp body)) ^ ") )"
  | Metavar (value, (_, name))      -> (lcol "Metavar" ) ^ "(" ^ (vcol (string_of_int value)) ^ ", " ^ (vcol name) ^ ")"
  | Call (_)                        -> (lcol "Call(...)" )
  | _                               -> "???"

let padding_right (str: string ) (dim: int ) (char_: char) : string =
  let diff = (dim - String.length str) + 5
  in let rpad = diff
  in str ^ (String.make rpad char_)

let padding_left (str: string ) (dim: int ) (char_: char) : string =
  let diff = (dim - String.length str) + 5
  in let lpad = diff
  in (String.make lpad char_) ^ str

let center (str: string ) (dim: int ) (char_: char) : string =
  let diff = (dim - String.length str) + 5
  in let lpad, rpad = ((diff / 2 ), ((diff / 2) + (diff mod 2)))
  in (String.make lpad char_) ^ str ^ (String.make lpad char_)

let get_max_dim (str_list : triplet list ) : (int * int * int) =
  let max_ i s = max i (String.length s)
  in (List.fold_left
        (fun (al,ac,ar) (el, ec, er) -> ((max_ al el), (max_ ac ec), (max_ ar er)))
        (0, 0, 0) str_list)

let fmt_unification_result (l: unif_res): string =
  match l with
  | (Constraint, _, lxp1, lxp2) ->
    "{ \"result\" : " ^ (str_yellow "\"Constraint\"") ^ ", \"lexp_left\" : \"" ^ (str_yellow (string_of_lxp lxp1)) ^ "\", \"lexp_right\" : \"" ^ (str_yellow (string_of_lxp lxp2)) ^ "\"}"
  | (Unification, _, lxp1, lxp2) ->
    "{ \"result\" : " ^ (str_yellow "\"Unification\"") ^ ", \"lexp_left\" : \"" ^ (str_yellow (string_of_lxp lxp1)) ^ "\", \"lexp_right\" : \"" ^ (str_yellow (string_of_lxp lxp2)) ^ "\"}"
  | (Equivalent, _, lxp1, lxp2) ->
    "{ \"result\" : " ^ (str_yellow "\"Equivalent\"") ^ ", \"lexp_left\" : \"" ^ (str_yellow (string_of_lxp lxp1)) ^ "\", \"lexp_right\" : \"" ^ (str_yellow (string_of_lxp lxp2)) ^ "\"}"
  | (Nothing, _, lxp1, lxp2) ->
    "{ \"result\" : " ^ (str_yellow "\"Nothing\"") ^ ", \"lexp_left\" : \"" ^ (str_yellow (string_of_lxp lxp1)) ^ "\", \"lexp_right\" : \"" ^ (str_yellow (string_of_lxp lxp2)) ^ "\"}"

let fmt_all (r: unif_res list) =
  List.map fmt_unification_result r

let fmt_unification_of lxp1 lxp2 =
  "Unifying " ^ (colored_string_of_lxp lxp1 str_yellow str_cyan)
  ^ " -> "
  ^ (colored_string_of_lxp lxp2 str_yellow str_cyan)
  ^ "\n"

let string_of_result r =
  match r with
  | Constraint  -> "Constraint"
  | Unification -> "Unification"
  | Equivalent  -> "Equivalent"
  | Nothing     -> "Nothing"

let fmt_title l1 l2 r = string_of_lxp l1 ^ ", " ^ string_of_lxp l2 ^ " -> " ^ string_of_result r

(* Inputs for the test *)
let input_, _  = lexp_decl_str "
        mult = lambda (x : Int) -> lambda (y : Int) -> x * y;

        twice = (mult 2);

        let_fun = lambda (x : Int) ->
            let a = (twice x); b = (mult 2 x); in
                a + b;" default_lctx

let input = List.map (fun (_, l, _)-> l) (List.flatten input_)

let man_input =
  Imm (Integer (Util.dummy_location, 3))
  ::Imm (Integer (Util.dummy_location, 4))
  ::Builtin ((Util.dummy_location, "Int=3"), Imm (Integer (Util.dummy_location, 3)))
  ::Var ((Util.dummy_location, "x"), 3)
  ::Var ((Util.dummy_location, "y"), 4)
  ::Metavar (0, (Util.dummy_location, "M"))
  ::[]


(* Test sample generation *)
let rec range (begin_: int) (end_: int) : (int list) =
  if begin_ >= end_
  then []
  else begin_::(range (begin_+1) end_)

let generate_combination (r: int list) (input: lexp list) : ((lexp * lexp) list) =
  let begin_ = List.hd r
  in List.map (fun idx -> ((List.nth input begin_ ), (List.nth input idx)) ) r

let generate_couples (input: lexp list) : ((lexp * lexp) list) =
  let length = List.length input
  in List.fold_left (fun acc elt -> (generate_combination (range elt length) input)@acc) [] (range 0 length)

(* Testing the sample *)

let test_input (lxp1: lexp) (lxp2: lexp) (subst: substitution): unif_res =
  do_debug (fun () -> print_string (fmt_unification_of lxp1 lxp2));
  let res = unify lxp1 lxp2 subst in
  match res with
  | Some (s, []) when s = empty_subst -> (Equivalent, res, lxp1, lxp2)
  | Some (_, [])                      -> (Unification, res, lxp1, lxp2)
  | Some _                            -> (Constraint, res, lxp1, lxp2)
  | None                              -> (Nothing, res, lxp1, lxp2)

let test_samples (samples: (lexp * lexp) list) (subst: substitution): (unif_res list) =
  List.map (fun (l1, l2) -> test_input l1 l2 subst) samples

(* Testing the inputs *)

let tests (input: lexp list) sample_generator formatter : (string list) =
  let samples = sample_generator input
  in let res = test_samples samples empty_subst
  in formatter res

let generate_testable (_: lexp list) : ((lexp * lexp * result) list) =
  ( Imm (Integer (Util.dummy_location, 3)) , Imm (Integer (Util.dummy_location, 3)) , Equivalent)
  ::( Imm (Integer (Util.dummy_location, 4)) , Imm (Integer (Util.dummy_location, 3)) , Nothing )
  ::( Builtin ((Util.dummy_location, "Int=3"), Imm (Integer (Util.dummy_location, 3))), Imm (Integer (Util.dummy_location, 3)), Equivalent)
  ::( Var ((Util.dummy_location, "x"), 3), Var ((Util.dummy_location, "y"), 4), Nothing )
  ::( Var ((Util.dummy_location, "x"), 3), Metavar (0, (Util.dummy_location, "M")), Unification )
  ::[]

let check (lxp1: lexp ) (lxp2: lexp ) (res: result) (subst: substitution ): bool =
  let r, _, _, _ = test_input lxp1 lxp2 subst
  in if r = res then true else false

let test_if (input: lexp list) sample_generator checker : bool =
  let rec test_if_ samples checker =
    match samples with
    | (l1, l2, res)::t -> if checker l1 l2 res empty_subst then test_if_ t checker else false
    | [] -> true
  in test_if_ (sample_generator input) checker

let print_as_json (input: lexp list) =
  let str = tests input (generate_couples) (fmt_all)
  in let s = "[\n" ^ (List.fold_right (fun e a -> a ^ e ^ ",\n") str "") ^ "]\n"
  in print_string s

(*let () = print_as_json (input@man_input)*)

(*let () = (fun () ->  if test_if [] generate_testable check then () else ()) ()*)

let _ = List.map
    (fun (l1, l2, r) ->
       add_test "UNIFICATION"
         (fmt_title l1 l2 r)
         (fun () -> if test_if [] (fun _ -> [(l1, l2, r)]) check then success () else failure ()))
    (generate_testable [])

let _ = run_all ()
