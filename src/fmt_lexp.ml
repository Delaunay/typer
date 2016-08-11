
open Sexp
open Pexp
open Lexp
open Fmt

let _color          = true

let str_red str     = if _color then red     ^ str ^ reset else str
let str_green str   = if _color then green   ^ str ^ reset else str
let str_magenta str = if _color then magenta ^ str ^ reset else str
let str_yellow str  = if _color then yellow  ^ str ^ reset else str
let str_cyan str    = if _color then cyan    ^ str ^ reset else str

let rec string_of_subst s =
  match s with
  | S.Cons (Var(_, idx), s2) -> (* "a" ^ *) string_of_int idx ^ " · " ^ string_of_subst s2
  | S.Cons (l, s2)           -> string_of_lxp l ^ " · " ^ string_of_subst s2
  | S.Shift (s2, shift)      -> "(" ^ string_of_subst s2 ^ ") ↑^" ^ string_of_int shift
  | S.Identity               -> "Id"

and ocaml_string_of_subst s =
  match s with
  | S.Cons (l, s2) -> "Cons(" ^ string_of_lxp l ^ ", "  ^ ocaml_string_of_subst s2 ^ ")"
  | S.Shift (s2, shift)      -> "Shift(" ^ ocaml_string_of_subst s2 ^ ", " ^ string_of_int shift ^ ")"
  | S.Identity               -> "Identity"

and pp_ocaml_string_of_subst s =
  let rec pp_ocaml_string_of_subst s i =
    match s with
    | S.Cons (l, s2) -> "Cons("  ^ string_of_lxp l ^ ",\n"
                        ^ (String.make (4 * i) ' ') ^ pp_ocaml_string_of_subst s2 (i + 1) ^ ")"
    | S.Shift (s2, shift)      -> "Shift(" ^ string_of_int shift ^ ",\n"
                                  ^ (String.make (4 * i) ' ') ^ pp_ocaml_string_of_subst s2 (i + 1)^ ")"
    | S.Identity               -> "Identity"
  in pp_ocaml_string_of_subst s 1

and string_of_lxp lxp =
  match lxp with
  | Imm (Integer (_, value))        -> "Integer(" ^ (string_of_int value) ^ ")"
  | Imm (String (_, value))         -> "String(" ^ value ^ ")"
  | Imm (Float (_, value))          -> "Float(" ^ (string_of_float value) ^ ")"
  | Cons (((_,name),_),_)           -> "Cons(" ^  name ^ ")"
  | Builtin ((_, name), _)          -> "Builtin(" ^ name ^ ")"
  | Let (_)                         -> "Let(..)"
  | Var ((_, name), idx)            -> "Var(" ^ name ^ ", #" ^(string_of_int idx) ^ ")"
  | Arrow (_, _, a, _, b)           -> "Arrow(" ^ (string_of_lxp a) ^ " => " ^ (string_of_lxp b) ^ ")"
  | Lambda (_,(_, name), dcl, body) -> "Lambda(" ^ name ^ ": " ^ (string_of_lxp dcl) ^ " => (" ^ (string_of_lxp body) ^ "))"
  | Metavar (value, _, (_, name))      -> "Metavar(" ^ (string_of_int value) ^ ", " ^ name ^ ")"
  | Call (_)                        -> "Call(...)"
  | Inductive _                     -> ("Inductive") ^ "(...)"
  | Sort (_, s)                     -> ("Sort") ^ "(" ^ string_of_sort s ^ ")"
  | SortLevel l                     -> ("SortLevel") ^ "(" ^ string_of_sort_level l ^ ")"
  | Case _                          -> ("Case") ^ "(...)"
  | Susp (v, s)                     -> "Susp(" ^ (string_of_lxp v) ^ ", " ^ (string_of_subst s) ^ ")"
  | _                               -> "Unidentified Lexp"

and string_of_sort_level lvl =
  match lvl with
  | SLn i    -> "SLn(" ^ string_of_int i ^ ")"
  | SLsucc l -> "SLsucc(" ^ string_of_lxp l^ ")"

and string_of_sort sort =
  match sort with
  | Stype lxp -> "Stype(" ^ string_of_lxp lxp ^ ")"
  | StypeOmega -> "StypeOmega"
  | StypeLevel -> "StypeLevel"

let rec colored_string_of_lxp lxp lcol vcol =
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
                                       ^ " => (" ^ (vcol (string_of_lxp body)) ^ "))"
  | Metavar (value, _, (_, name))      -> (lcol "Metavar" ) ^ "(" ^ (vcol (string_of_int value)) ^ ", " ^ (vcol name) ^ ")"
  | Call (_)                        -> (lcol "Call(...)" )
  | Case _                          -> (lcol "Case") ^ "(...)"
  | Inductive _                     -> (lcol "Inductive") ^ "(...)"
  | Sort (_, s)                     -> (lcol "Sort") ^ "(" ^ vcol (string_of_sort s)^ ")"
  | SortLevel l                     -> (lcol "SortLevel") ^ "(" ^ vcol (string_of_sort_level l)  ^ ")"
  | Susp (v, s)                     -> (lcol "Susp") ^ "(" ^ colored_string_of_lxp v lcol vcol ^ ", " ^ vcol (string_of_subst s)  ^")"
  | _                               -> (lcol "Unidentified Lexp")

let padding_right (str: string ) (dim: int ) (char_: char) : string =
  let diff = (dim - String.length str)
  in let rpad = max diff 0
  in str ^ (String.make rpad char_)

let padding_left (str: string ) (dim: int ) (char_: char) : string =
  let diff = (dim - String.length str)
  in let lpad = max diff 0
  in (String.make lpad char_) ^ str

let center (str: string ) (dim: int ) (char_: char) : string =
  let diff = max (dim - String.length str) 0
  in let lpad, rpad = ((diff / 2 ), ((diff / 2) + (diff mod 2)))
  in (String.make lpad char_) ^ str ^ (String.make lpad char_)


let rec string_of_pexp pxp =
  match pxp with
  (* | Psort of location * sort *)
  | Pimm (Integer (_, i))     -> "Pimm( Integer (" ^ string_of_int i ^ "))"
  | Pimm (Float (_, f))       -> "Pimm( Float (" ^ string_of_float f ^ "))"
  | Pimm (String (_, s))      -> "Pimm (String (" ^ s ^ "))"
  | Pvar (_, s)               -> "Pvar (" ^ s ^ ")"
  | Phastype (_, p1, p2)      -> "Phastype (" ^ string_of_pexp p1 ^ ", " ^ string_of_pexp p2 ^ ")"
  | Pmetavar (_, s)           -> "Pmetavar (" ^ s ^ ")"
  | Plet (_, _, p)            -> "Plet (_, " ^ string_of_pexp p ^ ")"
  | Parrow (_, _, _, _, _)    -> "Parrow (...)"
  | Plambda _                 -> "Plambda (...)"
  | Pcall _                   -> "Pcall (...)"
  | Pinductive _              -> "Pinductive (...)"
  | Pcons ( (_, s), (_, s2) ) -> "Pcons (" ^ s ^ ", " ^ s2 ^ ")"
  | Pcase _                   -> "Pcase (...)"
  | _                         -> "Pexp not handled"
