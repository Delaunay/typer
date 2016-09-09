
module L = Lexp
module S = Subst

let _color          = true

let str_red str     = if _color then Fmt.red     ^ str ^ Fmt.reset else str
let str_green str   = if _color then Fmt.green   ^ str ^ Fmt.reset else str
let str_magenta str = if _color then Fmt.magenta ^ str ^ Fmt.reset else str
let str_yellow str  = if _color then Fmt.yellow  ^ str ^ Fmt.reset else str
let str_cyan str    = if _color then Fmt.cyan    ^ str ^ Fmt.reset else str

let rec string_of_subst s =
  match s with
  | S.Cons (L.Var(_, idx), s2) -> (* "a" ^ *) string_of_int idx ^ " · " ^ string_of_subst s2
  | S.Cons (l, s2)             -> string_of_lxp l ^ " · " ^ string_of_subst s2
  | S.Shift (s2, shift)        -> "(" ^ string_of_subst s2 ^ ") ↑^" ^ string_of_int shift
  | S.Identity                 -> "Id"

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
  | L.Imm (Sexp.Integer (_, value))        -> "Integer(" ^ (string_of_int value) ^ ")"
  | L.Imm (Sexp.String (_, value))         -> "String(" ^ value ^ ")"
  | L.Imm (Sexp.Float (_, value))          -> "Float(" ^ (string_of_float value) ^ ")"
  | L.Cons (((_,tname),_),(_, cname))      -> "Cons(" ^  tname ^ ", " ^ cname ^")"
  | L.Builtin ((_, name), _)               -> "Builtin(" ^ name ^ ")"
  | L.Let (_)                              -> "Let(..)"
  | L.Var ((_, name), idx)                 -> "Var(" ^ name ^ ", #" ^(string_of_int idx) ^ ")"
  | L.Arrow (kind, Some(_, name), a, _, b) -> name ^ ":Arrow(" ^ (string_of_lxp a) ^ ":"  ^ string_of_kind kind ^ " => " ^ (string_of_lxp b) ^ ")"
  | L.Arrow (kind, _, a, _, b)             -> "Arrow(" ^ (string_of_lxp a) ^ ":"  ^ string_of_kind kind ^ " => " ^ (string_of_lxp b) ^ ")"
  | L.Lambda (_,(_, name), dcl, body)      -> "Lambda(" ^ name ^ ": " ^ (string_of_lxp dcl) ^ " => (" ^ (string_of_lxp body) ^ "))"
  | L.Metavar (value, _, (_, name))        -> "Metavar(" ^ (string_of_int value) ^ ", " ^ name ^ ")"
  | L.Call (_)                             -> "Call(...)"
  | L.Inductive _                          -> ("Inductive") ^ "(...)"
  | L.Sort (_, s)                          -> ("Sort") ^ "(" ^ string_of_sort s ^ ")"
  | L.SortLevel l                          -> ("SortLevel") ^ "(" ^ string_of_sort_level l ^ ")"
  | L.Case _                               -> ("Case") ^ "(...)"
  | L.Susp (v, s)                          -> "Susp(" ^ (string_of_lxp v) ^ ", " ^ (string_of_subst s) ^ ")"
  | _                                      -> "Unidentified Lexp"

and string_of_kind = function
 | Pexp.Aexplicit -> "Aexplicit"
 | Pexp.Aimplicit -> "Aimplicit"
 | Pexp.Aerasable -> "Aerasable"

and string_of_sort_level lvl =
  match lvl with
  | L.SLn i    -> "SLn(" ^ string_of_int i ^ ")"
  | L.SLsucc l -> "SLsucc(" ^ string_of_lxp l^ ")"

and string_of_sort sort =
  match sort with
  | L.Stype lxp  -> "Stype(" ^ string_of_lxp lxp ^ ")"
  | L.StypeOmega -> "StypeOmega"
  | L.StypeLevel -> "StypeLevel"

let rec colored_string_of_lxp lxp lcol vcol =
  match lxp with
  | L.Imm (Sexp.Integer (_, value))   -> (lcol "Integer") ^ "("  ^ (vcol (string_of_int value)) ^ ")"
  | L.Imm (Sexp.String (_, value))    -> (lcol "String") ^ "(" ^  (vcol value ) ^ ")"
  | L.Imm (Sexp.Float (_, value))     -> (lcol "Float" ) ^ "(" ^ (vcol (string_of_float value)) ^ ")"
  | L.Cons (((_,name),_),_)           -> (lcol "Cons" ) ^ "(" ^ (vcol name) ^ ")"
  | L.Builtin ((_, name), _)          -> (lcol "Builtin") ^ "(" ^ (vcol name) ^ ")"
  | L.Let (_)                         -> (lcol "Let(..)")
  | L.Var ((_, name), idx)            -> (lcol "Var" ) ^ "(" ^ (vcol name ) ^ ", " ^ (vcol ("#" ^ (string_of_int idx))) ^ ")"
  | L.Arrow (_, _, a, _, b)           -> (lcol "Arrow(") ^ (vcol (string_of_lxp a)) ^ " => " ^ (vcol (string_of_lxp b)) ^ ")"
  | L.Lambda (_,(_, name), dcl, body) -> (lcol "Lambda") ^ "(" ^ (vcol name) ^ " : " ^ (vcol (string_of_lxp dcl))
  | L.Metavar (value, _, (_, name))   -> (lcol "Metavar" ) ^ "(" ^ (vcol (string_of_int value)) ^ ", " ^ (vcol name) ^ ")"
  | L.Call (_)                        -> (lcol "Call(...)" )
  | L.Case _                          -> (lcol "Case") ^ "(...)"
  | L.Inductive _                     -> (lcol "Inductive") ^ "(...)"
  | L.Sort (_, s)                     -> (lcol "Sort") ^ "(" ^ vcol (string_of_sort s)^ ")"
  | L.SortLevel l                     -> (lcol "SortLevel") ^ "(" ^ vcol (string_of_sort_level l)  ^ ")"
  | L.Susp (v, s)                     -> (lcol "Susp") ^ "(" ^ colored_string_of_lxp v lcol vcol ^ ", " ^ vcol (string_of_subst s)  ^")"
  | _                                 -> (lcol "Unidentified Lexp")

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
  in let lpad, rpad = ((diff / 2), ((diff / 2) + (diff mod 2)))
  in (String.make lpad char_) ^ str ^ (String.make rpad char_)


let rec string_of_pexp pxp =
  match pxp with
  | Pexp.Pimm (Sexp.Integer (_, i)) -> "Pimm( Integer (" ^ string_of_int i ^ "))"
  | Pexp.Pimm (Sexp.Float (_, f))   -> "Pimm( Float (" ^ string_of_float f ^ "))"
  | Pexp.Pimm (Sexp.String (_, s))  -> "Pimm (String (" ^ s ^ "))"
  | Pexp.Pvar (_, s)                -> "Pvar (" ^ s ^ ")"
  | Pexp.Phastype (_, p1, p2)       -> "Phastype (" ^ string_of_pexp p1 ^ ", " ^ string_of_pexp p2 ^ ")"
  | Pexp.Pmetavar (_, s)            -> "Pmetavar (" ^ s ^ ")"
  | Pexp.Plet (_, _, p)             -> "Plet (_, " ^ string_of_pexp p ^ ")"
  | Pexp.Parrow (_, _, _, _, _)     -> "Parrow (...)"
  | Pexp.Plambda _                  -> "Plambda (...)"
  | Pexp.Pcall _                    -> "Pcall (...)"
  | Pexp.Pinductive _               -> "Pinductive (...)"
  | Pexp.Pcons ( (_, s), (_, s2) )  -> "Pcons (" ^ s ^ ", " ^ s2 ^ ")"
  | Pexp.Pcase _                    -> "Pcase (...)"
  | _                               -> "Pexp not handled"

let print_meta_ctx ((subst: L.substitution), (const: L.constraints)) =
  let print_const c =
    let strs = List.map (fun (c1, c2) -> (string_of_lxp c1, string_of_lxp c2)) c
    in let strs = ("left lexp", "right lexp")::strs
    in let (max_size_left, max_size_right) = List.fold_right
           (fun (s1, s2) (l1, l2) ->  (
                (max (String.length s1) l1),
                (max (String.length s2) l2)
            )) strs (0, 0)
    in let head, tail = (List.hd strs), (List.tl strs)
    in let strs = head::(String.make (max_size_left) '=', String.make (max_size_right) '=')::tail
    in print_endline (center " Constraints " (max_size_left + max_size_right + 7) '=');
    List.iter
      (fun (s1, s2) ->
         print_endline ( "| "
         ^ padding_right s1 (max_size_left) ' '
         ^ " | "
         ^ padding_right s2 (max_size_right) ' '
         ^ " |")
      ) strs;
    print_endline (center "=" (max_size_left + max_size_right + 7) '=');
  and print_meta m =
    let strs = List.map (fun (k, v) -> (string_of_int k, string_of_lxp v)) (L.VMap.bindings m)
    in let strs = ("Metavar index", "Lexp")::strs
    in let (max_size_left, max_size_right) = List.fold_right
           (fun (s1, s2) (l1, l2) ->  (
                (max (String.length s1) l1),
                (max (String.length s2) l2)
            )) strs (0, 0)
    in let head, tail = (List.hd strs), (List.tl strs)
    in let strs = head::(String.make (max_size_left) '=', String.make (max_size_right) '=')::tail
    in print_endline (center " Metavar Context " (max_size_left + max_size_right + 7) '=');
    List.iter
      (fun (s1, s2) ->
         print_endline ( "| "
         ^ padding_right s1 (max_size_left) ' '
         ^ " | "
         ^ padding_right s2 (max_size_right) ' '
         ^ " |")
      ) strs;
    print_endline (center "=" (max_size_left + max_size_right + 7) '=');
  in print_meta subst;
  print_const const

