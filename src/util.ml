(* util.ml --- Misc definitions for Typer.  -*- coding: utf-8 -*-

Copyright (C) 2011-2013, 2016  Free Software Foundation, Inc.

Author: Stefan Monnier <monnier@iro.umontreal.ca>
Keywords: languages, lisp, dependent types.

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

module SMap
  = Map.Make (struct type t = string let compare = String.compare end)
module IntMap
  = Map.Make (struct type t = int let compare = compare end)

type charpos = int
type bytepos = int
type location = { file : string; line : int; column : charpos }
let dummy_location = {file=""; line=0; column=0}

(*************** DeBruijn indices for variables *********************)

(* Occurrence of a variable's symbol: we use DeBruijn index, and for
 * debugging purposes, we remember the name that was used in the source
 * code.  *)
type vdef = location * string
type db_index = int             (* DeBruijn index.  *)
type db_offset = int            (* DeBruijn index offset.  *)
type db_revindex = int          (* DeBruijn index counting from the root.  *)
type vref = vdef * db_index

type bottom = | B_o_t_t_o_m_ of bottom

(* print debug info *)
let loc_string loc =
  "Ln " ^ (Fmt.ralign_int loc.line 3) ^ ", cl " ^ (Fmt.ralign_int loc.column 3)

let loc_print loc = print_string (loc_string loc)

(*
 *  -1 - Nothing    (* During testing we may want to produce errors *)
 *   0 - Fatal
 *   1 - Error
 *   2 - Warning
 *   3 - Info
 *)

let _typer_verbose = ref 20

exception Internal_error of string
let internal_error s = raise (Internal_error s)

exception Unreachable_error of string
let typer_unreachable s = raise (Unreachable_error s)

(*  Section is the name of the compilation step [for debugging]     *)
(*  'prerr' output is ugly                                          *)
let msg_message lvl kind section (loc: location) msg =
  if lvl <= !_typer_verbose then(
    let info =
      " [" ^ loc_string loc ^ "] " ^  loc.file ^ "\n" ^
      "   " ^ kind ^ " " ^ (Fmt.lalign_string section 8) ^ " " ^ msg ^ "\n" in
        print_string info) else ()

(* let info = "    " ^ kind ^ " [" ^ loc_string loc ^ "] " ^ (Fmt.lalign_string section 8) in
      print_string (info ^ " " ^ msg ^ "\n")) else () *)

let msg_fatal s l m  =
    msg_message 0 "[X] Fatal    " s l m;
    flush stdout;
    internal_error "Compiler Fatal Error"

let msg_error   = msg_message 1 "[!] Error    "
let msg_warning = msg_message 2 "/!\\ Warning  "
let msg_info    = msg_message 3 "[?] Info     "

(* Compiler Internal Debug print *)
let debug_msg expr =
    if 4 <= !_typer_verbose then expr else ()

let not_implemented_error () = internal_error "not implemented"

let string_implode chars = String.concat "" (List.map (String.make 1) chars)

let opt_map f x = match x with None -> None | Some x -> Some (f x)

let str_split str sep =
    let str = String.trim str in
    let n = String.length str in

    if n = 0 then []
    else (

        let ret = ref [] in
        let buffer = Buffer.create 10 in
            Buffer.add_char buffer (str.[0]);

        for i = 1 to n - 1 do
            if str.[i] = sep then (
                ret := (Buffer.contents buffer)::(!ret);
                Buffer.reset buffer)
            else
                Buffer.add_char buffer (str.[i]);
        done;
        (if (Buffer.length buffer) > 0 then
            ret := (Buffer.contents buffer)::(!ret));

        List.rev (!ret))

let utf8_head_p (c : char) : bool
  = Char.code c < 128 || Char.code c >= 192

(* Display size of `str`, assuming the byte-sequence is UTF-8.
 * Very naive: doesn't pay attention to LF, TABs, double-width chars, ...  *)
let string_width (s : string) : int =
  let rec width i w =
    if i < 0 then w
    else width (i - 1)
               (if utf8_head_p (String.get s i)
                then w + 1
                else w) in
  width (String.length s - 1) 0

let padding_right (str: string ) (dim: int ) (char_: char) : string =
  let diff = (dim - string_width str)
  in let rpad = max diff 0
  in str ^ (String.make rpad char_)

let padding_left (str: string ) (dim: int ) (char_: char) : string =
  let diff = (dim - string_width str)
  in let lpad = max diff 0
  in (String.make lpad char_) ^ str
