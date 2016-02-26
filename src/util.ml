(* util.ml --- Misc definitions for Typer.

Copyright (C) 2011-2013  Free Software Foundation, Inc.

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

type charpos = int
type bytepos = int
type location = { file : string; line : int; column : charpos }
let dummy_location = {file=""; line=0; column=0}

type bottom = | B_o_t_t_o_m_ of bottom

(* print debug info *)
let print_loc (loc: location) = 
    (*print_string loc.file; *) (* Printing the file is too much*)
    print_string "ln "; 
    Fmt.ralign_print_int loc.line 3;
    print_string ", cl ";
    Fmt.ralign_print_int loc.column 3;
;;

(* print debug info *)
let prerr_loc (loc: location) = 
    (*print_string loc.file; *) (* Printing the file is too much*)
    prerr_string "ln "; 
    Fmt.ralign_prerr_int loc.line 3;
    prerr_string ", cl ";
    Fmt.ralign_prerr_int loc.column 3;
;;

(*  File is not printed because currently we parse only one file... *)
(*  Section is the name of the compilation step [for debugging]     *)
(*  'prerr' output is ugly                                          *)
let msg_message kind section (loc: location) msg =
  print_string ("   " ^ kind);
  print_string " ["; print_loc loc; print_string "]    ";
  print_string (section ^ "    ");
  print_string msg;
  print_newline ()
  
let msg_error = msg_message "[!] Error    "
let msg_info = msg_message "[?] Info     "
let msg_warning = msg_message "/!\\ Warning  "

let string_implode chars = String.concat "" (List.map (String.make 1) chars)

exception Internal_error of string
let internal_error s = raise (Internal_error s)


