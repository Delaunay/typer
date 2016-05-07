(* util.ml --- Misc definitions for Typer.

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

(*  File is not printed because currently we parse only one file... *)
(*  Section is the name of the compilation step [for debugging]     *)
(*  'prerr' output is ugly                                          *)
let msg_message lvl kind section (loc: location) msg =
  if lvl <= !_typer_verbose then(
    print_string ("    " ^ kind);
    print_string " ["; print_loc loc; print_string "] ";
    print_string (section ^ "    ");
    print_string msg;
    print_newline ()) else ()

let msg_error   = msg_message 1 "[!] Error    "
let msg_info    = msg_message 3 "[?] Info     "
let msg_warning = msg_message 2 "/!\\ Warning  "
let msg_fatal s l m  =
    msg_message 0 "[X] Fatal    " s l m;
    internal_error m

let not_implemented_error () = internal_error "not implemented"

let string_implode chars = String.concat "" (List.map (String.make 1) chars)

let print_trace name max elem_to_string print_elem trace =
    print_string (Fmt.make_title name);

    let n = List.length trace in
    print_string "        size = "; print_int n;
    print_string (" max_printed = " ^ (string_of_int max) ^ "\n");
    print_string (Fmt.make_sep '-');

    let racc = List.rev trace in
        Fmt.print_first max racc (fun j (i, l, g) ->
            print_string "    ["; print_loc l; print_string "] ";
            Fmt._print_ct_tree i; print_string "+- ";
            print_string (elem_to_string g); print_string ": ";
            print_elem g; print_string "\n");

    print_string (Fmt.make_sep '=');


