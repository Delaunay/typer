(*
 *      Typer Compiler
 *
 * ---------------------------------------------------------------------------
 *
 *      Copyright (C) 2011-2016  Free Software Foundation, Inc.
 *
 *   Author: Pierre Delaunay <pierre.delaunay@hec.ca>
 *   Keywords: languages, lisp, dependent types.
 *
 *   This file is part of Typer.
 *
 *   Typer is free software; you can redistribute it and/or modify it under the
 *   terms of the GNU General Public License as published by the Free Software
 *   Foundation, either version 3 of the License, or (at your option) any
 *   later version.
 *
 *   Typer is distributed in the hope that it will be useful, but WITHOUT ANY
 *   WARRANTY; without even the implied warranty of MERCHANTABILITY or FITNESS
 *   FOR A PARTICULAR PURPOSE.  See the GNU General Public License for
 *   more details.
 *
 *   You should have received a copy of the GNU General Public License along 
 *   with this program.  If not, see <http://www.gnu.org/licenses/>. 
 *
 * ---------------------------------------------------------------------------
 *  
 *      Description:
 *          print out read pretoken
 *
 * --------------------------------------------------------------------------- *)

open Util
open Prelexer
open Debug

(* TODO: add a Prestring and a Preblock example into the test.typer file *)
let rec debug_pretokens_print pretokens =
  List.iter (fun pt ->
             print_string " ";
             match pt with
               | Preblock(loc, pts,_)
                 -> print_string "Preblock:\t"; 
                    print_string "["; print_loc loc; print_string "]\t";
                    print_string "{"; 
                        pretokens_print pts; 
                    print_string " }"
                    
               | Pretoken(loc, str) 
                 -> print_string "Pretoken:\t"; 
                    print_string "["; print_loc loc; print_string "]\t"; 
                        print_string str; 
                    print_string "\n"
                    
               | Prestring(loc, str)
                 -> print_string "Prestring:\t"; 
                    print_string "["; print_loc loc; print_string "]\t";
                    print_string "\""; 
                        print_string str; 
                    print_string "\"\n";
            )
            pretokens

let main () = 
    
    let arr = prelex_file "./samples/pretoken_test.typer" in
    debug_pretokens_print arr
;;

main ();
