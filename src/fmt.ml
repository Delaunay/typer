(*
 *      Kiwi Compiler
 * 
 *          Pierre Delaunay
 *
 *  ---------------------------------------------------------------------------
 *
 *
 *)

 
(******************************************************************************
 *  Print helper      
 *
 *      Declare new print function which align printed values.
 *
 *****************************************************************************)
 
(*  Compute the number of character needed to print an integer*)
let str_size_int value =
    (int_of_float (log10 (float value))) + 1
;;

(* print n char 'c' *)
let rec make_line c n = 
    print_string c;
    if n >= 1 then (make_line c (n - 1));
;;
     
(* print an integer right-aligned *)
let ralign_print_int value nb =
    make_line " " (nb - (str_size_int value));
    print_int value;
;;

let lalign_print_int value nb =
    print_int value;
    make_line " " (nb - (str_size_int value));
;;

let ralign_print_string str nb =
    make_line " " (nb - String.length str);
    print_string str;
;;

let lalign_print_string str nb =
    print_string str;
    make_line " " (nb - String.length str);
;;
