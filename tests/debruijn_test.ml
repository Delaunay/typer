(*  TODO make some real test *)
open Debruijn
open Util

let main () = 
    (*  Tests *)
    (*  Create a new scope: global scope *)
    let loc = dummy_location in
    let g0 = make_context in
    let g1 = add_variable "a" loc g0 in 
    let g2 = add_variable "a" loc g1 in 
    let g3 = add_variable "b" loc g2 in 
    let g4 = add_variable "c" loc g3 in 
    let g5 = add_variable "d" loc g4 in 

        (*  we enter a let or whatever *)
        let l0 = add_scope g5 in
        let l1 = add_variable "a" loc l0 in
        let l2 = add_variable "e" loc l1 in
        
        (*  Testing is done *)
        print_string "Inner Context\n";
        print_lexp_context l2;
        
        (*  We exit the scope *)
        print_string "Outer Context\n";
        print_lexp_context g5
;;


main ()
;;