open Util
open Prelexer
open Debug

let main () = 
    let file = Sys.argv.(1) in
    print_string file;
    print_string "\n";
    
    let arr = prelex_file file in
    debug_pretokens_print_all arr
;;

main ();
