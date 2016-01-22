
open Util
open Prelexer
open Debug

let main () =

    print_endline Sys.argv.(0);
    print_endline Sys.argv.(1);
    
    let file_name = (Sys.argv.(1) ^ "/samples/lexer_test.typer") in
        prelex_file file_name
;;

main ()
;;