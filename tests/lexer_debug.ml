open Util
open Prelexer
open Sexp
open Lexer
open Debug

let default_stt =
  let stt = Array.create 256 false
  in stt.(Char.code ';') <- true;
     stt.(Char.code ',') <- true;
     stt.(Char.code '(') <- true;
     stt.(Char.code ')') <- true;
     stt

let main () = 
    (*
     *  print tokens/sexp of the file given as first arg
     *
     ********************************************************)
    
    let file = Sys.argv.(1) in
    print_string file;
    print_string "\n";
    
    (* Todo read file from prog args *)
    (* get pretokens*)
    let pretoks = prelex_file file in
    
    (* get tokens *)
    let toks = lex default_stt pretoks in
    
    (* print tokens *)
    debug_sexp_print_all toks
;;

main ();;