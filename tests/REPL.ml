open Debug
open Prelexer
open Lexer
open Sexp
open Grammar
open Pexp
open Debruijn
open Lparse
open Myers
open Eval
open Util
open Lexp
open Fmt

let print_input_line i =
    print_string "  In[";
    ralign_print_int i 2;
    print_string "] >> "
;;

(*  Read stdin for input. Returns only when the last char is ';' *)
let rec read_input i =
    print_input_line i;
    flush stdout;
    
    let rec loop str i =
        flush stdout;
        let line = input_line stdin in
        let s = String.length str in
        let n = String.length line in
            if s = 0 && n = 0 then read_input (i + 1) else
            (if n = 0 then (
                print_string "          : "; 
                print_string (make_line ' ' (i * 4)); 
                loop str (i + 1)) 
            else
        let str = if s > 0 then  String.concat "\n" [str; line] else line in
            if line.[n - 1] = ';' || line.[0] = '%' then
                str
            else (
                print_string "          . "; 
                print_string (make_line ' ' (i * 4));
                loop str (i + 1))) in
                
    loop "" 1
;;


(*  Specials commands %[command-name] *)
let rec repl () = 
    let tenv = default_stt in
    let grm = default_grammar in
    let limit = (Some ";") in
    let eval_string str clxp rctx = eval_string str tenv grm limit clxp rctx in
    let lxp_ctx = make_lexp_context in
    (*  Those are hardcoded operation *)
        let lxp_ctx = add_def "_+_" lxp_ctx in
        let lxp_ctx = add_def "_*_" lxp_ctx in
            
    let rctx = make_runtime_ctx in

    let rec loop i clxp rctx =
        let ipt = read_input i in
        (*  Check special keywords *)
            if ipt = "%quit" then ()       (* Stop REPL *)
            else if ipt = "%who" then      (* Print environment *)
                (print_rte_ctx rctx; loop (i + 1) clxp rctx)
            else if ipt = "%info" then
                (lexp_context_print clxp; loop (i + 1) clxp rctx)
            else if ipt = "%calltrace" then
                (print_call_trace (); loop (i + 1) clxp rctx)
        (*  Else Process Typer code *)
            else
                let (ret, rctx), clxp = (eval_string ipt clxp rctx) in
                let print_e j v = print_eval_result i v in
                    List.iteri print_e ret;
                    loop (i + 1) clxp rctx  in
    
    loop 1 lxp_ctx rctx
;;
                
let main () = 
    print_string (make_title " TYPER REPL ");
    print_string "      %quit      : leave REPL\n";
    print_string "      %who       : print runtime environment\n";
    print_string "      %info      : print elaboration environment\n";
    print_string "      %calltrace : print call trace of last call \n";
    print_string (make_sep '=');
    flush stdout; 

    repl ()
;;


main ()
;;