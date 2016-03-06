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
    
    let rec loop str =
        let line = input_line stdin in
        let s = String.length str in
        let n = String.length line in
            if n = 0 then loop str else
        let str = if s > 0 then  String.concat "\n" [str; line] else line in
            if line.[n - 1] = ';' || line.[0] = '%' then
                str
            else 
                (print_string "          ";  loop str) in
                
    loop ""
;;


let eval_string (str: string) tenv grm limit lxp_ctx rctx =
    let rec eval_all lxps acc rctx = 
        match lxps with
            | [] -> (List.rev acc), rctx 
            | hd::tl ->
                let lxp, rctx = eval hd rctx in
                    eval_all tl (lxp::acc) rctx in

    let pretoks = prelex_string str in
    let toks = lex tenv pretoks in
    let sxps = sexp_parse_all_to_list grm toks limit in
    let pxps = pexp_parse_all sxps in
    let lxp, lxp_ctx = lexp_parse_all pxps lxp_ctx in
        (eval_all lxp [] rctx), lxp_ctx
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
        let lxp_ctx = add_def "_=_" lxp_ctx in
            
    let rctx = make_runtime_ctx in

    let rec loop i clxp rctx =
        let ipt = read_input i in
        (*  Check special keywords *)
            if ipt = "%quit" then ()       (* Stop REPL *)
            else if ipt = "%who" then      (* Print environment *)
                (print_rte_ctx rctx; loop (i + 1) clxp rctx)
        (*  Else Process Typer code *)
            else
                let (ret, rctx), clxp = (eval_string ipt clxp rctx) in
                let printe j v = print_eval_result i v in
                    List.iteri printe ret;
                    print_string "\n";
                    loop (i + 1) clxp rctx  in
    
    loop 1 lxp_ctx rctx
;;
                
let main () = 
    print_string ((make_line '-' 80) ^ "\n");
    print_string "   Typer REPL \n";
    print_string "      %quit to leave\n";
    print_string "      %who to print environment\n";
    print_string ((make_line '-' 80) ^ "\n\n");
    flush stdout; 

    repl ()
;;


main ()
;;