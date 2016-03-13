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

(* Interactive mode is not usual typer 
 * It makes things easier to test out code *)
type ptop =
    | Pdecl of pvar * pexp * bool
    | Pexpr of pexp
    
let ipexp_parse p =
    match p with 
        (* Declaration *)
        | Node (Symbol (_, "_=_"), [Symbol s; t]) ->
             let (a, b, c)::_ = pexp_p_decls nod in
                Pdecl(a, b, c)
        | Node (Symbol (_, "_:_"), [Symbol s; t]) ->
            let (a, b, c)::_ = pexp_p_decls nod in
                Pdecl(a, b, c)
        (* Expression *)
        | _ -> let a = pexp_parse nod in Pexpr(a)
;;
        
let ipexp_parse_all ps = List.map ipexp_parse ps;;
    
type ltop =
    | Ldecl of vdef * lexp * ltype
    | Lexpr of lexp
    
let ilexp_parse l lctx =
    match l with
        | Pdecl(_, _, _) -> let (a, b, c), d = lexp_decls [l] ctx in
            Ldecl(a, b, c), d
        | Pexpr(x) -> let v, c = lexp_parse x lctx in
            Lexpr(v), c
            
let ilexp_parse_all ls lctx =
    let rec loop lst acc ctx =
        match lst with
            | [] -> List.rev acc, ctx
            | hd::tl ->
                let x, c = ilexp_parse hd ctx in
                let nacc = acc::x in
                    loop tl nacc c in
    loop ls [] lctx
    
type ival = 
    | Ivoid
    | Ival of lexp

let ieval xpr rctx =
    match xpr with
        | Ldecl(_, _, _) -> let r = eval_decls xpr rctx in
            Ivoid, rctx
        | Lexpr(x) -> let v, _ = eval x rctx in
            Ival(v), rctx

let ieval_all xprs rctx =
    let rec loop lst acc ctx =
        match lst with
            | [] -> List.rev acc, ctx
            | hd::tl ->
                let x, c = ieval hd ctx in
                let nacc = acc::x in
                    loop tl nacc c in
    loop xprs [] rctx

let ieval_string str lctx rctx =
    let pres = prelex_string str in
    let sxps = lex default_stt pres in
    let nods = sexp_parse_all_to_list default_grammar sxps (Some ";") in
    
    (*  Different from usual typer *)
    let pxps = ipexp_parse_all nods in
    let lxps, ctx = ilexp_parse_all pxps lctx in
    let v, rctx = ieval_all lxps rctx in
        v, lctx, rctx
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
                let (ret, clxp, rctx) = (ieval_string ipt clxp rctx) in
                
                let print_e j v = 
                    match b with
                        | Ivoid -> ()
                        | Ival(x) -> print_eval_result i x in
                        
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