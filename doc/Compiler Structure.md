
Typer Compiler Structure
========================

Read tests/full_debug.ml for ocaml usage


* in_channel -> PreLexer: PreToken
    
    Skips Blocks and identifies Strings
        
        Blocks  : {this is a block}
        String  : "this is a string"
        PreToken: a pretoken is everything else
    
    Function:
        prelex_file file
        
    TODO:
        prelex_str "my code"
        
* PreToken -> Lexer: Sexp 
    
    Process PreToken. Cut them in smaller pieces according to [stt : token_env]
    For example:
    
        Code: "a => 3;"
        
        Pretoken: ['a', '=>', '3;']
        
        Lexer ['a', '=>', '3;'] => ['a', '=>', '3', ';']
        
    Here ';' is in stt which makes the '3;' pretoken to explode in two.
    
    Function:
        lex stt pretoken
    
* Sexp -> sexp_parse: Sexp
    
    Group Sexp into Nodes according to the specified grammar.
    
    Code: "a => 3;"
        
    Pretoken: ['a', '=>', '3;']
    
    Lexer ['a', '=>', '3;'] => ['a', '=>', '3', ';'] (Sexp)
    
    sexp_parse ['a', '=>', '3', ';']
        => [Node('=>', ['a', '3']), ';'] (Sexp)
        
    Function:
        sexp_parse sexp
        
* Sexp -> Lexp