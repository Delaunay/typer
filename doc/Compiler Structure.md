Typer Compiler Structure
========================

Read tests/full_debug.ml for ocaml usage


* in_channel -> PreLexer: PreToken

Skips Blocks and identifies Strings

    Blocks  : {this is a block}
    String  : "this is a string"
    PreToken: a pretoken is everything else

Code: "a => 3;"
    Pretoken: ['a', '=>', '3;']

Functions:
    prelex_file file
    prelex_string str

* PreToken -> Lexer: Sexp

Process PreToken. Cut them in smaller pieces according to [stt : token_env]
For example:

    Code: "a => 3;"
    Lexer => ['a', '=>', '3', ';']

Here ';' is in stt which makes the '3;' pretoken to explode in two.

Functions:
    lex stt pretoken
    lex_string str

* Sexp -> sexp_parse: Node Sexp

Group Sexp into Nodes according to the specified grammar.
Create the program tree.

    Code: "a => 3;"
    sexp_parse => Node('_=>_', ['a', '3'])

Functions:
    sexp_parse sexp
    sexp_parse_str str

* Sexp -> Pexp: ~ Lexical Analysis

Identify nodes and transform them into language primitives

    Code: "a => 3;"
    Pexp: PArrow(kind='=>', a, 3)

Functions:
    pexp_parse sexp     % For evaluable expression
    pexp_p_decls        % For top level declaration

* Pexp -> Lexp: ~ Semantic Analysis

Replace variable name by their (reverse) index in the environment.
Lexps are very close to pexps

    Code: "a => 3;"
    Lexp: Arrow(kind='=>', a, 3)

Functions:
    lexp_parse
    lexp_p_decls
    lexp_expr_str
    lexp_decl_str

* Lexp -> Value: ~ Evaluation

Functions:
    eval_all        % Evals expression do not modify runtime
    eval_decls      % Evals declaration modify runtime env
    eval_decl_str
    eval_expr_str




