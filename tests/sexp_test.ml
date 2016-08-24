open Sexp
open Lexer
open Utest_lib

let test_sexp_add dcode testfun =
  add_test "SEXP" dcode (fun () -> testfun (sexp_parse_str dcode))

let _ = test_sexp_add "lambda x -> x + x" (fun ret ->
        match ret with
        | [Node(Symbol(_, "lambda_->_"),
                [Symbol(_, "x");
                 Node(Symbol(_, "_+_"), [Symbol(_, "x"); Symbol(_, "x")])])]
          -> success ()
        | _ -> failure ()
)

let _ = test_sexp_add "x * x * x" (fun ret ->
        match ret with
        | [Node(Symbol(_, "_*_"),
                [Node(Symbol(_, "_*_"), [Symbol(_, "x"); Symbol(_, "x")]);
                 Symbol(_, "x")])]
          -> success ()
        | _ -> failure ()
)

(* run all tests *)
let _ = run_all ()
