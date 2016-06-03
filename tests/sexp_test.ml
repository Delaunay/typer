open Sexp
open Lexer
open Utest_lib

let _ = (add_test "SEXP" "lambda x -> x + x" (fun () ->

    let dcode = "lambda x -> x + x;" in

    let ret = sexp_parse_str dcode in
        match ret with
            | [Node(lbd, [x; add])] -> (match lbd, x, add with
                | (Symbol(_, "lambda_->_"), Symbol(_, "x"),
                   Node(Symbol(_, "_+_"), [Symbol(_, "x"); Symbol(_, "x")])) -> success ()
                | _ -> failure ())
          | _ -> failure ()
))

let _ = (add_test "SEXP" "x * x * x" (fun () ->

  let dcode = "x * x * x;" in

  let ret = sexp_parse_str dcode in
    match ret with
      | [n] ->(match n with
        | Node(Symbol(_, "_*_"),
          [Node(Symbol(_, "_*_"), [Symbol(_, "x"); Symbol(_, "x")]); Symbol(_, "x")])
            -> success ()

        | Node(Symbol(_, "_*_"),
          [Symbol(_, "x"); Node(Symbol(_, "_*_"), [Symbol(_, "x")]); Symbol(_, "x")])
            -> success ()

        | _ -> failure ())
      | _ -> failure ()

))

(* run all tests *)
let _ = run_all ()
