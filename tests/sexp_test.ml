open Sexp
open Lexer
open Utest_lib


(*  _+_ precedence is too low ?
 *
 * a = lambda x -> x + x + x
 * is parsed to
 * a = (_+_ (_+_ (lambda_->_ x x) x) x)  <=> a = (lambda x -> x) + x + x
 * instead of
 * a = (lambda_->_ x (_+_ (_+_ x x) x)) *)
let _ = (add_test "SEXP" "lambda x -> x + x" (fun () ->

    let dcode = "lambda x -> x + x;" in

    let ret = sexp_parse_str dcode in
        match ret with
          | [Node(lbd, [x; add])] -> (match lbd, x, add with
            | (Symbol(_, "lambda_->_"), Symbol(_, "x"),
               Node(Symbol(_, "_+_"), [Symbol(_, "x"); Symbol(_, "x")])) -> success ())
          | _ -> failure ()
));;


(*  _*_ is not a binary operator
 *
 * b = lambda x -> (x * x * x);
 * is parsed to
 * b = (lambda_->_ x (_*_ x x x))
 * instead of
 * b = (lambda_->_ x (_*_ (_*_ x x) x))     *)
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

));;

(* run all tests *)
run_all ()
;;
