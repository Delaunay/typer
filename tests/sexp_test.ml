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

let test_sexp_eqv dcode1 dcode2 =
  add_test "SEXP" dcode1
           (fun () ->
             let s1 = sexp_parse_str dcode1 in
             let s2 = sexp_parse_str dcode2 in
             if sexp_eq_list s1 s2
             then success ()
             else (sexp_print (List.hd s1);
                   sexp_print (List.hd s2);
                   failure ()))

let _ = test_sexp_eqv "((a) ((1.00)))" "a 1.0"
let _ = test_sexp_eqv "(x + y)" "_+_ x y"
let _ = test_sexp_eqv "(x := y)" "_:=_ x y"
let _ = test_sexp_eqv "if A then B else C -> D" "if A then B else (C -> D)"
let _ = test_sexp_eqv "A : B -> C" "A : (B -> C)"
let _ = test_sexp_eqv "f __\\; y" "(f (__\\;) y)"
let _ = test_sexp_eqv "case e | p1 => e1 | p2 => e2"
                      "case_ (_|_ e (_=>_ p1 e1) (_=>_ p2 e2))"
let _ = test_sexp_eqv "a\\b\\c" "abc"
let _ = test_sexp_eqv "(a;b)" "(_\\;_ a b)"
let _ = test_sexp_eqv "a.b.c . (.)" "(__\\.__ (__\\.__ a b) c) \\. \\."

(* run all tests *)
let _ = run_all ()
