
open Lparse
open Fmt_lexp
open Utest_lib

open Pexp
open Lexp

open Builtin

let test
    (input_gen: (unit -> 'a list))
    (fmt: 'b list -> string list)
    (tester: 'a -> ('b * bool)): (string * bool) list =
  let input = List.map tester (input_gen ())
  in let str = List.map (fun (s, _) -> s ) input
  in let b = List.map (fun (_, b) -> b) input
  in List.combine (fmt str) b

let generate_tests (name: string)
    (input_gen: (unit -> 'a list))
    (fmt: 'b list -> string list)
    (tester: 'a -> ('b * bool)) =
  let idx = (ref 0)
  in List.map (fun (sub, res) ->
      idx := !idx + 1;
      add_test name
        ((padding_left (string_of_int (!idx)) 2 '0') ^ " - " ^ sub)
        (fun () -> if res then success () else failure ()))
    (test input_gen fmt tester)

(* let input = "y = lambda x -> x + 1;" *)
let input = "id = lambda (α : Type) ≡> lambda x : α -> x;"

let generate_lexp_from_str str =
  List.hd ((fun (lst, _) ->
      (List.map
         (fun (_, lxp, _) -> lxp))
        (List.flatten lst))
       (lexp_decl_str str default_lctx))

let _ = generate_tests
    "TYPECHECK"
    (fun () -> [generate_lexp_from_str input])
    (fun x -> List.map string_of_lxp x)
    (fun x -> (x, false))

let lctx = default_lctx
let _ = (add_test "TYPECHEK_LEXP" "lexp_print" (fun () ->

    let dcode = "
        sqr = lambda (x) -> x * x;
        cube = lambda (x) -> x * (sqr x);

        mult = lambda (x) -> lambda (y : Int) -> x * y;

        twice = (mult 2);

        let_fun = lambda (x) ->
            let a = (twice x); b = (mult 2 x); in
                a + b;" in

    let ret1, _ = lexp_decl_str dcode lctx in

    let to_str decls =
        let str = _lexp_str_decls (!compact_ppctx) (List.flatten ret1) in
            List.fold_left (fun str lxp -> str ^ lxp) "" str in

    (* Cast to string *)
    let str1 = to_str ret1 in

    (* read code again *)
    let ret2, _ = lexp_decl_str str1 lctx in

    (* Cast to string *)
    let str2 = to_str ret2 in

    if str1 = str2 then success () else failure ()
))

(*
let set_to_list s =
    StringSet.fold (fun g a -> g::a) s []

let _ = (add_test "LEXP" "Free Variable" (fun () ->

    let dcode = "
        a = 2;
        b = 3;
        f = lambda n -> (a + n);           % a is a fv
        g = lambda x -> ((f b) + a + x);   % f,a,b are fv
    " in

    let ret = pexp_decl_str dcode in
    let g = match List.rev ret with
        | (_, g, _)::_ -> g
        | _ -> raise (Unexpected_result "Unexpected empty list") in

    let (bound, free) = free_variable g in

    let bound = set_to_list bound in
    let (free, _) = free in

    match bound with
        | ["x"] ->(
            match free with
                | ["_+_"; "f"; "b"; "a"] -> success ()
                | _ -> failure ())
        | _ -> failure ()

)) *)

(* run all tests *)
let _ = run_all ()

let _ = run_all ()
