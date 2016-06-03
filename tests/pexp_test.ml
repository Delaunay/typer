open Pexp
open Utest_lib


let _ = (add_test "PEXP" "Type Parsing" (fun () ->

    let dcode = "
        let a : Nat; a = 1; b : Nat; b = 3; in a + b;" in

    let ret = pexp_expr_str dcode in
        match ret with
            | [expr] ->(
            match expr with
                | Plet(_, arg, _) -> (match arg with
                    | Ptype(_, tp)::_ ->success ()
                    | _ -> failure ())
                | _ -> failure ())
            | _ -> failure ())
)


let _ = run_all ()
