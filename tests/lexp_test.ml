open Lparse     (* add_def       *)
open Debruijn   (* make_lexp_context *)
open Lexp
open Pexp
open Utest_lib

(* default environment *)
let lctx = default_lctx ()

let _ = (add_test "LEXP" "Built-in type Inference" (fun () ->

    let dcode = "a = 10; b = 1.12;" in

    let ret, _ = lexp_decl_str dcode lctx in

        match ret with
            (* (vdef * lexp * ltype) *)
            | [(_, _, Builtin(_, "Int", _));
               (_, _, Builtin(_, "Float", _))] ->
                success()

            | _ -> failure ())
);;


let set_to_list s =
    StringSet.fold (fun g a -> g::a) s []
;;

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

));;

(* run all tests *)
run_all ()
;;
