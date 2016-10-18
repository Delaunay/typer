
(* let _debug = true *)
let _debug = false

let logs = ref []

(** Execute the function if _debug = true*)
let do_debug func =
  if _debug then (func ()) else ()

(** print the two string parameter (buffered print) *)
let debug_print str1 str2 =
  logs := ((Fmt_lexp.padding_left str1 20 ' ')^" : ", (str2^"\n"))::(!logs); ()

let clear_indent () =
  let indent = ref 0
  in
  do_debug (fun () ->
      List.iter (fun (s1, s2) ->
          prerr_string s1;
          prerr_string (String.make (!indent * 2) '-');
          prerr_string s2;
          indent := !indent + 1;
        ) (!logs);
      logs := [];
      prerr_newline ();
      ())

(** Print when _debug = true. No buffer *)
let debug_print_no_buff str =
  do_debug (fun () -> prerr_string str; ())

(** Print a lxp when _debug = true. No buffer *)
let debug_print_lexp lxp =
  let str = Lexp.lexp_string lxp
  in do_debug (fun () -> prerr_string str; ())

(** Helper for printing in a unify* function. Buffered *)
let debug_print_unify fn lhs rhs str =
    let debug_print_unify fn lhs rhs str =
      let tmp = ((Fmt_lexp.padding_left fn 20 ' ') ^ " : ",
                 Lexp.lexp_string lhs
                 ^ " , "
                 ^ Lexp.lexp_string rhs
                 ^ str ^ "\n")
      in
      logs := tmp::(!logs);
    in do_debug (fun () -> debug_print_unify fn lhs rhs str; ())

