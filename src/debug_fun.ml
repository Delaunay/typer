
open Fmt_lexp

(* let _debug = true *)
let _debug = false

let logs = ref []

let do_debug func =
  if _debug then (func ()) else ()

let debug_print str1 str2 =
  logs := ((padding_left str1 20 ' ')^" : ", (str2^"\n"))::(!logs); ()

let clear_indent () =
  let indent = ref 0
  in
  do_debug (fun () ->
      List.iter (fun (s1, s2) ->
          print_string s1;
          print_string (String.make (!indent * 2) '-');
          print_string s2;
          indent := !indent + 1;
        ) (!logs);
      logs := [];
      print_newline ();
      ())

let debug_print_lexp lxp =
  let str = colored_string_of_lxp lxp str_yellow str_magenta
  in do_debug (fun () -> print_string str; ())

let debug_print_unify fn lhs rhs str =
    let debug_print_unify fn lhs rhs str =
      let tmp = ((padding_left fn 20 ' ') ^ " : ",
                  (colored_string_of_lxp lhs str_yellow str_magenta)
                  ^ " , "
                  ^ colored_string_of_lxp rhs str_yellow str_magenta
                  ^ str ^ "\n")
      in
      logs := tmp::(!logs);
    in do_debug (fun () -> debug_print_unify fn lhs rhs str; ())

