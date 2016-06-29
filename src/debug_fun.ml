
open Fmt_lexp

let _debug = true

let indent = ref 0

let do_debug func =
  if _debug then (func ()) else ()

let clear_indent () =
  do_debug (fun () -> indent := 0; ())

let unindent () =
  do_debug (fun () -> indent := (max 0 (!indent - 1)); ())

let debug_print_lexp lxp =
  let str = colored_string_of_lxp lxp str_yellow str_magenta
  in do_debug (fun () -> print_string str; ())

let debug_print_unify fn lhs rhs str =
    let debug_print_unify fn lhs rhs str =
      print_newline ();
      print_string (padding_left fn 10 ' ');
      print_string " : ";
      print_string (String.make (!indent * 4) '-');
      debug_print_lexp lhs;
      print_string " , ";
      debug_print_lexp rhs;
      print_string str;
      indent := !indent + 1;
    in do_debug (fun () -> debug_print_unify fn lhs rhs str; ())
