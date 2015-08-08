(* javascript.ml --- Javascript backend.

Copyright (C) 2012  Alexandre St-Louis

Author: Alexandre St-Louis <stlouial@iro.umontreal.ca>
Keywords: languages, lisp, dependent types, javascript.

This file is part of Typer.

Typer is free software; you can redistribute it and/or modify it under the
terms of the GNU General Public License as published by the Free Software
Foundation, either version 3 of the License, or (at your option) any
later version.

Typer is distributed in the hope that it will be useful, but WITHOUT ANY
WARRANTY; without even the implied warranty of MERCHANTABILITY or FITNESS
FOR A PARTICULAR PURPOSE.  See the GNU General Public License for
more details.

You should have received a copy of the GNU General Public License along with
this program.  If not, see <http://www.gnu.org/licenses/>.  *)

module U = Ulexp
open Lexp
open Sexp
open Prelexer
open Pexp
open Util


(** Javascript internal representation.  **)
type jsvar = int
 and jssymbol = string
 and number =
  | JsFloat of float
  | JsInt of int
 and primitive =
  | Builtins of string
  | Number of number
  | JsString of string
  | AssociativeArr of (jssymbol * jsexp) list
  | Undefined
  | Null
 (* Loops are special statements.  *)
 and loop =
  | For of jsstatement * jsstatement * jsstatement * jsstatement list
  | While of jsexp * jsstatement list

 (* A javascript statement is an expression that dos not evaluate to a value
    and hence can't be passed as argument.  *)
 and jsstatement =
  | Statement of jsexp
  | Loop of loop
  | IfStatement of jsexp * jsstatement list * jsstatement list option
  | Return of jsexp
  | Declaration of jsexp * jsexp option
  | Sequence of jsstatement list

 (* A javascript statement is an expression that can be passed as argument;
    it evaluates to a value.  *)
 and jsexp =
  | JsVar of jsvar
  | Primitive of primitive
  | Function of jsvar list * jsstatement list
  | FunctionCall of jsexp * jsexp list (*1st should either be Function/JsVar*)
  | Assignement of jsexp * jsexp
  | IfThenElse of jsexp * jsexp * jsexp
  | MemberAccess of jsexp * jsexp
  | ArrayAccess of jsexp * jsexp
  | IdOp_ of jsexp * jsexp
  | SumOp_ of jsexp * jsexp
  | ConcatOp of jsexp * jsexp
  | TypeOf_ of jsexp



(** Javascript associative array **)
module JsMap = Map.Make (struct type t = primitive let compare = compare end)




(** From lambda expression to javascript expression **)
let rec lexp_to_jsexp lexp = match lexp with
  | Imm String (_,s) -> Primitive (JsString s)
  | Imm Float (_,x) -> Primitive (Number (JsFloat x))
  | Imm Integer (_,n) -> Primitive (Number (JsInt n))
  | Imm _ -> Primitive Undefined
  | Var (_, v)-> JsVar v
  | Let (_, decls, body)->
      let letVars = List.map (fun((_,v),_,_)->v) decls
      in
      let rec isMutualRec currentvar exp = match exp with
        | Call(f,args) -> isMutualRec currentvar f
                          || List.exists (fun (_,e)-> isMutualRec currentvar e)
                                         args
        | Var(_,v) -> v != currentvar && List.exists ((==) v) letVars
        | Let (_,d,b) -> List.exists (fun (_,le,_) ->
                                        isMutualRec currentvar le)
                                    d
                         || isMutualRec currentvar b
        | Lambda (_,_,_,e) -> isMutualRec currentvar e
        | _ -> false
      in
      let make_decl = List.map
                      (fun ((_,v),e,_) ->
                         if (isMutualRec v e)
                           then Declaration(JsVar v,None)
                           else Declaration (JsVar v, Some (lexp_to_jsexp e)))
      and make_assign =
        let compose f g = fun x -> f(g x) in
        compose (List.map (fun ((_,v),e,_) ->
                             Statement (Assignement(JsVar v, lexp_to_jsexp e))))
                (List.filter (fun ((_,v),e,_) -> isMutualRec v e))

      in
      FunctionCall(Function ([],(make_decl decls)@(make_assign decls)@[Return (lexp_to_jsexp body)]),[])
  | Lambda (Aerasable,(_,var),_,expression) -> lexp_to_jsexp expression
  | Lambda (_,(_,var),_,expression) -> Function ([var],[Return (lexp_to_jsexp expression)])
  | Call (f,args) ->
      let not_erasable (argkind,_) = match argkind with
        |Aerasable -> false
        | _ -> true
      (* make_args removes erasable arguments then converts those remaining to
      javascript expressions *)
      in
      let mk_args args = List.map (fun(_,v)-> lexp_to_jsexp v)
                                  (List.filter not_erasable args)
      in let rec has_nonerasable args = match args with
        | [(Aerasable,_)]   -> false
        | (Aerasable,_)::xs -> false
        | x::xs             -> has_nonerasable xs
        | []                -> true
      in (match f with
        | Lambda (Aerasable,_,_,e) -> lexp_to_jsexp e
        | Lambda (_,_,_,_) -> FunctionCall (lexp_to_jsexp f, mk_args args)
        (* Possible bug if Var refers to a function which as been stipped of
        all its argument.
        Example of what could happen: a=2;a();
        Maybe introduce special vars or vars that know what they references
        *)
        | Var (_,_) -> if has_nonerasable args
                          then FunctionCall (lexp_to_jsexp f, mk_args args)
                          else lexp_to_jsexp f
        | _         -> lexp_to_jsexp f) (* Should never happen. Maybe I
                                        should try to throw an error if
                                        possible error *)

  | Inductive ((_,v),_,branches) ->
      let mk_ind (k,_) =
        (k, Function ([], [Return(Primitive(Builtins("[" ^ k ^
                        "].concat(Array.prototype.slice.call(arguments))")))]))
      in
      Primitive(AssociativeArr (List.map mk_ind (SMap.bindings branches)))
  | Cons (t,(_,name)) -> MemberAccess (lexp_to_jsexp t,Primitive (Builtins name))
  | Case (_,e,lt,branches,default_exp) ->
      let mk_branch args lexp =
        let not_erasable (argkind,_) = match argkind with
          |Aerasable -> false
          | _ -> true
        and call args =
          let rec call' n out =
            if n == 0
            then out
            else call' (n-1) (ArrayAccess(lexp_to_jsexp e,Primitive(Number(JsInt n)))::out)
          in call' (List.length args) []
        in
        let currentargs = List.map (fun (_,(_,x)) -> x) (List.filter not_erasable args)
        in
        FunctionCall(Function(currentargs, [Return (lexp_to_jsexp lexp)]),
                     call currentargs)
      in
      let rec build_case l = match l with
        | []    -> (match default_exp with
                      | Some e -> lexp_to_jsexp e
                      | None -> Primitive Undefined)
        | (key,(_,args,lexp))::xs -> IfThenElse(IdOp_(Primitive(Builtins key),
                                                 ArrayAccess(
                                                  IfThenElse(
                                                   IdOp_(Primitive(JsString "function"),
                                                         TypeOf_ (lexp_to_jsexp e)
                                                   ),
                                                   FunctionCall(lexp_to_jsexp e, []),
                                                   lexp_to_jsexp e
                                                  ),
                                                  Primitive(Number(JsInt 0)))),
                                           mk_branch args lexp,
                                           build_case xs)
      in
      build_case (SMap.bindings branches)
  | (Metavar (_, _, _)|Susp (_, _)|Arrow (_, _, _, _, _)|Sort (_, _))
    -> internal_error "Metavar|Susp|Arrow|Sort in Jsexp.lexp_to_jsexp"









(** FROM ULEXP TO JSEXP **)
let rec from_ulexp ulexp = match ulexp with
  | U.Imm String (_,s) -> Primitive (JsString s)
  | U.Imm Float (_,x) -> Primitive (Number (JsFloat x))
  | U.Imm Integer (_,n) -> Primitive (Number (JsInt n))
  | U.Imm _ -> Primitive Undefined
  | U.Var (_,v)-> JsVar v
  | U.Let ((_,v),e, body)->
      FunctionCall(Function ([],[Declaration(JsVar v, Some (from_ulexp e));
                                 Return (from_ulexp body)]),[])
  | U.Letrec (_,decls, body)->
      let make_decl = List.map (fun ((_,v),e) ->
        Declaration(JsVar v, None))
      and make_assign = List.map (fun ((_,v),e) ->
        Statement (Assignement(JsVar v, from_ulexp e)))
      in
      FunctionCall(Function ([],(make_decl decls)@(make_assign decls)@[Return (from_ulexp body)]),[])
  | U.Function (args,e) -> Function (List.map snd args,[Return(from_ulexp e)])
  | U.Call (f,args) -> FunctionCall (from_ulexp f, List.map from_ulexp args)
  | U.Inductive ((_,v),branches) ->
      let mk_inductive (k,_) =
        (k, Function ([], [Return(Primitive(Builtins("λ.cons()")))]))
      in Primitive(AssociativeArr (List.map mk_inductive (SMap.bindings branches)))
      (*let mk_ind (k,_) =
        (k, Function ([], [Return(Primitive(Builtins("[" ^ k ^
                        "].concat(Array.prototype.slice.call(arguments))")))]))
      in Primitive(AssociativeArr (List.map mk_ind (SMap.bindings branches)))*)
  | U.Cons (t,(_,name)) -> MemberAccess (lexp_to_jsexp t,Primitive (Builtins name))
  | U.Case (_,e,lt,branches,default_exp) ->
      let call args =
          let rec call' n out =
            if n == 0
            then out
            else call' (n-1) (ArrayAccess(from_ulexp e,Primitive(Number(JsInt n)))::out)
          in call' (List.length args) []
      in
      let mk_condition key = IdOp_(
                               Primitive(Builtins key),
                               ArrayAccess(
                                 IfThenElse(
                                   IdOp_(Primitive(JsString "function"),
                                         TypeOf_ (from_ulexp e)),
                                   FunctionCall(from_ulexp e, []),
                                   from_ulexp e),
                                 Primitive(Number(JsInt 0))))
      and mk_branch args lexp =
        let currentargs = List.map (fun (_,x) -> x) args
        in FunctionCall(Function(currentargs,
                                 [Return (from_ulexp lexp)]),
                        call currentargs)
      in
      let rec build_case l = match l with
        | []    -> (match default_exp with
                      | Some e -> from_ulexp e
                      | None -> Primitive Undefined)
        | (key,(_,args,lexp))::[] -> (match default_exp with
            | Some e -> IfThenElse(mk_condition key,
                                   mk_branch args lexp,
                                   from_ulexp e)
            | None -> mk_branch args lexp)

        | (key,(_,args,lexp))::xs ->
            IfThenElse(mk_condition key,
                       mk_branch args lexp,
                       build_case xs)
      in build_case (SMap.bindings branches)










let rec print_jsexp printer expression =
  let rec print_join element_printer l = match l with
    | []    -> ()
    | [x]   -> element_printer x
    | x::xs -> element_printer x;
               printer ",";
               print_join element_printer xs
  and print_number printer num = match num with
    | JsFloat x -> printer (string_of_float x)
    | JsInt n   -> printer (string_of_int n)


  in
  match expression with
    | Primitive Number x   -> print_number printer x
    | Primitive Builtins s -> printer s
    | Primitive Undefined  -> printer "undefined"
    | Primitive Null       -> printer "null"
    | Primitive JsString s -> printer "\"";
                              printer s;
                              printer "\""
    | JsVar (v) -> printer (varname v)
    | IfThenElse (condition,then_clause,else_clause) ->
        printer "(";
        print_jsexp printer condition;
        printer ")?";
        print_jsexp printer then_clause;
        printer ":";
        print_jsexp printer else_clause;
    | Function (args,statements) ->
        let args_printer x = printer (varname x)
        and statement_printer = List.iter (print_jsstatement printer)
        in
        printer "function(";
        print_join args_printer args;
        printer "){";
        statement_printer statements;
        printer "}"
    | FunctionCall (f,args) ->
        let args_printer = print_jsexp printer
        in
        (match f with
           | Function (_,_) | FunctionCall (_,_)-> printer "(";
                                                   print_jsexp printer f;
                                                   printer ")"
           | _   -> print_jsexp printer f);
        (match args with
           | [] -> printer "()"
           | _ ->  List.iter (fun x -> printer "("; args_printer x; printer ")")
                             args)
        (*printer "(";
        print_join args_printer args;
        printer ")"*)
    | Assignement (v,e) ->
        print_jsexp printer v;
        printer "=";
        print_jsexp printer e
    | Primitive AssociativeArr(consList) ->
        let print_ind (k, v) = printer k;
                               printer ":";
                               print_jsexp printer v
        in
        let rec join l =
           match l with
             | [] -> printer ""
             | [x] -> print_ind x
             | x::xs -> print_ind x; printer ","; join xs
        in
        printer "{";
        join consList;
        printer "}"
    | MemberAccess(container,member) -> print_jsexp printer container;
                                        printer ".";
                                        print_jsexp printer member
    | ArrayAccess(container,member) -> (match container with
        | JsVar _ -> print_jsexp printer container
        | _       -> printer "(";
                     print_jsexp printer container;
                     printer ")";
                     printer "[";
                     print_jsexp printer member;
                     printer "]")
    | IdOp_ (e1,e2) -> print_jsexp printer e1;
                       printer "===";
                       print_jsexp printer e2
    | TypeOf_ (e) -> printer "typeof ";
                    print_jsexp printer e


and print_jsstatement printer statement =
  match statement with
    | Statement expression ->
        print_jsexp printer expression;
        printer ";"
    | Loop While (condition,statements) ->
        printer "while(";
        print_jsexp printer condition;
        printer "){";
        List.iter (print_jsstatement printer) statements;
        printer "}"
    | Loop For (init,cond,after,statements) ->
        printer "for(";
        print_jsstatement printer init;
        print_jsstatement printer cond;
        print_jsstatement printer after;
        printer "){";
        List.iter (print_jsstatement printer) statements;
        printer "}"

    | IfStatement (condition,then_clause,else_clause) ->
        printer "if(";
        print_jsexp printer condition;
        printer "){";
        List.iter (print_jsstatement printer) then_clause;
        printer "}";
        (match else_clause with
           | Some expression ->
               printer "else{";
               List.iter (print_jsstatement printer) expression;
               printer "}"
           | None -> ())
    | Return e -> printer "return ";
                  print_jsexp printer e;
                  printer ";"
    | Declaration (var, expression) ->
        printer "var ";
        print_jsexp printer var;
        (match expression with
           | Some e -> printer "=";
                       print_jsexp printer e
           | None -> ());
        printer ";"

(*
let optimize jsexp = match jsexp with
  | Assignment(v, Function(_,statement)) -> match last statement with
      | Return (FunctionCall(f,args)) ->
      | _ -> jsexp*)

(** Boilerplate Javascript code, appended at the beginning of the file  *)
let intro =
  "var λ = {
     merge: function (cons, args) {
              var length = args.length;
              for (i = 0; i < length; i++)
                cons[i] = args[i];
     },
     cons: function () {
       var f;
       var cons = function(args){ λ.merge(this, args) };
       (f = function () {return new cons(arguments)}).constructor = cons
       return f ;
     }
   }
  "


(** Js traduction and   **)

let translate_to_js ulexp = Statement(from_ulexp ulexp)

let output_jsexp jsstatement = print_jsstatement print_string jsstatement






(*let js_file_prntr dest str = output_string (open_out dest) str

let jsexp_parse printer lexp = lexp_to_js printer lexp;
                               printer ";"
let jsexp_parse_to_console = jsexp_parse print_string*)
