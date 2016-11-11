(* ulexp.ml --- Type-erased Lambda expressions.

Copyright (C) 2012  Alexandre St-Louis

Author: Alexandre St-Louis <stlouial@iro.umontreal.ca>
Keywords: languages, lisp, dependent types.

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

module L = Lexp
open Sexp
open Prelexer
open Pexp
open Util


(** Things to replace in their respective files.  **)
let rec pretokens_to_str pretokens =
  List.fold_left (fun acc pt ->
                 acc ^ " " ^ match pt with
                               | Preblock(_,pts,_) ->
                                   "{" ^ (pretokens_to_str pts) ^ " }"
                               | Pretoken(_, str) ->
                                   str
                               | Prestring(_, str) -> "\"" ^ str ^ "\"")
                 ""
                 pretokens


let rec sexp_to_str sexp =
  match sexp with
    | Epsilon -> "()"
    | Block(_,pts,_) -> "{" ^ (pretokens_to_str pts) ^ " }"
    | Symbol(_, name) ->  name
    | String(_, str) -> "\"" ^ str ^ "\""
    | Integer(_, n) ->  string_of_int n
    | Float(_, x) ->  string_of_float x
    | Node(f, args) ->
        "(" ^
        (sexp_to_str f) ^
        (List.fold_left (fun str sexp -> str ^ " " ^ (sexp_to_str sexp))
                        ""
                        args) ^
        ")"



(** Types declarations ********************************************************)

module VMap = Map.Make (struct type t = int let compare = compare end)
module VSet = Set.Make (struct type t = int let compare = compare end)
module SCC = Set.Make (struct type t = VSet.t let compare = VSet.compare end)

exception Parse_error

type var = int
 and varo = location * var
 and ulexp =
  | Imm of sexp                        (* Used for strings, ...  *)
  | Var of varo
  | Let of varo * ulexp * ulexp
  | Letrec of location * (varo * ulexp) list * ulexp
  | Function of varo list * ulexp
  | Call of ulexp * ulexp list (* Curried call.  *)
  (* This is just used to keep track of the shape of the values manipulated,
   * it is not an actual run-time entity.  *)
  | Inductive of varo * L.lexp SMap.t
  | Cons of L.ltype * symbol
  | Case of location * ulexp
            * L.ltype
            * (location * varo list * ulexp) SMap.t
            * ulexp option               (* Default.  *)
  (*| Constructor *)



(* Here is the default pattern match done over ulexp:
  match ulexp with
   | Imm(sexp) ->
   | Sort(l,s) ->
   | Arrow ((l,v),l,e) ->
   | Var(l,v) ->
   | Lambda(v,e) ->
   | Let(l,decls, body) ->
   | Letrec(l,decls, body) ->
   | Call(f,args) ->
   | Inductive(v,branches) ->
   | Case(l,e,lt,branches,default) ->
   | Cons(lt,sym) ->
   | Constructor ->
*)




(* Here is the default pass function :
let rec pass ulexp = match ulexp with
  | Imm(sexp) ->
  | Sort(l,s) ->
  | Arrow ((l,v),l,e) ->
  | Var(l,v) ->
  | Lambda(v,e) ->
  | Let(l,decls, body) ->
  | Letrec(l,decls, body) ->
  | Call(f,args) ->
  | Inductive(v,branches) ->
  | Case(l,e,lt,branches,default) ->
  | Cons(lt,sym) ->
  | Constructor ->
*)


(* Normally types don't appear in Ulexp, but in case they're passed
 * explicitly to a function, just represent them with a random constant.
 * The code can't do anything with them anyway.  *)
let arrow_var = L.mkvar "arrow"
let arrow l = Inductive ((l, arrow_var), SMap.empty)


(** Building Ulexp ************************************************************)

let rec from_lexp lexp = match lexp with
  | L.Imm sexp -> Imm sexp
  | L.Var (l,v) -> Var(l,v)
  | L.Let (l,decls,body) ->
      let convert_declaration (v,e,_) = (v, from_lexp e) in
      Letrec(l, List.map convert_declaration decls, from_lexp body)
  | L.Lambda (Aerasable,_,_,e) -> from_lexp e
  | L.Lambda (_,v,_,e) -> Function([v],from_lexp e)
  | L.Call (f,args) ->
      let not_erasable (ak,_) = not (ak = Aerasable) in
      let throw_erasable args = List.map (fun x -> from_lexp (snd x))
                                         (List.filter not_erasable args) in
      let rec has_nonerasable = function
        | [(Aerasable,_)]   -> false
        | (Aerasable,_)::xs -> false
        | x::xs             -> has_nonerasable xs
        | []                -> true (* match empty call *) in
      if has_nonerasable args then
        Call(from_lexp f, throw_erasable args)
      else from_lexp f
  | L.Inductive (v,_,branches) -> Inductive(v,branches)
  | L.Cons (ltype,symbol) -> Cons(ltype,symbol)
  | L.Case (l,e,ltype,branches,default_exp) ->
      let not_erasable (ak,_)= not (ak = Aerasable) in
      let throw_erasable x = List.map snd (List.filter not_erasable x) in
      let convert_branches =
        SMap.map (fun (l,args,exp)-> (l, throw_erasable args, from_lexp exp))
      and convert_default = function
        | Some exp -> Some(from_lexp exp)
        | None -> None in
      Case(l, from_lexp e, ltype, convert_branches branches,
           convert_default default_exp)
  | L.Arrow(_,varo,ltype,l,lexp) -> arrow l
  | L.Metavar (_, _, r)
    -> (match !r with
       | L.MetaSet e -> from_lexp e
       | L.MetaUnset _ -> internal_error "Unset metavar in Ulexp.from_lexp")
  | L.Susp (s, e) -> from_lexp (L.lexp_whnf s e)
  | L.Sort _ -> internal_error "Unerasable Sort in Ulexp.from_lexp"






(** Code analysis pass ********************************************************)



type varinfo = { count: int; expression: ulexp option; freevars: VSet.t;
                 recursive: bool; inline: bool}
 and environment = varinfo VMap.t



(*
let rec freevars ulexp =
  let rec freevars' acc ulexp = match ulexp with
    | Var(_,v) -> VSet.add v acc
    | Let((_,v),e, body)
      -> VSet.union (freevars e)
                   (VSet.remove v (freevars body))
    | Letrec (_,decls, body) -> (* FIXME mutually recursive *)
        let arg_freevars acc ((_,v),e) =
          VSet.union acc (freevars e) in
        let inner_freevars = List.fold_left
          arg_freevars (VSet.union acc (freevars body)) decls in
        let remove_declared freevars =  List.fold_left
          (fun acc ((_,v),_) -> VSet.remove v acc) freevars decls in
        remove_declared inner_freevars

    | Lambda((_,v),e) -> VSet.remove v (freevars e)
    | Call(f,args) -> List.fold_left
                        (fun acc e -> VSet.union acc (freevars e))
                        (freevars f)
                        args
    | Inductive((_,v),branches) ->  (* FIXME consider v as a variable *)
        VSet.remove v (List.fold_left
          (fun acc (_,e) -> VSet.union (freevars e) acc)
          VSet.empty
          (SMap.bindings branches))
    | Case(_,e,lt,branches,default_exp) ->
        let branches_vars (_,args,e) = List.fold_left
                                           (fun acc (_,v) -> VSet.remove v acc)
                                           (freevars e)
                                           args
        in
        List.fold_left
          (fun acc (k,branches) -> VSet.union acc (branches_vars branches))
          (match default_exp with
             | Some(exp) -> VSet.union (freevars e) (freevars exp)
             | _ -> freevars e)
          (SMap.bindings branches)
    | Cons(lt,_) -> VSet.empty
    | _ -> VSet.empty
  in freevars' VSet.empty ulexp    *)




(*
let freevars ulexp =
  let recursive = true in
  let add_var freevar vset vmap =
    VSet.fold
     (fun e a -> let freevars = try VMap.find e vmap
                                with Not_found -> VSet.empty
      in VMap.add v (Vset.add freevar freevars) vmap)
     vset vmap
  in
  let rec add_var_forall freevar vlist vmap = match vlist with
    | [] -> vmap
    | (x,r)::xs ->
       if VSet.mem freevar x
        if r = recursive
         then vmap
         else add_var freevar  vmap
        else add_var_forall v xs (add_var v x vmap)
  in
  let merge = VMap.merge (fun (Some(v1),Some(v2)) ->
                            | (Some(v1),None)     ->
                            | (None,Some(v2))     ->
                            | (None,None)         ->  ) in
  let freevars' vdeclared vmap ulexp = match ulexp with
    | Var(_,v) -> add_var_forall v vdeclared ulexp
    | Let(_,decls, body) ->
       let vset, new_vmap = List.fold_left
          (fun (set,map) ((l,v),e)-> (VSet.add v set,
                                      freevars' vdeclared map e))
          (VSet.empty, vmap)
          decls
       in
       let new_vlist = vset::vdeclared in
       freevars' new_vlist new_vmap body
    | Letrec (_,decls, body) ->
       let vset = List.fold_left
          (fun set ((_,v),_)-> VSet.add v set)
          VSet.empty
          decls
       in
       let new_vlist = vset::vdeclared in
       let new_vmap = List.fold_left
          (fun map (_,e)-> freevars' new_vlist map e)
          vmap
          decls
       in
       freevars' new_vlist new_vmap body
    | Lambda((_,v),e) ->
        freevars' ((VSet.singleton v,not recursive)::vdeclared) vmap ulexp
    | Call(f,args) ->
    | Inductive((_,v),branches) ->
    | Case(_,e,lt,branches,default_exp) ->
    | Cons(lt,_) ->
    | _ ->
  in freevars' [] VMap.empty ulexp
*)




let freevars ulexp =
  let remove_freevars v (freevars,record) = (VSet.remove v freevars, record) in
  let merge_record =
    VMap.merge (fun k a b -> match a,b with
                  | Some(v1),Some(v2) -> Some(VSet.union v1 v2)
                  | Some(v1),None     -> Some(v1)
                  | None,Some(v2)     -> Some(v2)
                  | None,None         -> None) in
  let merge_result (a,b) (c,d) = (VSet.union a c, merge_record b d) in
  let rec freevars' ulexp = match ulexp with
  | Imm(_) (* | Sort(_,_) | Arrow (_,_,_) *) -> (VSet.empty, VMap.empty)
  | Var(_,v) -> (VSet.singleton v, VMap.empty)
  | Function(args,e)
    -> List.fold_right
        remove_freevars
        (List.map snd args)
        (freevars' e)
  | Let((_,v), exp, body)
    -> let (efree, erec) = freevars' exp in
      let (bfree, brec) = freevars' body in
      (VSet.union efree (VSet.remove v bfree),
       merge_record erec brec)
  | Letrec(l, decls, body) ->
     let declared_var = List.fold_left (fun acc ((_,v),e) -> v::acc) [] decls in
     List.fold_left
       (fun acc v -> remove_freevars v acc)
       (List.fold_left
         (fun  (freevars,record) ((_,v),e) ->
           let (new_freevars,new_record) = freevars' e in
           (VSet.union freevars new_freevars,
            VMap.add v new_freevars (merge_record record new_record)))
         (freevars' body)
         decls)
       declared_var
  | Call(f,args) ->
      List.fold_left
      (fun  (freevars,record) e ->
        let (new_freevars,new_record) = freevars' e in
        (VSet.union freevars new_freevars, merge_record record new_record)
      )
      (freevars' f)
      args
  (* A U.Inductive really is like a union+struct in C, i.e. it has no run-time
   * content and hence no free variable.  *)
  | Inductive((_,v),branches) -> (VSet.empty, VMap.empty)
  | Case(l,e,lt,branches,default) ->
      let branches_vars (_,args,e) =
        List.fold_left
         (fun (freevars,record) (_,v) -> (VSet.remove v freevars, record))
         (freevars' e)
         args
      in
      List.fold_left
        (fun acc (k,branches) ->
           merge_result acc (branches_vars branches))
        (match default with
           | Some(exp) -> merge_result (freevars' e) (freevars' exp)
           | None -> freevars' e)
        (SMap.bindings branches)

  | Cons(lt,sym) -> (VSet.empty, VMap.empty)
  in
  snd (freevars' ulexp)




let usage_count ulexp =
  let get_count v record = try VMap.find v record with Not_found -> 0 in
  let rec usage_count' record ulexp = match ulexp with
   | Imm(_) (* | Sort(_,_) *) -> record
   | Var(l,v) -> VMap.add v (1+(get_count v record)) record
   | Function(args,e) -> usage_count' record e
   | Let((_,v), exp, body)
     -> usage_count' (usage_count' record exp) body
   | Letrec(l,decls, body) ->
       List.fold_left (fun acc (_,e) -> usage_count' acc e)
                      (usage_count' record body)
                      decls
   | Call(f,args) -> List.fold_left usage_count' (usage_count' record f) args
   (* A U.Inductive really is like a union+struct in C, i.e. it has no run-time
    * content and hence no free variable.  *)
   | Inductive(v,branches) -> record
   | Case(l,e,lt,branches,default) ->
       SMap.fold
        (fun k (_,_,e) acc -> usage_count' acc e)
        branches
        (match default with
          | None -> (usage_count' record e)
          | Some(d) -> (usage_count' (usage_count' record e) d))
   | Cons(lt,sym) -> record
  in usage_count' VMap.empty ulexp




(* Removes dead variable declaration *)
let dead ulexp var_count =
  let is_alive v exp =
    let use_count = try (VMap.find v var_count) with Not_found -> 0 in
    (* FIXME: What is this for?  Recursive defs?  *)
    ((try (VMap.find v (usage_count exp)) with Not_found -> 0) < use_count)
    (* FIXME: This shouldn't be needed, because we should count references
     * to Inductive.  *)
    || (match exp with Inductive(_,_) -> true | _ -> false)
  in
  let rec dead' ulexp = match ulexp with
   | Imm(_) (* | Sort(_,_) *) | Var(_,_) -> ulexp
   | Function(args, e) -> Function(args, dead' e)
   | Let((l,v), exp, body)
     -> if is_alive v exp
       then Let((l,v), dead' exp, dead' body)
       else dead' body
   | Letrec(l,decls, body) ->
      (match List.filter (fun ((_,v),e) -> is_alive v e) decls with
       | [] -> dead' body
       | new_decls -> Letrec(l, new_decls, dead' body))
   | Call(f,args) -> Call(dead' f, List.map dead' args)
   | Case(l,e,lt,branches,Some(default)) ->
       Case(l,dead' e,lt, SMap.map (fun (l,v,e) -> (l,v,dead' e)) branches,
            Some(dead' default))
   | Case(l,e,lt,branches,None) ->
       Case(l,dead' e,lt, SMap.map (fun (l,v,e) -> (l,v,dead' e)) branches,
            None)
   | Inductive(v,branches) -> ulexp
   | Cons(lt,sym) -> ulexp
  in dead' ulexp




let strongly_connected_components map =
  let vertices = List.map (fun (k,e) -> k) (VMap.bindings map)  in
  let edges = VMap.filter (fun k e -> not (e = VSet.empty)) map in

  let indexes = VMap.empty in
  let get_lowlink x map = snd (VMap.find x map) in
  let get_index x map = fst (VMap.find x map) in

  let rec link (v,w) (indexes,index,stack,components) =
    if VMap.exists (fun k a -> k = w) indexes && List.exists ((=) w) stack
    then
      (VMap.add v
               (index, min (get_lowlink v indexes) (get_index w indexes))
               indexes,
       index, stack, components)
    else
      let new_indexes,new_index,new_stack,new_components =
        strong_connect w (indexes,index,stack,components) in
      (VMap.add v
               (new_index, min (get_lowlink v new_indexes)
                               (get_lowlink w new_indexes))
               new_indexes,
        new_index, new_stack, new_components)
  and strong_connect v (indexes,index,stack,components) =
    let rec create_component stack v component =
      (match stack with
        | [] -> ([], component)
        | [x] -> ([], VSet.add x component)
        | x::xs -> if x = v then (xs, VSet.add x component)
                            else create_component xs v (VSet.add x component))
    in
    let new_indexes,new_index,new_stack,new_components =
      VSet.fold (fun w acc -> link (v,w) acc)
               (try VMap.find v edges with Not_found -> VSet.empty)
               (VMap.add v (index,index) indexes, index+1, v::stack, components)
    in
    if let (v_index, v_lowlink) = VMap.find v new_indexes in v_index = v_lowlink
    then
      let (stack,comp) = create_component new_stack v VSet.empty
      in (new_indexes,new_index,stack,SCC.add comp new_components)
    else (new_indexes,new_index,new_stack,new_components)
  in
  let _,_,_,scc = (List.fold_left
                    (fun acc v -> if VMap.exists (fun k a -> a = v) indexes
                                  then acc
                                  else strong_connect v acc)
                    (VMap.empty,0,[],SCC.empty)
                    vertices)
  in scc




let get_component v ssc =
  SCC.min_elt (SCC.filter (fun component -> VSet.exists ((=) v) component) ssc)




(** Proprieties Test **)
  let is_recursive v scc freevars =
    (* If it has itself as a freevar or if it is part of a component bigger than
       1 in size. *)
    try (VSet.mem v (VMap.find v freevars))
     || ((VSet.cardinal (get_component v scc)) > 1)
    with Not_found -> false





(*

(* explode: Explodes untyped lambda expressions having multiple arguments     *)
(* constructs (such as let expressions and function calls) into nested        *)
(* expressions that are better suited for optimisation.                       *)
(* Operations done in this step preserve the environment                      *)
let rec explode env ulexp = match ulexp with
  (* Subject to explosion and propagation *)
  | Letrec(l,decls, body) ->
      let extract_non_recursive declarations =
        let declared_variable =
          List.fold_left
            (fun acc ((_,v),_) -> VSet.add v acc)
            VSet.empty
            decls in
        let rec extract_non_recursive' declarations recursive_declarations =
          match declarations, recursive_declarations with
          | [], x::xs -> Letrec(l,recursive_declarations,body)
          | [((l,v),exp) as decl], []  ->
              let varinfo = try Some(VMap.find v env)
               with Not_found -> None (* Should not happen *) in
              (match varinfo with
                 | Some(varinfo) ->
                    if VSet.mem v varinfo.freevars || (match varinfo.expression with
                      | Some (Cons(_,_)) -> true
                      | _ -> false)
                    then Letrec(l,[decl],body)
                    else Let((l,v),exp,body)
                 | None -> Letrec(l,[decl],body))
          | (((l,v),exp) as decl)::rest, _ ->
             (* FIXME: Code duplication with previous case!  *)
             let varinfo = try Some(VMap.find v env)
               with Not_found -> None (* Should not happen *) in
             (match varinfo with
                | Some(varinfo) ->
                   if VSet.is_empty (VSet.inter varinfo.freevars
                                                declared_variable) ||
                      (match varinfo.expression with
                     | Some (Cons(_,_)) -> false
                     | _ -> true)
                   then
                     Let(l, [decl], extract_non_recursive'
                                      rest
                                      recursive_declarations)
                   else
                     extract_non_recursive' rest (decl::recursive_declarations)
                | None -> Letrec(l,[decl],body))
          (*   (try
              let ((_,v),_) = decl in
              if VSet.is_empty (VSet.inter (VMap.find v env).freevars
                                           declared_variable)
              then Let(l, [decl], extract_non_recursive' rest recursive_declarations)
              else extract_non_recursive' rest (decl::recursive_declarations)
             with Not_found -> Letrec(l,recursive_declarations,body)) (* Should not happen *)*)
          | [], [] -> raise Parse_error (* Should not happen *) in
        extract_non_recursive' declarations [] in
      extract_non_recursive decls
  | Call(f,args) -> List.fold_left (fun acc arg-> Call(acc, [explode env arg]))
                                   (explode env f)
                                   args
  (* Propagate-only *)
  | Lambda(v,e) -> Lambda(v, explode env e)
  | Inductive(v,branches) -> Inductive (v, SMap.map (explode env) branches)

  | Case(l,e,lt,branches,Some(default_exp)) ->
      Case(l,e,lt,
      SMap.map (fun (l,v,e) -> (l,v,explode env e)) branches,
      Some(explode env default_exp))
  | Case(l,e,lt,branches,None) ->
      Case(l,e,lt,
      SMap.map (fun (l,v,e) -> (l,v,explode env e)) branches,
      None)
  | _ -> ulexp

*)




(* explode: Explodes untyped lambda expressions having multiple arguments     *)
(* constructs (such as let expressions and function calls) into nested        *)
(* expressions that are better suited for optimisation.                       *)
(* Operations done in this step preserve the environment                      *)
let rec explode freevars scc ulexp = match ulexp with
  (* Subject to explosion and propagation *)
  | Letrec(l,decls, body) ->
      let rec extract_non_recursive (recur,non_recur) ((l,v),e) =
        if is_recursive v scc freevars
          then (((l,v),e)::recur, non_recur)
          else (recur, ((l,v),e)::non_recur)
      in
      let rec create_let x = match x with
        | ([],[])           -> body
        | ([],(v,exp)::nrs) -> Let(v, exp, create_let ([], nrs))
        | (recur,nrs)       -> Letrec(l, recur, create_let ([],nrs))
      in
      create_let (List.fold_left extract_non_recursive ([],[]) decls)
  | Let(v, exp, body)
    -> Let (v, explode freevars scc exp, explode freevars scc body)
  | Call(f,args) -> List.fold_left (fun acc arg->
                                      Call(acc, [explode freevars scc arg]))
                                   (explode freevars scc f)
                                   args
  (* Propagate-only *)
  | Function(args,e) -> Function(args, explode freevars scc e)
  | Case(l,e,lt,branches,Some(default_exp)) ->
      Case(l,e,lt,
      SMap.map (fun (l,v,e) -> (l,v,explode freevars scc e)) branches,
      Some(explode freevars scc default_exp))
  | Case(l,e,lt,branches,None) ->
      Case(l,e,lt,
      SMap.map (fun (l,v,e) -> (l,v,explode freevars scc e)) branches,
      None)
  | (Cons (_, _)|Var _|Imm _|Inductive _)
    -> ulexp                     (* Don't bother for now.  *)











let inline freevars scc var_count ulexp =
  let is_inlinable v record =
    (try (VMap.find v var_count) = 1 with Not_found -> true)
     && (not (is_recursive v scc freevars))
     && (VMap.mem v record)
    in




  let rec inline' record ulexp =
   match ulexp with
    | Var(l,v) -> if is_inlinable v record
                   then VMap.find v record
                   else ulexp
    | Let((l,v), exp, body) ->
        Let((l,v),
            inline' record exp,
            inline' (VMap.add v exp record) body)
    | Letrec(l,decls,body) ->
        let new_record = List.fold_left (fun acc ((_,v),e) -> VMap.add v e acc)
                                        record
                                        decls
        in
        Letrec(l,
               List.map (fun (v,e) -> (v,inline' record e)) decls,
               inline' new_record body)
    | Function(args,e) -> Function(args, (*inline' record*) e)
    | Call(f,args) -> Call(inline' record f, List.map (inline' record) args)
    | Case(l,e,lt,branches,Some(default_exp)) ->
        Case(l,inline' record e,lt,
             SMap.map (fun (l,v,e) -> (l,v,inline' record e)) branches,
             Some(inline' record default_exp))
    | Case(l,e,lt,branches,None) ->
        Case(l,inline' record e,lt,
            SMap.map (fun (l,v,e) -> (l,v,inline' record e)) branches,
            None)
    | (Cons (_, _)|Imm _|Inductive _) -> ulexp (* Don't bother.  *)
  in inline' VMap.empty ulexp









(** Optimisation pass *********************************************************)


let optimisation_pass ulexp =
  let var_count = usage_count ulexp in
  let freevars = freevars ulexp in
  let scc = strongly_connected_components freevars in
  let exploded = explode freevars scc ulexp in

  let inlined = inline freevars scc var_count exploded in
  let new_var_count  = usage_count inlined in
  dead inlined new_var_count











(*
let rec inline env ulexp =
  let is_inlinable vinfo = vinfo.inline ||
    ((vinfo.count = 1) && (not vinfo.recursive)) || vinfo.count = 0 in
  match ulexp with
  | Var(l,v) -> (try
      let vinfo = VMap.find v env in
      match vinfo.expression with
        Some e when is_inlinable vinfo -> e
      | _ -> ulexp
      with Not_found -> ulexp)
  | Let((l,v),e,body)
    -> if is_inlinable (VMap.find v env)
      (* FIXME: Here, we assume that `inline' will indeed get rid of
       * all uses of `v'.  Better would be to check after-the-fact.  *)
      then inline env body
      else Let((l,v), inline env e, inline env body)
  | Letrec(l,decls,body) ->
      let throw_inlinable ((_,v),_) =
        try not (is_inlinable (VMap.find v env)) with Not_found -> true in
      (match List.filter throw_inlinable decls with
        | [] -> inline env body
        | x -> Let(l,
                   List.map (fun (v,e) -> (v,inline env e)) x,
                   inline env body))
  | Letrec(l,decls,body) ->
      let throw_inlinable ((_,v),_) =
        try not (is_inlinable (VMap.find v env)) with Not_found -> true in
      (match List.filter throw_inlinable decls with
        | [] -> inline env body
        | x -> Letrec(l,
                      List.map (fun (v,e) -> (v,inline env e)) x,
                      inline env body))
  | Lambda((l,v),e) -> (try
      let vinfo = VMap.find v env in
        if is_inlinable vinfo
        then inline env e
        else Lambda((l,v), inline env e)
      with Not_found -> Lambda((l,v), inline env e))
  | Call(f,args) -> Call(inline env f, List.map (inline env) args)
  | Inductive(v,branches) -> Inductive (v, SMap.map (inline env) branches)

  | Case(l,e,lt,branches,Some(default_exp)) ->
      Case(l,inline env e,lt,
        SMap.map (fun (l,v,e) -> (l,v,inline env e)) branches,
        Some(inline env default_exp))

  | Case(l,e,lt,branches,None) ->
      Case(l,inline env e,lt,
        SMap.map (fun (l,v,e) -> (l,v,inline env e)) branches,
        None)

  | _ -> ulexp

*)








(** PRINT FUNCTIONS ***********************************************************)
let rec pretty_print printer ulexp =
  let rec join s_printer c s = match s with
    | [s]   -> s_printer s
    | s::xs -> s_printer s;
               printer c
    | [] -> () in
  match ulexp with
  | Imm(s) -> printer (sexp_to_str s)
  | Var(_,v) -> printer (L.varname v)
  | Let((_,v),e,body)
    -> printer (L.varname v);
      printer " := ";
      pretty_print printer e;
      printer "\n";
      pretty_print printer body
  | Letrec(_,(args),e) ->
      let print_definition ((_,v),e) = begin
        printer (L.varname v);
        printer " ::= ";
        pretty_print printer e;
        printer "\n"
      end in
      List.iter print_definition args;
      pretty_print printer e
  | Function(args,e) ->
      printer "λ[";
      join (fun (_,v) -> printer (L.varname v)) "," args;
      printer "].";
      pretty_print printer e
  | Call(f,args) ->
      pretty_print printer f;
      printer "(";
      join (pretty_print printer) " " args;
      printer ")"
  | Inductive((_,v),emap) ->
      printer "(Inductive ";
      printer (L.varname v);
      (* printer " (";
       * join (fun (k,e) -> pretty_print printer e) " "
       *   (SMap.bindings emap);
       * printer "))" *)
  | Cons(lt,(_,name)) ->
      printer (sexp_to_str (pexp_unparse (L.lexp_unparse lt)));
      printer ".";
      printer name
  | Case(_,e,t,branches,default) ->
      let print_varname (_,v) = printer (" " ^ (L.varname  v)) in
      let print_branch (k,(_,args,e)) = begin
        printer "  | ";
        printer k;
        List.iter  print_varname args;
        printer " -> ";
        pretty_print printer e;
        printer "\n"
      end in
      pretty_print printer e;
      printer " :\n";
      List.iter print_branch (SMap.bindings branches)




(* let rec print_rec printer ulexp =
 *   let print_rec' = print_rec printer in
 *   match ulexp with
 *   | Imm(_) | Var(_,_) -> printer ulexp
 *   | Let(_,e,body) ->
 *       printer ulexp;
 *       print_rec' e;
 *       print_rec' body
 *   | Letrec(_,(args),e) ->
 *       printer ulexp;
 *       List.iter (fun (_,e) -> print_rec' e) args;
 *       print_rec printer e
 *   | Call(f,args) ->
 *       printer ulexp;
 *       print_rec printer f;
 *       List.iter (print_rec') args
 *   | Inductive((_,v),emap) ->
 *       printer ulexp;
 *       List.iter (fun (_,e) -> print_rec' e) (SMap.bindings emap)
 *   | Case(_,e,t,branches,default) ->
 *       printer ulexp;
 *       print_rec printer e;
 *       List.iter (fun (_,(_,_,e)) -> print_rec' e) (SMap.bindings branches);
 *       (match default with Some(e) -> print_rec printer e | None -> ()) *)



(*
let print_debug printer ulexp =
  let print_freevar v = begin
    printer " ";
    printer (L.varname v);
    printer ":";
    printer (string_of_int v);
    printer " ";
  end in
  printer "-------------------------------------------------------------------------- Ulexp \n";
  pretty_print printer ulexp;
  printer "\n FREEVARS: ";
  VSet.iter print_freevar (freevars ulexp);
  printer "\n\n"
*)


let print_freevars freev =
  print_string "\n\nFREEVARS:\n";

  VMap.iter (fun k vars -> print_string (L.varname k);
                        print_string ": ";
                        VSet.iter (fun v -> print_string (L.varname k);
                                            print_string " ") vars;
                        print_string "\n"
            )
            freev



(*
let print_environment printer env =
  let print_freevar var = printer ((L.varname var) ^ ":" ^ (string_of_int var)) in
  let rec print_freevars set =
    if set = VSet.empty
      then printer "_"
      else VSet.iter (fun x -> print_freevar x;printer " ") set in
  VMap.iter
    (fun  k varinfo ->
      printer "\n\n+++++++++++++++++++++++++++++++++++++++++++++++++ Expression ++\n";
      (match varinfo.expression with
       | None -> printer "Unknown-value";
       | Some e -> pretty_print printer e);
      printer "\n";
      printer (L.varname k);
      printer ": {count = ";
      printer (string_of_int varinfo.count);
      printer "; freevars = ";
      print_freevars varinfo.freevars;
      printer "; inlinable = ";
      printer (string_of_bool varinfo.inline);
      printer "; rec = ";
      printer (string_of_bool varinfo.recursive);
      printer "};")
     env*)

(*
let print_freevars_analysis ulexp =
  print_environment print_string (make_environment ulexp)
  (*print_rec (print_debug print_string)*)
*)



let print_scc ulexp =
  print_string "\n\nStrongly Connected Components\n";
  SCC.iter (fun component ->
       VSet.iter (fun v-> print_string (L.varname v);
                          print_string "<-->") component;
       print_string "\n"
    )
    (strongly_connected_components (freevars ulexp));
  print_string "\n\n"
