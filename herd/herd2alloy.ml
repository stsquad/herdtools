(*********************************************************************)
(*                        Herd                                       *)
(*                                                                   *)
(* Luc Maranget, INRIA Paris-Rocquencourt, France.                   *)
(* Jade Alglave, University College London, UK.                      *)
(* John Wickerson, Imperial College London, UK.                      *)
(*                                                                   *)
(*  Copyright 2013 Institut National de Recherche en Informatique et *)
(*  en Automatique and the authors. All rights reserved.             *)
(*  This file is distributed  under the terms of the Lesser GNU      *)
(*  General Public License.                                          *)
(*********************************************************************)


open AST
open Printf

let with_sc = ref false

let in_ignore_section = ref false 

let rec fprintf_iter s f chan = function
  | [] -> ()
  | [x] -> fprintf chan "%a" f x
  | x::xs -> fprintf chan "%a%s%a" f x s (fprintf_iter s f) xs
       
let rec fprintf_list s f chan = function
  | [] -> ()
  | [x] -> fprintf chan "%a" f x
  | x::xs -> fprintf chan "(%s %a %a)" s f x (fprintf_list s f) xs

let rec fprintf_list_infix s f chan = function
  | [] -> ()
  | [x] -> fprintf chan "%a" f x
  | x::xs -> 
    fprintf chan "(%a %s %a)" 
      f x s (fprintf_list_infix s f) xs

let alloy_of_konst chan = function
  | Empty SET -> fprintf chan "emps"
  | Empty RLN -> fprintf chan "empr"

let alloy_of_dir = function
  | Write -> "x.W"
  | Read -> "x.R"
  | WriteRead -> "x.(W&R)"
  | Atomic -> "x.A"
  | Plain -> "x.(ev-A)"
  | Unv_Set -> "x.ev"
		 
let rec alloy_of_op2 args chan es = function
  | Union -> fprintf_list_infix "+" (alloy_of_exp args) chan es
  | Inter -> fprintf_list_infix "&" (alloy_of_exp args) chan es
  | Diff -> fprintf_list_infix "-" (alloy_of_exp args) chan es
  | Seq -> fprintf_list_infix "." (alloy_of_exp args) chan es
  | Cartesian -> fprintf_list_infix "->" (alloy_of_exp args) chan es
  | _ -> Warn.fatal "alloy_of_op2"

and alloy_of_op1 args chan e = function
  | Plus -> fprintf chan "(^%a)" (alloy_of_exp args) e
  | Star -> fprintf chan "(*%a)" (alloy_of_exp args) e
  | Opt -> fprintf chan "(rc[%a])" (alloy_of_exp args) e
  | Select (d1,d2) -> fprintf chan "((%s -> %s) & %a)" (alloy_of_dir d1) (alloy_of_dir d2) (alloy_of_exp args) e 
  | Inv -> fprintf chan "(~%a)" (alloy_of_exp args) e
  | Square -> fprintf chan "(%a -> %a)" (alloy_of_exp args) e (alloy_of_exp args) e
  | Ext -> fprintf chan "(%a - x.thd)" (alloy_of_exp args) e
  | Int -> fprintf chan "(%a & x.thd)" (alloy_of_exp args) e
  | NoId -> fprintf chan "(%a - iden)" (alloy_of_exp args) e
  | Set_to_rln -> fprintf chan "(stor[%a])" (alloy_of_exp args) e
  | Comp SET -> fprintf chan "(x.ev - %a)" (alloy_of_exp args) e
  | Comp RLN -> fprintf chan "((x.ev -> x.ev) - %a)" (alloy_of_exp args) e
  | _ -> Warn.fatal "Unknown operator in herd2alloy"
and alloy_of_var args chan x = 
  match x with
  | "asw" | "lo" | "addr" | "data" | "acq" | "rel"
  | "sc" | "R" | "W" | "F" | "A" | "con"
	-> fprintf chan "(x.%s)" x
  | "thd" | "loc" -> fprintf chan "(rc[x.%s])" x
  | "rf" -> fprintf chan "rf"
  | "rfe" -> fprintf chan "(rf - x.thd)"
  | "po-loc" -> fprintf chan "(^(x.sb) & rc[x.loc])"
  | "nonatomicloc" -> fprintf chan "(x.naL)"
  | "MFENCE" -> fprintf chan "(x.F)"
  | "co" -> fprintf chan "^co"
  | "po" | "sb" -> fprintf chan "^(x.sb)"
  | "S" -> fprintf chan "^s"
  | "I" -> fprintf chan "I"
  | "M" | "_" -> fprintf chan "x.ev"
  | "id" -> fprintf chan "iden"
  | "fr" -> fprintf chan "(fr[x,rf,co])"
  | _ -> 
    let x = Str.global_replace (Str.regexp_string "-") "_" x in
    if List.mem x args then
      fprintf chan "%s" x
    else
      fprintf chan "(%s[x,rf,co%s])" x (if !with_sc then ",s" else "")

and alloy_of_exp args chan = function
  | Konst (_,k) -> alloy_of_konst chan k
  | Var (_,x) -> alloy_of_var args chan x
  | Op1 (_,op1, e) -> alloy_of_op1 args chan e op1
  | Op (_,op2, es) -> alloy_of_op2 args chan es op2
  | App (_,_,_) -> fprintf chan "Functions not done yet"
  | Bind _ -> fprintf chan "Bindings not done yet"
  | BindRec _ -> fprintf chan "Recursive bindings not done yet"
  | Fun _ -> fprintf chan "Local functions not done yet"
  | _ -> Warn.fatal "explicitset/match/tag etc. in herd2alloy"


and alloy_of_binding chan (x, e) = 
  match e with
  | Fun (_,_,_,_,_) ->
     fprintf chan "Functions not done yet"
  | _ ->
     if x = "alloy_ignore_section_begin" then
       in_ignore_section := true
     else if x = "alloy_ignore_section_end" then
       in_ignore_section := false
     else if not !in_ignore_section then
       fprintf chan "(y.%s) = %a\n\n" 
               x 
               (alloy_of_exp []) e

and alloy_of_binding' chan (x, e) = 
  match e with
  | Fun (_,_,_,_,_) ->
     fprintf chan "Functions not done yet"
  | _ ->
     if x = "alloy_ignore_section_begin" then
       in_ignore_section := true
     else if x = "alloy_ignore_section_end" then
       in_ignore_section := false
     else if not !in_ignore_section then
       fprintf chan "fun %s[x : BasicExec, rf : E -> E, co : E -> E%s] : E -> E {\n  %a\n}\n\n" 
               x
	       (if !with_sc then ", s : E -> E" else "")
               (alloy_of_exp []) e

let fprintf_so x chan so = 
  fprintf chan "%s" (match so with
    | None -> x
    | Some s -> s)

let alloy_of_test = function
  | Acyclic -> "acyclic"
  | Irreflexive -> "irreflexive"
  | TestEmpty -> "is_empty"

let provides : string list ref = ref []
let requires : string list ref = ref []
let seen_requires_clause : bool ref = ref false
	   
let find_derived_relations prog =
  List.concat
    (List.map
       (function
	 | Let (_,b) -> List.map fst b
	 | _ -> [])
       prog)
					  
let print_derived_relations chan = function
  | Let (_,bs) -> List.iter (alloy_of_binding chan) bs
  | _ -> ()

let print_derived_relations' chan = function
  | Let (_,bs) -> List.iter (alloy_of_binding' chan) bs
  | _ -> ()

let print_predicates chan = function
  | Test (_,_, test, exp, name, test_type) ->
    let name = begin match name with 
        | None -> Warn.user_error "You need to give each constraint a name!"
        | Some name -> name 
 	       end
    in
    fprintf chan "pred %s[x : BasicExec, rf : E -> E, co : E -> E%s] {\n  %s[%a]\n}\n\n" 
	    name
	    (if !with_sc then ", s : E -> E" else "")
	    (alloy_of_test test)
	    (alloy_of_exp []) exp;
    begin match test_type with
    | Provides -> 
       if (!seen_requires_clause) then
	 Warn.user_error "Provides-clause follows requires-clause!";
       provides := name :: (!provides)
    | Requires ->
       seen_requires_clause := true;
       requires := name :: (!requires)
    end

  | _ -> ()
					  
let alloy_of_ins chan = function
  | Let (_,bs) -> List.iter (alloy_of_binding chan) bs
  | Test (_,_, test, exp, name, test_type) ->
    let name = begin match name with 
        | None -> Warn.user_error "You need to give each constraint a name!\n"
        | Some name -> name 
    end in
    (*fprintf chan "let %s X = %s [%a]" 
      name
      (alloy_of_test test)
      (alloy_of_exp []) exp;*)
    begin match test_type with
      | Provides -> 
        if (!seen_requires_clause) then
          Warn.user_error "Provides-clause follows requires-clause!";
        provides := name :: (!provides)
      | Requires -> 
        seen_requires_clause := true;
        requires := name :: (!requires)
    end
  | UnShow _ | Show _ | ShowAs _ | Latex _ -> ()
  | Include (_,file) ->
    let file = String.capitalize file in
    let file = String.sub file 0 (String.length file - 4) in
    provides := (sprintf "%s.provides_clauses" file) :: (!provides);
    requires := (sprintf "%s.requires_clauses" file) :: (!requires);
    fprintf chan "open import %s" file
  | ProcedureTest _ | Procedure _ | Call _ | Enum _ | Debug _
  | Foreach _ | ForOrder _ | Rec _ ->
      Warn.fatal "procedure/call/enum/debug/foreach in herd2alloy"

let alloy_of_prog chan (with_sc_arg:bool) prog =

  with_sc := with_sc_arg;
  
  List.iter (print_derived_relations' chan) prog;

  List.iter (print_predicates chan) prog;

  fprintf chan "pred consistent[x : BasicExec, rf : E -> E, co : E -> E] {\n      ";
  if !with_sc then
    fprintf chan "  some s : E -> E when ax_wfS[x,s] |\n      ";
  (*  fprintf chan "  some y : Extras | wf_Extras[x,y%s] &&\n    " (if !with_sc then ",s" else ""); *)
  fprintf_iter "\n    && " (fun chan s -> fprintf chan "%s[x,rf,co%s]" s (if !with_sc then ",s" else "")) chan (List.rev !provides);
  fprintf chan "\n}\n\n";

  fprintf chan "pred not_faulty[x : BasicExec, rf : E -> E, co : E -> E] {\n      ";
  fprintf_iter "\n    && " (fun chan s -> fprintf chan "%s[x,rf,co%s]" s (if !with_sc then ",none->none" else "")) chan (List.rev !requires);
  fprintf chan "\n}\n\n";
  
