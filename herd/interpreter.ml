(*********************************************************************)
(*                        Herd                                       *)
(*                                                                   *)
(* Luc Maranget, INRIA Paris-Rocquencourt, France.                   *)
(* Jade Alglave, University College London, UK.                      *)
(*                                                                   *)
(*  Copyright 2013 Institut National de Recherche en Informatique et *)
(*  en Automatique and the authors. All rights reserved.             *)
(*  This file is distributed  under the terms of the Lesser GNU      *)
(*  General Public License.                                          *)
(*********************************************************************)

(** Interpreter for a user-specified model *)

open Printf

module type S = sig
  
  module S : Sem.Semantics

(* Values *)
  module V : sig type env end

  val env_empty : V.env

(* Helpers, initialisation *)
val add_rels : V.env -> (string * S.event_rel Lazy.t) list -> V.env      
val add_sets : V.env -> (string * S.event_set Lazy.t) list -> V.env      

(* State of interpreter *)

  type st = { 
    env : V.env ;
    show : S.event_rel StringMap.t Lazy.t ;
    seen_requires_clause : bool ;
    skipped : StringSet.t ; 
  }

  val show_to_vbpp : 
    st -> (StringMap.key * S.event_rel) list

  val interpret : 
    (unit -> unit) -> (* function called when a requires clause fails *)
    S.test ->
    S.concrete ->
    V.env ->
    S.event_rel lazy_t ->
    (StringMap.key * S.event_rel) list Lazy.t ->
    st option
end


module type Config = sig
  val m : AST.pp_t
  include Model.Config
end

module Make
    (O:Config)
    (S:Sem.Semantics)
    (B:AllBarrier.S with type a = S.barrier)
    :
    (S with module S = S)
    =
  struct

(****************************)
(* Convenient abbreviations *)
(****************************)

    module S = S
    module A = S.A
    module E = S.E
    module U = MemUtils.Make(S)
    module MU = ModelUtils.Make(O)(S)
    module W = Warn.Make(O)
(*  Model interpret *)
    let (txt,(_,_,prog)) = O.m

(*
  let debug_proc chan p = fprintf chan "%i" p
  let debug_event chan e = fprintf chan "%s" (E.pp_eiid e)
  let debug_set chan s =
  output_char chan '{' ;
  E.EventSet.pp chan "," debug_event s ;
  output_char chan '}'

  let debug_events = debug_set

  let debug_rel chan r =
  E.EventRel.pp chan ","
  (fun chan (e1,e2) -> fprintf chan "%a -> %a"
  debug_event e1 debug_event e2)
  r
 *)

    module V = Ivalue.Make(S)

    let env_empty = StringMap.empty

    open V

(* Add values to env *)
  let add_rels m bds =
    List.fold_left
      (fun m (k,v) -> StringMap.add k (lazy (Rel (Lazy.force v))) m)
      m bds
    
  let add_sets m bds =
    List.fold_left
      (fun m (k,v) -> StringMap.add k (lazy (Set (Lazy.force v))) m)
      m bds



    type st = { 
        env : env ;
        show : S.event_rel StringMap.t Lazy.t ;
        seen_requires_clause : bool ;
        skipped : StringSet.t ; 
      }

    let error loc msg =
      eprintf "%a: %s\n" TxtLoc.pp loc msg ;
      raise Misc.Exit (* Silent failure *)

    let find_env env k =
      Lazy.force begin
	try StringMap.find k env
	with
	| Not_found -> Warn.user_error "unbound var: %s" k
      end

    let find_env_loc loc env k =
      try  find_env env k
      with Misc.UserError msg -> error loc msg

    let is_rel = function
      | Rel _ -> true
      | _ -> false

    let is_set = function
      | Set _ -> true
      | _ -> false

    let as_rel = function
      | Rel r -> r
      | _ ->  assert false

    let as_set = function
      | Set s -> s
      | _ -> assert false


    let rec stabilised vs ws = match vs,ws with
    | [],[] -> true
    | v::vs,w::ws ->
        E.EventRel.subset w v && stabilised vs ws
    | _,_ -> assert false

    open AST

(* Get an expression location *)
    let get_loc = function
      | Konst (loc,_)
      | Var (loc,_)
      | Op1 (loc,_,_)
      | Op (loc,_,_)
      | Bind (loc,_,_)
      | BindRec (loc,_,_)
      | App (loc,_,_)
      | Fun (loc,_,_) -> loc


(* State of interpreter *)

    let rt_loc lbl =
      if
        O.verbose <= 1 &&
        not (StringSet.mem lbl S.O.PC.symetric) &&
        not (StringSet.mem lbl S.O.PC.showraw)
      then S.rt else (fun x -> x)

    let show_to_vbpp st =
      StringMap.fold (fun tag v k -> (tag,v)::k)   (Lazy.force st.show) []

    let empty_rel = Rel E.EventRel.empty
    let empty_set = Set E.EventSet.empty        

    let interpret failed_requires_clause test conc m id vb_pp =

      let is_dir = function
          (* Todo: are these still needed? *)
	| Unv_Set -> (fun _ -> true)
	| Bar_Set -> E.is_barrier
        | WriteRead -> E.is_mem
        | Write -> E.is_mem_store
        | Read -> E.is_mem_load
        | Atomic -> E.is_atomic
        | Plain -> fun e -> not (E.is_atomic e) in

      let rec eval env = function
        | Konst (_,Empty RLN) -> empty_rel
        | Konst (_,Empty SET) -> empty_set
        | Var (loc,k) -> find_env_loc loc env k
        | Fun (_,xs,body) ->
            Clo {clo_args=xs; clo_env=env; clo_body=body; }
        | Op1 (loc,op,e) ->
            begin match eval env e with
            | Clo _ -> 
                error (get_loc e)
                  "Expected a set or a relation, found a closure"
            | Proc _ ->
                error (get_loc e)
                  "Expected a set or a relation, found a procedure"
            | Set v -> begin match op with
              | Set_to_rln -> Rel (E.EventRel.set_to_rln v)
              | Square -> Rel (E.EventRel.cartesian v v)
              | Comp SET -> 
                  Set
                    (E.EventSet.diff
                       (eval_set env (Var (TxtLoc.none,"_"))) v)

              | Comp RLN ->
                  error loc
                    "Bad syntax. Use '!' to complement a set, not '~'"
              | _ ->
                  error loc "Expected a relation, found a set"
            end
            | Rel v -> 
                Rel
                  (match op with
                  | Inv -> E.EventRel.inverse v
                  | Int -> U.internal v
                  | Ext -> U.ext v
                  | NoId ->
                      E.EventRel.filter
                        (fun (e1,e2) -> not (E.event_equal e1 e2))
                        v
                  | Plus -> S.tr v
                  | Star -> S.union (S.tr v) (Lazy.force id)
                  | Opt -> S.union v (Lazy.force id)
                  | Comp RLN -> 
                      E.EventRel.diff (eval_rel env (Var (TxtLoc.none,"unv"))) v
                  | Comp SET -> 
                      error loc
                        "Bad syntax. Use '~' to complement a relation, not '!'"
                  | Select (s1,s2) ->
                      let f1 = is_dir s1 and f2 = is_dir s2 in
                      S.restrict f1 f2 v
                  | Square|Set_to_rln -> 
                      error loc "Expected a set, found a relation")
            end
        | Op (loc,op,es) ->
            begin
              let vs = List.map (eval env) es in
	      if List.for_all is_rel vs then begin
		let vs = List.map as_rel vs in
		let v = match op with
		| Union -> S.unions vs
		| Seq -> S.seqs vs
		| Diff ->
                    begin match vs with
		    | [] -> assert false
		    | v::vs ->
			List.fold_left E.EventRel.diff v vs
                    end
		| Inter ->
                    begin match vs with
		    | [] -> assert false
                    | v::vs ->
			List.fold_left E.EventRel.inter v vs
                    end
		| Cartesian -> assert false in
		Rel v
	      end else if List.for_all is_set vs then begin
		let vs = List.map as_set vs in
		match op with
		| Union -> Set (E.EventSet.unions vs)
		| Seq -> assert false
		| Diff ->
                    begin match vs with
		    | [] -> assert false
		    | v::vs ->
			Set (List.fold_left E.EventSet.diff v vs)
                    end
		| Inter ->
                    begin match vs with
		    | [] -> assert false
                    | v::vs ->
			Set (List.fold_left E.EventSet.inter v vs)
                    end
		| Cartesian -> 
                    begin match vs with
		    | [v1;v2] -> 
                        Rel (E.EventRel.cartesian v1 v2)
                    | _ -> assert false
		    end
	      end else 
	        error loc
		  "Unable to operate on values of different types (set and relation)" 
            end
        | App (_,f,es) ->
            let f = eval_clo env f in
            let env = add_args f.clo_args es env f.clo_env in
            eval env f.clo_body
        | Bind (_,bds,e) ->
            let env = eval_bds env bds in
            eval env e
        | BindRec (_,bds,e) ->
            let env = env_rec (fun pp -> pp) bds env in
            eval env e

      and add_args xs es env_es env_clo =
        let vs = List.map (eval env_es) es in
        let bds =
          try
            List.combine xs vs
          with _ -> Warn.user_error "argument_mismatch" in
        List.fold_right
          (fun (x,v) env -> StringMap.add x (lazy v) env)
          bds env_clo

      and eval_rel env e =  match eval env e with
      | Rel v -> v
      | _ -> error (get_loc e) "relation expected"

      and eval_set env e = match eval env e with
      | Set v -> v
      | _ -> error (get_loc e) "set expected"

      and eval_clo env e = match eval env e with
      | Clo v -> v
      | _ -> error (get_loc e) "closure expected"

      and eval_proc loc env x = match find_env_loc loc env x with
      | Proc p -> p
      | _ ->
          Warn.user_error "procedure expected"

(* For let *)
      and eval_bds env bds = match bds with
      | [] -> env
      | (k,e)::bds ->
          let v = eval env e in
          (*
            begin match v with
            | Rel r -> printf "Defining relation %s = {%a}.\n" k debug_rel r
            | Set s -> printf "Defining set %s = %a.\n" k debug_set s
            | Clo _ -> printf "Defining function %s.\n" k
            end;
           *)
          StringMap.add k (lazy v) (eval_bds env bds)

(* For let rec *)
      and env_rec pp bds =
        let rec fix  k env vs =          
          if O.debug && O.verbose > 1 then begin
            let vb_pp =
              List.map2
                (fun (x,_) v -> x, rt_loc x v)
                bds vs in
            let vb_pp = pp vb_pp in
            MU.pp_failure test conc
              (sprintf "Fix %i" k)
              vb_pp
          end ;
          let env,ws = fix_step env bds in
          if stabilised vs ws then env
          else fix (k+1) env ws in
        fun env ->
          fix 0
            (List.fold_left
               (fun env (k,_) -> StringMap.add k (lazy empty_rel) env)
               env bds)
            (List.map (fun _ -> E.EventRel.empty) bds)

      and fix_step env bds = match bds with
      | [] -> env,[]
      | (k,e)::bds ->
          let v = eval env e in
          let env = StringMap.add k (lazy v) env in
          let env,vs = fix_step env bds in
          env,(as_rel v::vs) in

(* Showing bound variables, (-doshow option) *)

      let find_show_rel env x =
        try
          rt_loc x (as_rel (Lazy.force (StringMap.find x env)))
        with Not_found -> E.EventRel.empty in

      let doshow bds st =
        let to_show =
          StringSet.inter S.O.PC.doshow (StringSet.of_list (List.map fst bds)) in
        if StringSet.is_empty to_show then st
        else
          let show = lazy begin
            StringSet.fold
              (fun x show  ->
                let r = find_show_rel st.env x in
                StringMap.add x r show)
              to_show
              (Lazy.force st.show)
          end in
          { st with show;} in

(* Execute one instruction *)

      let rec exec txt st i c =  match i with
      | Show (_,xs) ->
          let show = lazy begin              
            List.fold_left
              (fun show x ->
                StringMap.add x (find_show_rel st.env x) show)
              (Lazy.force st.show) xs
          end in
          run txt { st with show;} c
      | UnShow (_,xs) ->
          let show = lazy begin
            List.fold_left
              (fun show x -> StringMap.remove x show)
              (Lazy.force st.show) xs
          end in
          run txt { st with show;} c
      | ShowAs (_,e,id) ->
          let show = lazy begin
            StringMap.add id
              (rt_loc id (eval_rel st.env e)) (Lazy.force st.show)
          end in
          run txt { st with show; } c
      | Test (_,pos,t,e,name,test_type) ->
          (* If this is a provides-clause and we've previously
             seen a requires-clause, abort. *)
	  if st.seen_requires_clause && test_type = Provides then
	    begin
	      let pp = String.sub txt pos.pos pos.len in
	      Warn.user_error
	        "A provided condition must not come after an `undefined_unless' condition. Culprit: '%s'." pp
	    end;
          (* If this is a requires-clause, record the fact that
             we have now seen at least one requires-clause. *)
	  let st = {st with seen_requires_clause =
	            (test_type = Requires) || st.seen_requires_clause;} in
          let skip_this_check =
            match name with
            | Some name -> StringSet.mem name O.skipchecks
            | None -> false in
          if
            O.strictskip || not skip_this_check
          then
            let v = eval_rel st.env e in
            let pred = match t with
            | Acyclic -> E.EventRel.is_acyclic
            | Irreflexive -> E.EventRel.is_irreflexive
            | TestEmpty -> E.EventRel.is_empty in
            let ok = pred v in
            let ok = MU.check_through ok in
            if ok then run txt st c
            else if skip_this_check then begin
              assert O.strictskip ;
              run txt
                { st with
                  skipped = StringSet.add (Misc.as_some name) st.skipped;}
                c
            end else begin
              if (O.debug && O.verbose > 0) then begin
                let pp = String.sub txt pos.pos pos.len in
                let cy = E.EventRel.get_cycle v in
                MU.pp_failure test conc
                  (sprintf "%s: Failure of '%s'" test.Test.name.Name.name pp)
                  (let k = show_to_vbpp st in
                  match cy with
                  | None -> k
                  | Some r -> ("CY",U.cycle_to_rel r)::k)
	      end ;
	      match test_type with
	      | Provides -> 
		  None
	      | Requires -> 
		  let () = failed_requires_clause () in
		  run txt st c
            end
          else begin
            W.warn "Skipping check %s" (Misc.as_some name) ;
            run txt st c
          end
      | Let (_,bds) ->
          let env = eval_bds st.env bds in
          let st = { st with env; } in
          let st = doshow bds st in
          run txt st c
      | Rec (_,bds) ->
          let env =
            env_rec
              (fun pp -> pp@show_to_vbpp st)
              bds st.env in
          let st = { st with env; } in
          let st = doshow bds st in
          run txt st c
      | Include (loc,fname) ->
          (* Run sub-model file *)
          let module P = ParseModel.Make(LexUtils.Default) in
          let itxt,(_,_,iprog) =
            try P.parse fname
            with Misc.Fatal msg | Misc.UserError msg ->
              error loc msg  in
          begin match run itxt st iprog with
          | None -> None            (* Failure *)
          | Some st -> run txt st c (* Go on *)
          end
      | Procedure (_,name,args,body) ->
          let p =
            Proc { proc_args=args; proc_env=st.env; proc_body=body; } in
          run txt { st with env = StringMap.add name (lazy p) st.env } c
      | Call (loc,name,es) ->
          let env0 = st.env in
          let p = eval_proc loc env0 name in
          let env1 = add_args p.proc_args es env0 p.proc_env in
          begin match run txt { st with env = env1; } p.proc_body with
          | None -> None
          | Some st_call ->
              run txt { st_call with env = env0; } c
          end
      | Latex _ -> run txt st c

      and run txt st = function
        | [] ->  Some st 
        | i::c -> exec txt st i c in

      let show =
        lazy begin
          let show =
            List.fold_left
              (fun show (tag,v) -> StringMap.add tag v show)
              StringMap.empty (Lazy.force vb_pp) in
          StringSet.fold
            (fun tag show -> StringMap.add tag (find_show_rel m tag) show)
            S.O.PC.doshow show
        end in
      run txt {env=m; show=show; 
               seen_requires_clause=false;
               skipped=StringSet.empty;} prog
        


  end
