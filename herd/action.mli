(*********************************************************************)
(*                        Memevents                                  *)
(*                                                                   *)
(* Jade Alglave, Luc Maranget, INRIA Paris-Rocquencourt, France.     *)
(* Susmit Sarkar, Peter Sewell, University of Cambridge, UK.         *)
(*                                                                   *)
(*  Copyright 2010 Institut National de Recherche en Informatique et *)
(*  en Automatique and the authors. All rights reserved.             *)
(*  This file is distributed  under the terms of the Lesser GNU      *)
(*  General Public License.                                          *)
(*********************************************************************)


module type S = sig

  module A : Arch.S

  type action

  val mk_init_write : A.location -> A.V.v -> action

  val pp_action     : bool -> action -> string

(* Some architecture-specific sets, and their definitions
   e.g. ["rmw", is_rmw; "ls", is_successful_lock]
 *)
  val arch_sets : (string * (action -> bool)) list

(**************************************)
(* Access to sub_components of events *)
(**************************************)

  val value_of : action -> A.V.v option
  val location_of   : action -> A.location option
  val location_reg_of : action -> A.reg option
  val global_loc_of    : action -> A.global_loc option

(****************************)
(* Convenience on locations *)
(****************************)

  val location_compare : action -> action -> int
(*  val same_location : action -> action -> bool
  val same_value : action -> action -> bool
  val is_visible_location : A.location -> bool *)

(************************)
(* Predicates on events *)
(************************)

(* relative to memory *)
  val is_mem_store : action -> bool
  val is_mem_load : action ->  bool
  val is_mem : action -> bool
  val is_atomic : action -> bool
  val get_mem_dir : action -> Dir.dirn

(* relative to the registers of the given proc *)
  val is_reg_store : action -> A.proc -> bool
  val is_reg_load : action -> A.proc -> bool
  val is_reg : action -> A.proc -> bool

(* Reg events, proc not specified *)
  val is_reg_store_any : action -> bool
  val is_reg_load_any : action -> bool
  val is_reg_any : action -> bool

(* Store/Load to memory or register *)
  val is_store : action -> bool
  val is_load : action -> bool

(* Barriers *)
  val is_barrier : action -> bool
  val barrier_of : action -> A.barrier option

(* Commits *)
  val is_commit : action -> bool

(* Mutex operations *)
  val is_mutex_action : action -> bool

(********************)
(* Equation solving *)
(********************)

  val undetermined_vars_in_action : action -> A.V.ValueSet.t
  val simplify_vars_in_action : A.V.solution -> action -> action

(************************)
(* Parallel composition *)
(************************)

  val make_action_atomic : action -> action

end