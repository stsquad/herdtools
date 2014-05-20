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

(** Generate hash from a litmus test *)

(**************)
(* Digest Env *)
(**************)

type hinfo = { hash : string ; filename : string; }

type env = hinfo StringMap.t

exception Seen

val check_env : env -> string -> string -> string -> env

(*******************)
(* Compute digests *)
(*******************)

module Make :
  functor (A:ArchBase.S) -> sig
    type init = MiscParser.state
    type prog = (A.param, A.pseudo list) MiscParser.process list

    type locations = MiscParser.LocSet.t

    val refresh_labels : string -> prog -> prog
    val digest : init -> prog -> locations -> string
  end    
