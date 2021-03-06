(*********************************************************************)
(*                          Litmus                                   *)
(*                                                                   *)
(*        Luc Maranget, INRIA Paris-Rocquencourt, France.            *)
(*        Susmit Sarkar, University of Cambridge, UK.                *)
(*                                                                   *)
(*  Copyright 2013 Institut National de Recherche en Informatique et *)
(*  en Automatique and the authors. All rights reserved.             *)
(*  This file is distributed  under the terms of the Lesser GNU      *)
(*  General Public License.                                          *)
(*********************************************************************)


(* Stop test as condition is settled *)
type t =
  | NoSpeed (* Don't *)
  | SomeSpeed (* Do for current run *)
  | AllSpeed  (* Do for current run and following runs (dont mode)*)

let tags = ["no";"some";"all";]


let parse tag = match tag with
| "false"|"no" -> Some NoSpeed
| "true"|"some" -> Some SomeSpeed
| "all"|"dont" -> Some AllSpeed
| _ -> None

let pp = function
  | NoSpeed -> "no"
  | SomeSpeed -> "some"
  | AllSpeed -> "all"
