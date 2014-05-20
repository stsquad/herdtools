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

(** A 'generic' parsing module for memevents/litmus files *)

(* Wapper (takes care of parsing exceptions *)
val call_parser :
    string -> Lexing.lexbuf -> 'a -> ('a -> Lexing.lexbuf -> 'b) -> 'b

(* Configuration, to change kind, condition and rename *)
module type Config = sig
  val debuglexer : bool
  val check_kind : string -> ConstrGen.kind option
  val check_cond : string -> string option
end

module DefaultConfig : Config

(* input signature, a lexer and a parser for a given architecture *)
module type LexParse = sig
  type token
  type pseudo
  type param

  val lexer : Lexing.lexbuf -> token
  val parser :
       (Lexing.lexbuf -> token) -> Lexing.lexbuf ->
	 (param, pseudo list) MiscParser.process list * MiscParser.gpu_data option
end

module type S = sig
  type pseudo
  type param
  val parse : in_channel -> Splitter.result -> (param, pseudo) MiscParser.t
end

(* Build a generic parser *)
module Make
    (C:Config)
    (A:ArchBase.S)
    (L: LexParse with type pseudo = A.pseudo and type param = A.param) :
    S with type pseudo = A.pseudo and type param = A.param
