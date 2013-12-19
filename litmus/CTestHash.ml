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

(**************)
(* Digest Env *)
(**************)

type hinfo = { hash : string ; filename : string; }

type env = hinfo StringMap.t

exception Seen

let check_env env name filename hash =
  try
    let ohash = StringMap.find name env in
    if hash = ohash.hash then raise Seen
    else Warn.user_error "Different hashes for test %s (previous file %s)"
        name ohash.filename
  with Not_found ->
    StringMap.add name {hash;filename;} env

(**********)
(* Digest *)
(**********)

module Make(P:PseudoAbstract.S)(A:Arch.Base)
    = struct

      open Printf

      type init = (MiscParser.location * SymbConstant.v) list
      type prog = (int * P.code) list
      type locations =  MiscParser.LocSet.t


      open MiscParser

      let verbose = 0

      let debug tag s =
        if verbose > 0 then eprintf "%s:\n%s\n" tag s
        else ()

(* Digest of initial state *)
      let digest_init init =
        let init =
          List.sort
            (fun (loc1,v1) (loc2,v2) -> match location_compare loc1 loc2 with
            | 0 ->
                if SymbConstant.compare v1 v2 <> 0 then begin
                  Warn.fatal
                    "Location %s non-unique in init state"
                    (dump_location loc1)
                end ;
                0
            | c -> c)
            init in
        let init =
          Misc.rem_dups
            (fun (loc1,_) (loc2,_) -> location_compare loc1 loc2 = 0)
            init in
        let pp =
          (String.concat "; "
             (List.map
                (fun (loc,v) -> sprintf "%s=%s"
                    (dump_location loc) (SymbConstant.pp_v v))
                init)) in
        debug "INIT" pp ;
        Digest.string pp


(* Code digest *)

      let digest_code code =
        let code = List.map P.dump_prog code in
        let pp =  Misc.string_of_prog code in
        debug "CODE" pp ;
        Digest.string pp


(* Observed locations digest *)
      let digest_observed locs =
        let locs = MiscParser.LocSet.elements locs in
        let pp = String.concat "; " (List.map dump_location locs) in
        debug "LOCS" pp ;
        Digest.string pp


      let digest init code observed =
        Digest.to_hex
          (Digest.string
             (digest_init init ^ digest_code code ^
              digest_observed observed))
    end