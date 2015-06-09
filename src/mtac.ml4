(***********************************************************)
(* Mtac plugin.                                            *)
(* Copyright (c) 2015 Beta Ziliani <beta@mpi-sws.org>      *)
(*                    et al.                               *)
(***********************************************************)

(** Mtac 
*)

(* These are necessary for grammar extensions like the one at the end 
   of the module *)

(*i camlp4deps: "parsing/grammar.cma" i*)
(*i camlp4use: "pa_extend.cmo" i*)

DECLARE PLUGIN "mtac"

(* $$ *)

open Pp
open Term
open Names
open Coqlib
open Universes 
open Globnames
open Vars
open Context
open Errors
open Proofview.Notations

open Run

(* $$ *)
exception ExecFailed of constr

let run_tac t i =
  Proofview.Goal.enter begin fun gl ->
    let sigma = Proofview.Goal.sigma gl in
    let env = Proofview.Goal.env gl in
    let r = run (env, sigma) t in
    match r with
    | Val (sigma', _, v) ->
      (Proofview.Unsafe.tclEVARS sigma')
      <*> (Tactics.letin_tac None (Name i) v None Locusops.nowhere)
    | Err (_, _, e) -> 
      raise (ExecFailed e)
  end


TACTIC EXTEND run
  | [ "run" constr(c) "as" ident(i) ] -> [ run_tac c i ]
END


