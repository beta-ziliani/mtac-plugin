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
      Errors.error ("Uncaught exception: " ^ (string_of_ppcmds (Termops.print_constr e)))
  end

let pretypeT env sigma t c =
  let (_, e) = MtacNames.mkT_lazy sigma env in
  let ty = Retyping.get_type_of env sigma c in
  let (h, args) = Reductionops.whd_betadeltaiota_stack env sigma ty in
  if eq_constr_nounivs e h && List.length args = 1 then
    let sigma = Evarconv.the_conv_x_leq env t (List.hd args) sigma in
    (sigma, c)
  else
    Errors.error "Not a Mtactic"


let refine_run_tac (sigma, t) =
  Proofview.Goal.nf_enter begin fun gl ->
(*    let sigma = Proofview.Goal.sigma gl in *)
    let env = Proofview.Goal.env gl in
    let concl = Proofview.Goal.concl gl in
    let (sigma, t) = pretypeT env sigma concl t in
    let r = run (env, sigma) t in
    match r with
    | Val (sigma', _, v) ->
      (Proofview.Unsafe.tclEVARS sigma')
      <*> (Proofview.Refine.refine ~unsafe:false (fun s->(s, v)))
    | Err (_, _, e) -> 
      Errors.error ("Uncaught exception: " ^ (string_of_ppcmds (Termops.print_constr e)))
  end


TACTIC EXTEND run
  | [ "run" constr(c) "as" ident(i) ] -> [ run_tac c i ]
END

TACTIC EXTEND rrun
  | [ "rrun" open_constr(c) ] -> [ refine_run_tac c ]
END

