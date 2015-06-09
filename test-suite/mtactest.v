(******************************************************************************)
(* Unicoq plugin.                                                             *)
(* Copyright (c) 2015 Beta Ziliani <beta@mpi-sws.org>                         *)
(*                    et al.                                                  *)
(******************************************************************************)
Require Import Lists.List.

Require Import Mtac.Mtac.

Import MtacNotations.

Goal True.
  run (ret I) as H.
  run (hypotheses) as Hs.
  Fail run (@raise nat exception) as H'.
  rrun (ret I).
Qed.

Definition test_of_definition : nat := $( rrun (ret 0) )$.
Definition test_of_definition_evar x : x = 0 := $( rrun (ret (eq_refl _)) )$.
