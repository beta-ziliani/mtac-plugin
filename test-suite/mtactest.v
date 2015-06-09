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