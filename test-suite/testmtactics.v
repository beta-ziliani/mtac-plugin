Require Import Mtac.Mtactics.
Import MtacNotations.

Require Import List.
Import ListNotations.

Example test_ass (P Q : Prop) (p:P) (q:Q) : P /\ Q.
  split; rrun assumption.
Qed.


Definition test_case := fun (G : Type) => Mrun (constrs (list G)).
Print test_case.

(* Bad error messages *)
Fail Definition test_case' := run (constrs list).
(* Definition test_case' := run (constrs (le 0 0)). *)



Example test_apply (P Q : Prop) (p:P -> Q) (q:P) : Q.
  rrun (apply p).
  Unshelve.
  rrun assumption.
Qed.

Example test_badapply (P Q : Prop) (p:P -> Q) (q:P) : Q.
  Fail rrun (apply q).
Abort.

Example test_eapply (P Q : Prop) (p: forall T1, T1 -> Q) (q:P) : Q.
  rrun (rs <- eapply p; ass <- retS (snd rs); print_term ass;; ret (fst rs)).
Abort.

Example test_eapply2 (P Q : Prop) (p:P -> Q) (q:P) : Q.
  rrun (ps <- eapply p; ((try_all eassumption (snd ps));; ret (fst ps))).
Qed.

Example test_tauto (P Q R : Prop) : 
  P \/ Q -> P /\ R -> forall x:nat, x > 0 \/ exists T : Prop, P /\ R /\ T.
Proof.
  rrun (tauto0 _).
Qed.

Definition test_fill_imp (x : nat) : In x [x] := in_eq ?.