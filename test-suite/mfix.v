Require Import Mtac2.Mtac2.
Import Mtac2Notations.

Definition rec {A} (f : A) : M A := raise Anomaly.
  
Require Import List.
Import ListNotations.

(** Testing the construction of mmatch *)
Definition NotFound : Exception. exact exception. Qed.

Notation "f << x" := (bind f (fun r=>r x)) (at level 70).

Definition inlist A (x : A) : forall l : list A, M (In x l) :=
  fix f (l : list A) : M (In x l) :=
  mmatch l with
  | [? l r] l ++ r =>
      ttry (
        il <- rec f << l;
        ret (in_or_app l r x (or_introl il)) )
      (fun e=>mmatch e with NotFound =>
        ir <- rec f << r;
        ret (in_or_app l r x (or_intror ir))
      end)
  | [? s] (x :: s) => ret (in_eq _ _)
  | [? y s] (y :: s) => r <- rec f << s; ret (in_cons y _ _ r)
  | _ => raise NotFound
  end.


Definition inlist3 : forall A (x : A) (l : list A), M (In x l) :=
  fix f A x (l : list A) : M (In x l) :=
  mmatch l with
  | [? l r] l ++ r =>
      ttry (
        il <- ((rec f << A) x) l;
        ret (in_or_app l r x (or_introl il)) )
      (fun e=>mmatch e with NotFound =>
        ir <- rec f << r;
        ret (in_or_app l r x (or_intror ir))
      end)
  | [? s] (x :: s) => ret (in_eq _ _)
  | [? y s] (y :: s) => r <- rec f << s; ret (in_cons y _ _ r)
  | _ => raise NotFound
  end.


