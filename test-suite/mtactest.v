(******************************************************************************)
(* Mtac plugin.                                                               *)
(* Copyright (c) 2015 Beta Ziliani <beta@mpi-sws.org>                         *)
(*                    et al.                                                  *)
(******************************************************************************)
Require Import Lists.List.

Require Import Mtac.Mtac.

Import MtacNotations.

Module AFewBasicExamples.

Goal True.
  run (ret I) as H.
  run (hypotheses) as Hs.
  run (mtry @raise nat exception with _ => ret 0 end) as H'.
  rrun (ret I).
Qed.

Definition test_of_definition : nat := $( rrun (ret 0) )$.

Definition test_of_definition_evar  : 0 = 0 := $( rrun (ret (eq_refl _)) )$.


Definition MyException (x:nat) : Exception. exact exception. Qed.
Program Definition test_exception_with_evar : M nat :=
  mtry
    e <- evar nat;
    raise (MyException e)
  with [e] MyException e => ret e
  end.

Check (Mrun test_exception_with_evar).

End AFewBasicExamples.

Module Abs.
Definition abs_evar (A : Type) :=
  e <- evar A;
  f <- @abs Type (fun A'=>A') A e  : M (forall A : Type, A);
  ret (f nat, f bool).

Check (fun A : Type => $( rrun (abs_evar A) )$ ). 

Definition abs_val2 (A : Type) :=
  e <- evar A;
  f <- @abs Type (fun A'=>A) A e;
  ret (f bool, f A).

Fail Check (fun A : Type => Mrun (abs_val2 A)). 
(* variable appearing in the returning type *)


Definition abs_dep (A : Type) (x : A) :=
  e <- evar nat;
  @abs Type (fun _ => nat) A e : M (Type -> nat).

(* 1. e := ?u[A, x] : nat[A, x : A]
   2. f := fun A' => ?u[A', x]
*)   

Fail Check fun A x => Mrun (@abs_dep A x).
(* Cannot abstract variable in a context depending on it *)

Definition test := nu n : nat, e <- evar nat; abs n e.
Check (fun x y => let f:= Mrun test in Mrun (mmatch f x with x => ret true | _ => ret false end)).

End Abs.

Section Misc.
Set Printing Universes.


Program Definition test_ho {A} B (t : A) :=
  mmatch t with
  | [f (x:B)] f x => ret f
  | _ => raise exception
  end.

Check (Mrun (test_ho nat (id 0))).

Example exret : 1 = 1.
set (H := Mrun (ret True)).
Abort.

Example exbind : 1 = 1.
set (H := Mrun (bind (ret 8) (fun n=>ret (n+1)))).
Abort.

Example exbind2 : 1 = 1.
set (H := Mrun (bind (bind (ret 8) (fun n=>ret (n+1))) (fun n=>ret (n+3)))).
Abort.

Example bla : 1 = 1.
set (H := Mrun ((fun x => bind x (fun n=>ret n)) (ret 8))).
Abort.

Example excomp : 1 = 1.
set (T := (fun x=>ret x) 8).
set (H := Mrun T).
Abort.

Example excomp2 : 1 = 1.
set (T := let x:=ret 8 in x).
set (H := Mrun T).
Abort.

Example exfix2 : 1 = 1.
set (iszero n := match n with 0 => true | _ => false end).
set (plus := mfix1 f (a : nat*nat) : M _ :=
    match a with
    | (n, m) =>
      if iszero n then
        ret m
      else
        f (n-1, S m)
    end)
  .
Time set (H := Mrun (plus (10, 52))).
idtac.
Abort.


Example exmatch : 1 = 1.
set (H1 := Mrun (mmatch 0 return M nat with
     | 0 => ret 8
     end)).
set (H2 := Mrun (mmatch 0 return M nat with
     | 1 => ret 8
     | 0 => ret 2
     end)).
Abort.



Definition madd : nat -> nat -> M nat :=
  mfix2 f (m : _) (n : nat) : M _ :=
    mmatch m return M nat with
    | 0 => ret n
    | [m'] (S m') => x <- f m' n; ret (S x)
    end.

Time Definition mresult1: nat := Mrun (madd 100 5000).
Time Definition mresult2: nat := Mrun (madd 1000 1000).
Time Definition mresult3: nat := Mrun (madd 1000 10).
Time Definition mresult4: nat := Mrun (madd 10 10000).
(*
100+5000 takes 3s
1000+1000 takes 18s
1000+10 takes 56s
10+10000 takes 1s
 *)

Ltac ladd m n :=
  match m with
  | 0 => constr:n
  | S ?m' => let x := ladd m' n in constr:(S x)
  end.

Definition lresult1: nat.
  Time let x := ladd 100 5000 in exact x.
Defined.
Definition lresult2: nat.
  Time let x := ladd 1000 1000 in exact x.
Defined.
Definition lresult3: nat.
  Time let x := ladd 1000 10 in exact x.
Defined.
Definition lresult4: nat.
  Time let x := ladd 10 10000 in exact x.
Defined.
(*
100+5000 takes .3s
1000+1000 takes .6s
1000+10 takes .3s
10+10000 takes .2s
 *)



Definition ElementNotFound : Exception.  exact exception. Qed.

Definition inlist A (x : A) := 
  mfix1 f (s : _) : M (In x s) :=
  mmatch s as s' return M In x s' with
  | [s] x::s => ret (in_eq x s)
  | [y s] y :: s => 
    t <- f s : M (In x s);
    ret (in_cons y x s t)
  | _ => raise ElementNotFound
  end.

Implicit Arguments inlist [A].

Set Printing Existential Instances.

Example x_en_zyx_u : forall A (x y z : A), 
  In x (z :: y :: x :: nil).
Proof.
  intros A x y z.
  rrun (inlist _ _).
Qed.

Example exinlist (x1 x2 x3 : nat) : In x2 (x1 :: x2 :: nil).
  rrun (inlist x2 (x1:: x2:: nil)).
Qed.


Example exinlist' (x1 x2 x3 x4 x5 x6 x7 x8 x9 x10: nat) : 
  let l := (x1 :: x2 :: x3 :: x4 :: x5 :: x6 :: x7 :: x8 :: x9 :: x10 :: nil) in
  In x10 l.
intro l.
unfold l.
rrun (inlist _ _).
Qed.

Require Import Strings.String.

Definition MyException (s : string) : Exception.
  exact exception.
Qed.


Definition AnotherException : Exception.
  exact exception.
Qed.

Definition test_ex (e : Exception) : M string := 
  mtry raise e
  with
  | AnotherException => ret ""%string
  | MyException "hello"%string => ret "world"%string
  | [s] MyException s => ret s
(*  | [e'] e' => raise e' *) (* universe constraints problems *)
  end.

Check (Mrun (test_ex (MyException "hello"%string))).
Check (Mrun (test_ex AnotherException)).
Check (Mrun (test_ex (MyException "dummy"%string))).
Fail Check (Mrun (test_ex exception)).



Import ListNotations.

Definition inlist'' {A} (x : A) :=
  mfix1 f (s : list A) : M _ :=
    mmatch s as s' return M (In x s') with
    | [l r] l ++ r => 
      mtry 
        il <- f l;
        ret (in_or_app l r x (or_introl il))
      with _ =>
        ir <- f r;
        ret (in_or_app l r x (or_intror ir))
      end
    | [s'] (x :: s') => ret (in_eq _ _)
    | [y s'] (y :: s') =>
      r <- f s';
      ret (in_cons y _ _ r)
    | _ => raise AnotherException
    end.


Definition remove {A} (x : A) :=
  mfix1 f (s : list A) : M (list A) :=
    mmatch s with
    | [s'] (x :: s') => f s'
    | [y s'] (y :: s') => 
      r <- f s';
      ret (y :: r)
    | _ => ret s
    end.


Definition inlistS {A} (x : A) :=
  mfix1 f (s : list A) : M (In x s) :=
    mmatch s with
    | [s'] (x :: s') => ret (in_eq _ _)
    | [y s'] (y :: s') =>
      r <- f s';
      ret (in_cons y _ _ r)
    | [l r] l ++ r => 
      mtry 
        il <- f l;
        ret (in_or_app l r x (or_introl il))
      with _ =>
        ir <- f r;
        ret (in_or_app l r x (or_intror ir))
      end
    | _ => raise AnotherException
    end.



Example exinlist'' (x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11: nat) : 
  let l := (x1 :: x2 :: x3 :: x4 :: x5 :: x6 :: x7 :: x8 :: x9 :: x10 :: nil) in
  In x11 (
    l ++ l ++ l ++ l ++ l ++ l ++ l ++ l ++ l ++ l ++ l ++ l ++
    l ++ l ++ l ++ l ++ l ++ l ++ l ++ l ++ l ++ l ++ l ++ l ++
    l ++ l ++ l ++ l ++ l ++ l ++ l ++ l ++ l ++ l ++ l ++ l ++
    l ++ l ++ l ++ l ++ l ++ l ++ l ++ l ++ l ++ l ++ l ++ l ++
    l ++ l ++ l ++ l ++ l ++ l ++ l ++ l ++ l ++ l ++ l ++ l ++
    l ++ l ++ l ++ l ++ l ++ l ++ l ++ l ++ l ++ l ++ l ++ l ++ [x11]).
intro l.
(* repeat rewrite <- app_assoc_reverse. *)
Time rrun (inlist'' _ _).
Time Qed.


Example exinlistS (x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11: nat) : 
  let l := (x1 :: x2 :: x3 :: x4 :: x5 :: x6 :: x7 :: x8 :: x9 :: x10 :: nil) in
  In x11 (
    l ++ l ++ l ++ l ++ l ++ l ++ l ++ l ++ l ++ l ++ l ++ l ++
    l ++ l ++ l ++ l ++ l ++ l ++ l ++ l ++ l ++ l ++ l ++ l ++
    l ++ l ++ l ++ l ++ l ++ l ++ l ++ l ++ l ++ l ++ l ++ l ++
    l ++ l ++ l ++ l ++ l ++ l ++ l ++ l ++ l ++ l ++ l ++ l ++
    l ++ l ++ l ++ l ++ l ++ l ++ l ++ l ++ l ++ l ++ l ++ l ++
    l ++ l ++ l ++ l ++ l ++ l ++ l ++ l ++ l ++ l ++ l ++ l ++ [x11]).
intro l.
(* repeat rewrite <- app_assoc_reverse. *)
Time rrun (inlistS _ _).
Time Qed.

End Misc.