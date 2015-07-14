Require Export Mtac.Mtac.
Import MtacNotations.

Require Import List.
Import ListNotations.


Module ListMtactics.

  Definition NotFound : Exception.
    exact exception.
  Qed.

  Definition inlist {A} (x : A) :=
    mfix1 f (s : list A) : M _ :=
      mmatch s as s' return M (In x s') with
      | [? l r] l ++ r =>
        mtry
          il <- f l;
          ret (in_or_app l r x (or_introl il)) 
        with NotFound =>
          ir <- f r;
          ret (in_or_app l r x (or_intror ir))
        end
      | [? s'] (x :: s') => ret (in_eq _ _)
      | [? y s'] (y :: s') =>
        r <- f s';
        ret (in_cons y _ _ r)
      | _ => raise NotFound
      end.
    
  Definition find {A} {B : A -> Type} (x : A) :=
    mfix1 f (s : list (sigT B)) : M (B x) :=
      mmatch s with
      | [? l r] l ++ r => 
        mtry 
          f l
        with NotFound =>
          f r
        end
      | [? y s'] (existT B x y :: s') => ret y
      | [? y s'] (y :: s') => f s'
      | _ => raise NotFound
      end.

  Definition remove {A} {B : A -> Type} (x : A) :=
    mfix1 f (s : list (sigT B)) : M (list (sigT B)) :=
      mmatch s with
      | [? y s'] (existT B x y :: s') => ret s'
      | [? y s'] (y :: s') => r <- f s'; ret (y :: r)
      | _ => raise NotFound
      end.

  Fixpoint iter {A:Type} (f : A -> M unit) (l : list A) : M unit :=
    match l with 
    | [] => ret tt
    | (a :: l') => f a;; iter f l'
    end.

End ListMtactics.

Set Implicit Arguments.

Definition AssumptionNotFound {T} (x : T) : Exception. exact exception. Qed.
Definition assumption {P : Type} : M P :=
  hs <- hypotheses; 
  let f := mfix1 f (s : list Hyp) : M P :=
    mmatch s return M P with
    | [? (x:P) t s'] (@ahyp P x t :: s') => ret x
    | [? a s'] (a :: s') => f s'
    | _ => raise (AssumptionNotFound P)
    end
  in f hs.

(** Tactic to unify two terms [x] and [y]. *)
Definition NotUnifiableException : Exception. exact exception. Qed.
Program Definition unify A (x y : A) (P : A -> Type) (f : x = y -> P y) : M (P x) :=
    a <- mmatch x as x' return M (x = x' -> P x') with 
         | y => ret (fun H => f H)
         | _ => raise NotUnifiableException
         end;
    retS (a (eq_refl _)).
Arguments unify {A} x y P f.

Definition CantApply {T1 T2} (x:T1) (y:T2) : Exception. exact exception. Qed.
Definition apply {P T} (l : T) : M P :=
  (mfix2 app (T : _) (l' : T) : M P :=
    mtry unify P T (fun a=>a) (fun _ => l')
    with NotUnifiableException =>
      mmatch T return M P with
      | [? T1 T2] (forall x:T1, T2 x) => [H]
          e <- evar T1;
          l' <- retS (eq_rect_r (fun T => T -> T2 e)
            (fun l : forall x : T1, T2 x => l e) H l');
          app (T2 e) l'
      | _ => raise (CantApply P l)
      end
    end) _ l.


Definition eapply {P T} (l : T)  :=
  (mfix3 app (T : _) (l' : T) (es : list dyn) : M (P * list dyn)%type :=
    mtry unify P T (fun a=>(a*list dyn)%type) (fun _ => (l', es))
    with NotUnifiableException =>
      mmatch T with
      | [? T1 T2] T1 -> T2 => [H]
          e <- evar T1;
          l' <- retS (eq_rect_r (fun T => T -> T2)
            (fun l : T1 -> T2 => l e) H l');
          app T2 l' (Dyn _ e :: es)
      | [? T1 T2] (forall x:T1, T2 x) => [H]
          e <- evar T1;
          l' <- retS (eq_rect_r (fun T => T -> T2 e)
            (fun l : forall x : T1, T2 x => l e) H l');
          app (T2 e) l' es
      | _ => raise (CantApply P l)
      end
    end) _ l [].


Fixpoint try_all (t : forall T, T -> M unit)  ls :=
  match ls with
  | [] => ret tt
  | (Dyn _ e :: ls') => 
    b <- is_evar e; 
    if b then t _ e;; try_all t ls' else try_all t ls'
  end.

Definition eassumption (T : Type) (e:T) :=
  r <- @assumption T;
  mmatch r with e => ret tt | _ => raise exception end.


Definition try_once_each_constr {P} T (x : T) : M P :=
  cs <- constrs x;
  (fix f (cs : list dyn) : M P :=
    match cs with
    | [] => evar _
    | (Dyn _ c :: cs') =>
      mtry 
        ps <- eapply c; 
        ass <- retS (rev (snd ps));
        try_all eassumption ass;;
        ret (fst ps)
      with _ => f cs' end
    end) cs.


Lemma uncurry P Q R : (P /\ Q -> R) -> P -> Q -> R.
Proof. tauto. Qed.

Lemma curry (P Q R : Prop) : (P -> Q -> R) -> P /\ Q -> R.
Proof. tauto. Qed.

Lemma orE (P Q R : Prop) : (P -> R) -> (Q -> R) -> P \/ Q -> R.
Proof. tauto. Qed.



Program Definition tauto0 :=
  mfix1 f (P : Prop) : M P :=
    mmatch P as P' return M P' with
    | True => ret I
    | [? R Q] R /\ Q =>
      r1 <- f R;
      r2 <- f Q;
      ret (conj r1 r2)
    | [? R Q] R \/ Q =>
      mtry
        r <- f R;
        ret (or_introl Q r)
      with [? T (x:T)] AssumptionNotFound x =>
        r <- f Q;
        ret (or_intror R r)
      end
    | [? R Q T : Prop] (R /\ Q -> T) =>
      r <- f (R -> Q -> T);
      ret (curry r)
    | [? R Q T : Prop] (R \/ Q -> T) =>
      r1 <- f (R -> T);
      r2 <- f (Q -> T);
      ret (orE r1 r2)
    | [? R Q : Prop] R -> Q =>
      nu (x : R),
        r <- f Q;
        abs x r
    | [? R (Q : R -> Prop)] forall x: R, Q x =>
      nu (x : R),
        r <- f (Q x);
        abs x r
    | [? A (q:A -> Prop)] (exists x : A, q x) =>
        X <- evar A;
        r <- f (q X);
        ret (ex_intro q X r)
    | _ => assumption
    end.

Definition CannotFillImplicits : Exception. exact exception. Qed.

Definition fill_implicits {A B} (x : A) : M B :=
  let rec :=
    mfix3 f (n : nat) (A' : Type) (x' : A') : M B :=
      match n with
      | 0 => raise CannotFillImplicits
      | S n' =>
        mmatch A' with
        | B => [H] retS (eq_rect A' id x' B H) : M B
        | [? (T : Type) (P : T -> Type)] forall y:T, P y =c> [H]
          nu z : T,
            e <- evar T;
            f n' _ (eq_rect A' id x' (forall y:T, P y) H e)
        | _ => print_term A';; raise exception
        end
      end
  in rec 10 _ x.
 
Notation "f ?" := (eval (fill_implicits f)) (at level 0).

Definition munify A (x y : A) (P : A -> Type) (f : x = y -> M (P y)) : M (P x) 
  := mmatch x with y => [H] f H | _ => raise NotUnifiableException end.
Arguments munify {A} x y P f.

Definition open_pattern {A} {P:A->Type} {t:A}  :=
  mfix1 op (p : tpatt A P t) : M (tpatt A P t) :=
    match p return M _ with
    | base x f u => ret p : M (tpatt _ _ _)
    | @tele A' B' C t' f =>
      e <- evar C;
      munify (tpatt A' B' t') (tpatt A P t) (fun _ => tpatt A P t)
      (fun H => op (match H in (_ = y) return y with
                      | eq_refl => (f e)
                    end ))
    end.

Definition NoPatternMatches : Exception. exact exception. Qed.
Fixpoint mmatch' A P t (ps : list (tpatt A P t)) : M (P t) :=
  match ps with
  | [] => raise NoPatternMatches
  | (p :: ps') => 
    p' <- open_pattern p;
    mtry 
      match p' with
      | @base A P t t' f u => 
        munify t t' P f : M (P t)
      | _ => raise NotUnifiableException
      end
    with NotUnifiableException =>
      mmatch' ps'
    end
  end.
Arguments mmatch' {A} {P} t ps.

Definition eopen_pattern {A} {P:A->Type} {t:A}  :=
  mfix2 op (p : tpatt A P t) (ls : list dyn) : M (list dyn * tpatt A P t)%type :=
    match p return M _ with
    | base x f u => ret (ls, p) : M (list dyn * tpatt _ _ _)
    | @tele A' B' C t' f =>
      e <- evar (C : Type);
      mmatch tpatt A' B' t' with
      | tpatt A P t => [H] op (match H in (_ = y) return y with
                               | eq_refl => (f e)
                               end ) (Dyn _ e :: ls)
      end
    end.
Arguments eopen_pattern {A} {P} {t} x1 x2.
Set Printing Universes.


Definition match_goal {A:Type} {P:A->Type} (t : A) (p : tpatt A P t) 
: M (list dyn * P t) :=
  pes <- eopen_pattern p [];
  let (ls, goal) := pes : (list dyn@{i} * tpatt _ _ _)%type in
  mmatch goal with
  | [? f u] @base A P t t f u => 
    pf <- (f eq_refl) : M (P t);
    ret (ls, pf)
  end.

Arguments match_goal _ _ _ p%mtac_patt.
Notation "'mmatch' x ls" := (mmatch' x ls).
Definition inl' A (x : A) : forall l : list A, M (In x l) :=
  mfix1 f (l : list A) : M (In x l) :=
  mmatch l with
  | [? s] (x :: s) => ret in_eq?
  | [? y s] (y :: s) => r <- f s; ret (in_cons y _ _ r)
  | _ => raise exception
  end.


Definition intro {A : Type} {P: A -> Type} (f : forall x:A, M (P x)) 
  : M (forall x:A, P x)
  := nu x:A, r <- f x; abs x r.



Definition LMap {A B} (f : A -> M B) :=
  mfix1 rec (l : list A) : M (list B) := 
  match l with
  | [] => ret []
  | (x :: xs) => l <- rec xs;
                b <- f x;
                ret (b :: l)
  end.
  
Definition CantCoerce : Exception. exact exception. Qed.

Definition coerce {A B : Type} (x : A) : M B :=
  mmatch A return M B with
  | B => [H] ret (eq_rect_r _ (fun x0 : B => x0) H x)
  | _ => raise CantCoerce
  end.

Program Definition copy_ctx {A} (B : A -> Type) :=
  mfix1 rec (d : dyn) : M Type :=
  mmatch d with
  | [? C (D : C -> Type) (E : forall y:C, D y)] {| elem := fun x : C=>E x |} => 
    nu y : C,
      r <- rec (Dyn _ (E y));
      pabs y r
  | [? c : A] {| elem := c |} => 
    ret (B c) 
  end.

Definition destruct {A : Type} (n : A) {P : A -> Prop} : M (P n) :=
  l <- constrs A;
  l <- LMap (fun d : dyn=> 
             t' <- copy_ctx P d;
             e <- evar t';
             ret {| elem := e |}) l;
  let c := {| case_ind := A;
              case_val := n;
              case_type := P n;
              case_return := {| elem := fun n : A => P n |};
              case_branches := l
           |} in
  d <- makecase c;
  d <- coerce (elem d);
  ret d.


Goal forall n : nat, True.
  intro n.
  Set Printing Implicit.
  rrun (destruct n).
  Unshelve.
  simpl.
  apply I.
  intro n'.
  simpl.
Abort.


(*
This is a proposal for a different kind of goal handling than the one attempted by Thomas. Given the difficulty to maintain Ocaml code free of bugs, the proposal is to keep as much code on the Coq side as possible. This is in accordance to #2. In this proposal, goals are just evars that are registered as goals. At a given point one can access the local context (hypotheses).

The primitives in Mtac2 can be the following:
```Coq
registerGoal {A:Type} : A -> Mtac2 unit
unregisterGoal {A:Type} : A -> Mtac2 unit
goals : Mtac2 (list dyn)
hypotheses : Mtac2 (list dyn)
```

The high-level idea is that the current goal will be passed along the tactics. For instance, the intro tactic 

Then, for refining a goal we can just use the primitive for unification (see #2). For instance, the apply tactic can be written as follow:
```Coq
Definition apply {P T} (l : T) : M P :=
  (mfix2 app (T : _) (l' : T) : M P :=
    mtry unify P T (fun a=>a) (fun _ => l')
    with NotUnifiableException =>
      mmatch T return M P with
      | [? T1 T2] (forall x:T1, T2 x) => [H]
          e <- evar T1;
          registerGoal e;
          l' <- retS (eq_rect_r (fun T => T -> T2 e)
            (fun l : forall x : T1, T2 x => l e) H l');
          app (T2 e) l'
      | _ => raise (CantApply P l)
      end
    end) _ l.
```
Then, a tactical like ";" can take the list of goals and pass them to the list of tactics. Note that each time we create a new goal, it has its local context mapped to the current one. This will maintain the current Ltac semantics. For instance, a tactic like the following, in the context where ```x``` is a natural number will generate two "goals" with the second one in an extended context (intros is just using the nu operator).
```Coq
case x; [ | intros n ]; reflexivity
```

There is an issue with the 
*)

Example test A (x y z : A) : In x [z;y;x].
rrun (inl' _ _).
Qed.
(*  
Example test (x : nat) (y : nat) (H : x > y) : x > y.
rrun (p <- match_goal ([? a] a => eassumption a;; evar a >> ret )%mtac_patt; ret (snd p)).

match goal with
| [u:nat, v:nat, H : ?v > ?u |- _] => idtac v; apply I 
end.


*)