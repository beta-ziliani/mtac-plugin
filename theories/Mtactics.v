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
      | [l r] l ++ r =>
        mtry
          il <- f l;
          ret (in_or_app l r x (or_introl il)) 
        with NotFound =>
          ir <- f r;
          ret (in_or_app l r x (or_intror ir))
        end
      | [s'] (x :: s') => ret (in_eq _ _)
      | [y s'] (y :: s') =>
        r <- f s';
        ret (in_cons y _ _ r)
      | _ => raise NotFound
      end.
    
  Definition find {A} {B : A -> Type} (x : A) :=
    mfix1 f (s : list (sigT B)) : M (B x) :=
      mmatch s with
      | [l r] l ++ r => 
        mtry 
          f l
        with NotFound =>
          f r
        end
      | [y s'] (existT B x y :: s') => ret y
      | [y s'] (y :: s') => f s'
      | _ => raise NotFound
      end.

  Definition remove {A} {B : A -> Type} (x : A) :=
    mfix1 f (s : list (sigT B)) : M (list (sigT B)) :=
      mmatch s with
      | [y s'] (existT B x y :: s') => ret s'
      | [y s'] (y :: s') => r <- f s'; ret (y :: r)
      | _ => raise NotFound
      end.

End ListMtactics.

Set Implicit Arguments.

Definition AssumptionNotFound {T} (x : T) : Exception. exact exception. Qed.
Definition assumption {P : Type} : M P :=
  hs <- hypotheses; 
  let f := mfix1 f (s : list Hyp) : M P :=
    mmatch s return M P with
    | [(x:P) t s'] (@ahyp P x t :: s') => ret x
    | [a s'] (a :: s') => f s'
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
      | [T1 T2] (forall x:T1, T2 x) => [H]
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
      | [T1 T2] T1 -> T2 => [H]
          e <- evar T1;
          l' <- retS (eq_rect_r (fun T => T -> T2)
            (fun l : T1 -> T2 => l e) H l');
          app T2 l' (Dyn _ e :: es)
      | [T1 T2] (forall x:T1, T2 x) => [H]
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

Definition eassumption T (e:T) :=
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
    | [R Q] R /\ Q =>
      r1 <- f R;
      r2 <- f Q;
      ret (conj r1 r2)
    | [R Q] R \/ Q =>
      mtry
        r <- f R;
        ret (or_introl Q r)
      with [T (x:T)] AssumptionNotFound x =>
        r <- f Q;
        ret (or_intror R r)
      end
    | [R Q T : Prop] (R /\ Q -> T) =>
      r <- f (R -> Q -> T);
      ret (curry r)
    | [R Q T : Prop] (R \/ Q -> T) =>
      r1 <- f (R -> T);
      r2 <- f (Q -> T);
      ret (orE r1 r2)
    | [R Q : Prop] R -> Q =>
      nu (x : R),
        r <- f Q;
        abs x r
    | [R (Q : R -> Prop)] forall x: R, Q x =>
      nu (x : R),
        r <- f (Q x);
        abs x r
    | [A (q:A -> Prop)] (exists x : A, q x) =>
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
        | [(T : Type) (P : T -> Type)] forall y:T, P y =c> [H]
          nu z : T,
            e <- evar T;
            f n' _ (eq_rect A' id x' (forall y:T, P y) H e)
        | _ => print_term A';; raise exception
        end
      end
  in rec 10 _ x.
 
Notation "f ?" := (eval (fill_implicits f)) (at level 0).

Definition open_pattern {A} {P:A->Type} {t:A}  :=
  mfix1 op (p : tpatt A P t) : M (tpatt A P t) :=
    match p return M _ with
    | base x f u => ret p : M (tpatt _ _ _)
    | @tele A' B' C t' f =>
      e <- evar C;
      mmatch tpatt A' B' t' with
      | tpatt A P t => [H] op (match H in (_ = y) return y with
                               | eq_refl => (f e)
                               end )
      end
    end.

Definition NoPatternMatches : Exception. exact exception. Qed.

Fixpoint mmatch' A P t (ps : list (tpatt A P t)) : M (P t) :=
  match ps with
  | [] => raise NoPatternMatches
  | (p :: ps') => 
    p' <- open_pattern p;
    mtry 
      mmatch p' with
      | [(f : t = t -> M (P t)) u] base t f u => [H] (f eq_refl)
      | _ => raise NotUnifiableException
      end
    with NotUnifiableException =>
      mmatch' ps'
    end
  end.
Arguments mmatch' {A} {P} t ps.

(*
  Definition inlist {A} (x : A) :=
    mfix1 f (s : list A) : M _ :=
      mmatch' s with
      | [l r] l ++ r =>
        mtry
          il <- f l;
          ret (in_or_app l r x (or_introl il)) 
        with ListMtactics.NotFound =>
          ir <- f r;
          ret (in_or_app l r x (or_intror ir))
        end
      | [s'] (x :: s') => ret (in_eq _ _)
      | [y s'] (y :: s') =>
        r <- f s';
        ret (in_cons y _ _ r)
      | _ => raise ListMtactics.NotFound
      end.


Definition match_goal {A} {P} {t} (p : tpatt A P t) : M (P t) :=
  
  l <- hypotheses;
  
*)