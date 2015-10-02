Require Export Mtac.Mtac.
Import MtacNotations.

Require Import List.
Import ListNotations.


Inductive pattern A (B : A -> Type) (t : A) : Prop := 
| pbase : forall (x:A) (b : t = x -> Mtac (B x)), Unification -> pattern A B t
| ptele : forall {C}, (forall (x : C), pattern A B t) -> pattern A B t.


Definition NotUnifiableException {A} (x y : A) : Exception. exact exception. Qed.
Definition munify A (x y : A) (P : A -> Type) (f : x = y -> M (P y)) : M (P x) 
  := mmatch x with y => [H] f H | _ => raise (NotUnifiableException x y) end.
Arguments munify {A} x y P f.

Definition open_pattern {A} {P:A->Type} {t:A}  :=
  mfix1 op (p : pattern A P t) : M (pattern A P t) :=
    match p return M _ with
    | pbase _ _ _ x f u => ret p : M (pattern _ _ _)
    | @ptele _ _ _ C f =>
      e <- evar C; op (f e)
    end.

Definition NoPatternMatches : Exception. exact exception. Qed.
Definition Anomaly : Exception. exact exception. Qed.

Fixpoint mmatch' {A P} t (ps : list (pattern A P t)) : M (P t) :=
  match ps with
  | [] => raise NoPatternMatches
  | (p :: ps') => 
    p' <- open_pattern p;
    mtry 
      match p' with
      | pbase _ _ _ t' f u => 
        munify t t' P f : M (P t)
      | _ => raise Anomaly
      end
    with [? A (x y:A)] NotUnifiableException x y =>
      mmatch' t ps'
    end
  end.

Arguments ptele {A B t C} f.
Arguments pbase {A B t} x b u.

Notation "[? x .. y ] ps" := (ptele (fun x=> .. (ptele (fun y=>ps)).. ))
  (at level 202, x binder, y binder, ps at next level) : mtac_pattern_scope.
Notation "p => b" := (pbase p%core (fun _=>b%core) UniRed) 
  (no associativity, at level 201) : mtac_pattern_scope. 
Notation "p => [ H ] b" := (pbase p%core (fun H=>b%core) UniRed) 
  (no associativity, at level 201, H at next level) : mtac_pattern_scope. 
Notation "'_' => b " := (ptele (fun x=> pbase x (fun _=>b%core) UniRed)) 
  (at level 201, b at next level) : mtac_pattern_scope.

Delimit Scope mtac_pattern_scope with mtac_pattern.

Notation "'with' | p1 | .. | pn 'end'" := 
  ((cons p1%mtac_pattern (.. (cons pn%mtac_pattern nil) ..)))
    (at level 91, p1 at level 210, pn at level 210).
Notation "'with' p1 | .. | pn 'end'" := 
  ((cons p1%mtac_pattern (.. (cons pn%mtac_pattern nil) ..)))
    (at level 91, p1 at level 210, pn at level 210).

Notation "'mmatch' x ls" := (mmatch' x ls).



(* Test *)
  Definition NotFound : Exception.
    exact exception.
  Qed.

Definition inl' A (x : A) : forall l : list A, M (In x l) :=
  mfix1 f (l : list A) : M (In x l) :=
  mmatch l with
  | [? l r] l ++ r =>
      ttry (
        il <- f l;
        ret (in_or_app l r x (or_introl il)) )
      (fun e=>mmatch e with NotFound =>
        ir <- f r;
        ret (in_or_app l r x (or_intror ir))
      end)
  | [? s] (x :: s) => ret (in_eq _ _)
  | [? y s] (y :: s) => r <- f s; ret (in_cons y _ _ r)
  | _ => raise NotFound
  end.

Example testM (
x01 x11 x21 x31 x41 x51 x61 x71 x81 x91 
x02 x12 x22 x32 x42 x52 x62 x72 x82 x92 
x03 x13 x23 x33 x43 x53 x63 x73 x83 x93 
x04 x14 x24 x34 x44 x54 x64 x74 x84 x94 
x05 x15 x25 x35 x45 x55 x65 x75 x85 x95 
x06 x16 x26 x36 x46 x56 x66 x76 x86 x96 
x07 x17 x27 x37 x47 x57 x67 x77 x87 x97 
x08 x18 x28 x38 x48 x58 x68 x78 x88 x98 
x09 x19 x29 x39 x49 x59 x69 x79 x89 x99 
 : nat) : In x99 [
x01;x11;x21;x31;x41;x51;x61;x71;x81;x91;
x02;x12;x22;x32;x42;x52;x62;x72;x82;x92;
x03;x13;x23;x33;x43;x53;x63;x73;x83;x93;
x04;x14;x24;x34;x44;x54;x64;x74;x84;x94;
x05;x15;x25;x35;x45;x55;x65;x75;x85;x95;
x06;x16;x26;x36;x46;x56;x66;x76;x86;x96;
x07;x17;x27;x37;x47;x57;x67;x77;x87;x97;
x08;x18;x28;x38;x48;x58;x68;x78;x88;x98;
x09;x19;x29;x39;x49;x59;x69;x79;x89;x99
].
Proof.
  Time rrun (inl' _ _ _).  
Qed.

Require Import Mtac.Mtactics.
Example testo (
x01 x11 x21 x31 x41 x51 x61 x71 x81 x91 
x02 x12 x22 x32 x42 x52 x62 x72 x82 x92 
x03 x13 x23 x33 x43 x53 x63 x73 x83 x93 
x04 x14 x24 x34 x44 x54 x64 x74 x84 x94 
x05 x15 x25 x35 x45 x55 x65 x75 x85 x95 
x06 x16 x26 x36 x46 x56 x66 x76 x86 x96 
x07 x17 x27 x37 x47 x57 x67 x77 x87 x97 
x08 x18 x28 x38 x48 x58 x68 x78 x88 x98 
x09 x19 x29 x39 x49 x59 x69 x79 x89 x99 
 : nat) : In x99 [
x01;x11;x21;x31;x41;x51;x61;x71;x81;x91;
x02;x12;x22;x32;x42;x52;x62;x72;x82;x92;
x03;x13;x23;x33;x43;x53;x63;x73;x83;x93;
x04;x14;x24;x34;x44;x54;x64;x74;x84;x94;
x05;x15;x25;x35;x45;x55;x65;x75;x85;x95;
x06;x16;x26;x36;x46;x56;x66;x76;x86;x96;
x07;x17;x27;x37;x47;x57;x67;x77;x87;x97;
x08;x18;x28;x38;x48;x58;x68;x78;x88;x98;
x09;x19;x29;x39;x49;x59;x69;x79;x89;x99
].
Proof.
  Time rrun (ListMtactics.inlist _ _).  
Qed.