Require Import NArith Arith.
Require Import Mtac.Mtac.

Import MtacNotations.


Check (Mrun (Array.make 10 0;; ret 0)).
Check (Mrun (r <- Array.make 10 0; Array.get r 0)).
Check (Mrun (r <- Array.make 10 0; Array.set r 0 10;; Array.get r 0)).
Check (Mrun (r <- Array.make 10 0; Array.set r 9 10;; 
  e1 <- Array.get r 0; e2 <- Array.get r 9; ret (e1, e2))).

Check (Mrun (r <- Array.make 10 0; retS (Array.length r))).


Check (Mrun (r <- Array.make 10 0; Array.set r (N.of_nat 0) 1)).

Definition test_set :=
  a <- Array.make 10 0;
  let init := fix f i :=
    match i with
    | 0 =>
      Array.set a (N.of_nat i) 1
    | S i' =>
      _ <- Array.set a (N.of_nat i') (S i'); f i'
    end in
  init 10.

Check (Mrun test_set).


Definition test_array :=
  a <- Array.make 10 0;
  let init := fix f i :=
    match i with
    | 0 =>
      Array.set a (N.of_nat i) 1
    | S i' =>
      _ <- Array.set a (N.of_nat i') (S i'); f i'
    end in
  init 10;;
  let verify := fix f i :=
    match i with
    | 0 =>
      n <- Array.get a 0;
      ret (beq_nat n 1)
    | S i' =>
      b <- f i';
      n <- Array.get a (N.of_nat i');
      ret (andb b (beq_nat n (S i')))
    end in
  verify 10.

Eval compute in (Mrun test_array).

Definition test_out_of_range :=
  a <- Array.make 10 0;
  Array.get a 10.

Fail Check (Mrun test_out_of_range).

Check (Mrun (
       mtry test_out_of_range 
       with ArrayOutOfBounds => ret 0 end)).

Definition test_init :=
  a <- Array.init 10 (fun i=>ret i);
  Array.to_list a.

Check (Mrun (test_init >> retS)).


Definition basic :=
  r1 <- ref 0;
  n1 <- read r1;
  ret n1.

Check (Mrun basic).
Check (Mrun basic).

Definition basic2 :=
  r1 <- ref 0;
  _ <- write r1 10;
  read r1.

Check (Mrun basic2).

Notation "a && b" := (andb a b).

Definition test_ref :=
  r1 <- ref 0;
  r2 <- ref 1;
  r3 <- ref 2;
  r4 <- ref 3;
  r5 <- ref 4;
  r6 <- ref 5;
  _ <- write r1 10;
  _ <- write r2 11;
  _ <- write r3 12;
  _ <- write r4 13;
  _ <- write r5 14;
  _ <- write r6 15;
  v1 <- read r1;
  v2 <- read r2;
  v3 <- read r3;
  v4 <- read r4;
  v5 <- read r5;
  v6 <- read r6;
  if (beq_nat v1 10) && (beq_nat v2 11) && (beq_nat v3 12) 
    && (beq_nat v4 13) && (beq_nat v5 14) && (beq_nat v6 15) then
    print "values ok"
  else
    print "values wrong".

Definition b := Mrun test_ref.

(* Scope tests *)

Example out_of_scope : (fun z : nat => Mrun 
  mtry
    r <- ref 0;
    (nu x : nat, r ::= x);;
    !r
  with NullPointer =>
    ret z
  end)
  = @id nat.
reflexivity.
Qed.

Example not_out_of_scope : (fun z : nat => Mrun 
  mtry
    r <- ref 0;
    (nu x : nat, r ::= z);;
    !r
  with NullPointer =>
    ret 0
  end)
  = @id nat.
reflexivity.
Qed.


Example not_out_of_scope_after_out_scope : (fun z : nat => Mrun 
  mtry
    r <- ref 0;
    (nu x : nat, r ::= x;; r ::= z);;
    !r
  with NullPointer =>
    ret 1
  end)
  = @id nat.
reflexivity.
Qed.


Example out_of_scope2 : (fun z : nat => Mrun 
  mtry
    r <- ref 0;
    (nu x y : nat, r ::= x);;
    !r
  with NullPointer =>
    ret z
  end)
  = @id nat.
reflexivity.
Qed.


Example not_out_of_scope2 : (fun z : nat => Mrun 
  mtry
    r <- ref 0;
    (nu x : nat,
      (nu y : nat,
       r ::= y);;
      r ::= x);;
    r ::= z;;
    !r
  with NullPointer =>
    ret 0
  end)
  = @id nat.
reflexivity.
Qed.

Example not_out_of_scope2' : (fun z : nat => Mrun 
  mtry
    r <- ref 0;
    (nu x : nat,
      (nu y : nat,
       r ::= y);;
      r ::= x;;
      (nu y : nat,
       r ::= y);;
      r ::= x);;
    r ::= z;;
    !r
  with NullPointer =>
    ret 0
  end)
  = @id nat.
reflexivity.
Qed.

Fail Check (let r := Mrun (ref 0) in Mrun (!r)).

Check (let r := Mrun (array_make 10 0) in Mrun (a <- array_make 5 0; array_get r 0)). 
Fail Check (let r := Mrun (array_make 10 0) in Mrun (a <- array_make 5 0; array_get r 5)).

Definition broken (x : (nat * Ref nat)) :=
  e <- ref 0;
  mmatch x with
   (0, e) => ret true
  | _ => ret false
end.

Check (let x := _ in let y := Mrun (broken (0, x) ;; ret x) in y).

Fail Check (let x := _ in let y := Mrun (broken (0, x) ;; ret x) in Mrun !y).

Definition abs_array :=
  nu a : Type,  
    arr <- @array_make (option a) 10 None;
    @abs _ (fun a'=>array (option a')) a arr : M (forall a', array (option a')).

Definition should_fail_abs_array :=
  foo <- abs_array;
  array_set (foo nat) 0 (Some 1);;
  array_get (foo bool) 0.

Check should_fail_abs_array.
Fail Check (Mrun should_fail_abs_array).

Definition should_fail_abs_array' :=
  foo <- abs_array;
  nu a : Type,
  array_set (foo a) 0 (@None a);;
  _ <- array_get (foo a) 0;
  ret 0.

Fail Check (Mrun should_fail_abs_array').




Definition abs_ref a :=
  r <- @ref (option a) None;
  foo <- @abs Type (fun a'=>Ref (option a')) a r;
  foo bool ::= Some false;;
  !(foo nat).

Check abs_ref.
Fail Check (fun a=>Mrun (abs_ref a)).


Definition fine (a : Type) :=
  r <- @ref (option nat) None;
  foo <- abs a r;
  foo bool ::= Some 1;;
  !(foo nat).

Check fine.
Check (fun a=>Mrun (fine a)).

Definition will_fail :=
  r <- (nu a : nat, ref a);
  nu b:bool, !r.

Fail Check (Mrun will_fail).


(* Hit a bug in Coq, when it's fixed I'll uncomment this *)

Definition abs_val (a : Type) :=
  r <- ref a;
  foo <- abs (P:=fun _=>Ref Type) a r;
  foo bool ::= Set;;
  !(foo nat).

Check abs_val.
Check (fun a=>Mrun (abs_val a)).
(* it's fine *)

Definition not_weird2 :=
  nu A : Type,
    e <- evar A;
    @abs _ (fun x=>x) A e.

Definition not_thatweird2 :=
  foo <- not_weird2;
  foon <- retS (foo nat);
  mmatch foon with
    _ => mmatch foo bool with
         _ => ret foon
         end
  end.

Check (Mrun not_thatweird2).

Definition abs_evar (A : Type) :=
  e <- evar A;
  f <- @abs _ (fun T=>T) A e;
  retS (f nat, f bool).

Check (fun A=>Mrun (abs_evar A)).

Definition abs_evar_id (A : Type) :=
  e <- evar (A->A);
  f <- @abs _ (fun T=>T -> T) A e;
  retS (f A).

Check (fun A=>Mrun (p <- abs_evar_id A; mmatch p with (fun x=>x) => ret true | _ => raise exception end)).
    
(* Shouldn't this fail? A is transformed into a section variable, and those 
   are not checked if they appear in a Ref *)
Definition not_allowed (A : Type) :=
  Mrun (r <- @ref (option A) None; abs (P:=fun B=>Ref (option B)) A r).

Definition abs_var_incontext (A : Type) (x : A) (z : A -> Type) (w : z x)
  := r <- ref w; abs A r.

Fail Check (fun A x z w => Mrun (abs_var_incontext A x z w)).
