Require Import Arith Lists.List NArith.
Import ListNotations.

Require Import Mtac.Mtac.
Require Import Mtac.Mtactics.
Import MtacNotations.

Module HashTbl.

  Definition t A (P : A -> Type) := (Ref N * Ref (array (list (sigT P))))%type.

  Definition initial_size := 16%N.
  Definition inc_factor := 2%N.
  Definition threshold := 7%N.

  Definition NotFound : Exception.
    exact exception.
  Qed.

  Definition create A B : M (t A B) :=
    n <- ref 0%N;
    a <- Array.make initial_size nil;
    ra <- ref a;
    ret (n, ra).

  
  Definition quick_add {A P} (a : Array.t (list (sigT P))) (x : A) (y : P x) : M unit :=
    let n := Array.length a in
    i <- hash x n;
    l <- Array.get a i;
    Array.set a i (existT _ x y  :: l).
  
  Definition iter {A B} (h : t A B) (f : forall x : A, B x -> M unit) : M unit :=
    let (_, ra) := h in
    a <- !ra;
    Array.iter a (fun _ l =>
      fold_right (fun k r => r;;
         match k with
           existT _ x y => f x y
         end) (ret tt) l).

  Definition expand {A B} (h : t A B) : M unit :=
    let (_, ra) := h in
    a <- !ra;
    let size := Array.length a in
    let new_size := (size * inc_factor)%N in
    new_a <- Array.make new_size nil;
    iter h (fun x y=> quick_add new_a x y);;
    ra ::= new_a.
        

  (* There is no order on the elements *)
  Definition to_list {A B} (h : t A B) :=
    rl <- ref nil;
    HashTbl.iter h (fun x y => l <- !rl; rl ::= (existT _ x y :: l));;
    !rl.

  (* debugging function to test how big is the biggest bucket *)
  Definition max_bucket {A B} (h : t A B) :=
    let (_, ra) := h in
    a <- !ra;
    max <- ref 0;
    Array.iter a (fun _ l => 
        prev <- !max;
        let size := List.length l in
        if leb prev size then
          max ::= size
        else
          ret tt);;
    !max.
    

  Definition add {A B} (h : t A B) (x : A) (y : B x) :=
    let (rl, ra) := h in
    load <- !rl;
    a <- !ra;
    let size := Array.length a in
    (if (threshold * size <=? 10 * load)%N then
      expand h
    else
      ret tt);;
    a <- !ra;
    quick_add a x y;;
    new_load <- retS (N.succ load);
    rl ::= new_load.

  Definition find {A B} (h : t A B) (x : A) : M (B x) :=
    let (_, ra) := h in
    a <- !ra;
    let size := Array.length a in
    i <- hash x size;
    l <- Array.get a i;
    mtry
      ListMtactics.find x l
    with ListMtactics.NotFound =>
      raise NotFound
    end.

  Definition remove {A B} (h : t A B) (x : A) : M unit :=
    let (rl, ra) := h in
    a <- !ra;
    let size := Array.length a in
    i <- hash x size;
    l <- Array.get a i;
    l' <- ListMtactics.remove x l;
    Array.set a i l';;
    load <- !rl;
    new_load <- retS (N.pred load);
    rl ::= new_load.
    
  
End HashTbl.
