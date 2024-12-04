Require Import Coq.Init.Nat.

Inductive pi : Type := 
 | Nil
 | Rep (P : pi)
 | Res (P : pi)
 | Par (P Q : pi)
 | In (n : nat) (P : pi)
 | Out (n m : nat) (P : pi).

Fixpoint swap (P : pi) : pi :=
  match P with
  | Nil => Nil
  | Rep Q => Rep (swap Q)
  | Res Q => Res (swap Q)
  | Par Q R => Par (swap Q) (swap R)
  | In 0 Q => In 1 (swap Q)
  | In 1 Q => In 0 (swap Q)
  | Out 0 0 Q => Out 1 1 (swap Q)
  | Out 1 1 Q => Out 0 0 (swap Q)
  | Out 0 1 Q => Out 1 0 (swap Q)
  | Out 1 0 Q => Out 0 1 (swap Q)
  | Out 0 n Q => Out 1 n (swap Q)
  | Out n 0 Q => Out n 1 (swap Q)
  | Out 1 n Q => Out 0 n (swap Q)
  | Out n 1 Q => Out n 0 (swap Q)
  | In n Q => In n (swap Q)
  | Out n m Q => Out n m (swap Q)
  end.

Example swap_thing:
  swap (Res (Out 1 0 (Nil))) = Res(Out 0 1 (Nil)). 
Proof. simpl. reflexivity. Qed.

Example swap_thing1:
  swap (Res (Out 1 7 (Nil))) = Res(Out 0 7 (Nil)).
Proof. simpl. reflexivity. Qed.

Fixpoint push (P : pi) : pi := 
  match P with 
  | Nil => Nil
  | Par Q R => Par (push Q) (push R)
  | Res Q => Res (push Q)
  | In n Q => In (n+1) (push Q)
  | Out n m Q => Out (n+1) (m+1) (push Q)
  | Rep Q => Rep (push Q)
  end.

(*Notation "'popN' n t c" :=
  (if (leb n c) then n - 1 else (if (eqb n c) then t else n))(at level 200).
*)

Definition popN (n t c : nat) : nat :=
  (if (ltb c n) then n - 1 else (if (eqb n c) then t else n)) .

Fixpoint pop (n c: nat) (P : pi) : pi :=
 match P with
  | Nil => Nil
  | Par Q R => Par (pop n c Q) (pop n c R)
  | Rep Q => Rep (pop n c Q) 
  | Out m o Q => Out (popN m n c) (popN o n c) (pop n c Q)
  | In m Q => In (popN m n c) (pop (n+1) (c+1) Q)
  | Res Q => Res (pop (n+1) (c+1) Q)
  end.

Example pop_thing1:
  pop 4 0 (Res (Out 1 0 (Nil))) = Res(Out 5 0 (Nil)). 
Proof. simpl. unfold popN. simpl. reflexivity. Qed.


Example pop_thing2:
  pop 4 0 (In 0 (Res (Out 1 0 (Nil)))) = In 4 (Res(Out 1 0 (Nil))). 
Proof. simpl. unfold popN. simpl. reflexivity. Qed.

Reserved Notation "P == Q" (at level 70).

Inductive cong : pi -> pi -> Prop :=
  | CRef (P : pi): cong P P 
  | CSym (P Q : pi): cong P Q -> cong Q P
  | CTrans (P Q R : pi): cong P Q -> cong Q R -> cong P R
  | CParNil (P Q : pi): cong P Q -> cong P (Par Q Nil)
  | CNilRes:  cong Nil (Res Nil)
  | CParRef (P Q R : pi):  cong P (Par Q R) -> cong P (Par R Q)
  | CParAsoc (P Q R S : pi): cong P (Par Q (Par R S)) -> cong P (Par (Par Q R) S)
  | CRep (P Q : pi): cong Q (Rep P) -> cong Q (Par (Rep P) P)
  | CRepNil : cong Nil (Rep Nil)
  | CRepRep (P Q : pi): cong Q (Rep P) -> cong Q (Rep (Rep P))
  | CRepPar (P Q R: pi): cong P (Rep (Par Q R)) -> cong P (Par(Rep Q) (Rep R))
  where "P == Q" := (cong P Q).

Inductive act : Set :=
  | Atau: act
  | Aout: nat -> nat -> act
  | Ain:  nat -> act
  | About: nat ->  act.


Reserved Notation "P -( a )> Q" (at level 70).
Inductive trans: pi -> act -> pi -> Prop := 
  | OUT   (n m : nat) (P: pi): trans (Out n m P) (Aout n m) P
  | IN    (n : nat) (P: pi): trans (In n P) (Ain n) P
  | PAR1  (a : act) (n m : nat) (P Q R: pi): 
    (a = Atau) \/ (a = Aout n m) -> 
    trans P a R -> trans (Par P Q) a (Par R Q)
  | PAR2  (a : act) (n : nat) (P Q R : pi):
     a = (About n) \/ a = (Ain n) ->
     trans P a R -> trans (Par P Q) a (Par R (push Q))
  | RES1  (n : nat) (P R : pi):
    trans P (Aout (n + 1) 0 ) R -> trans (Res P) (About n) R
  | COM1  (n m : nat) (P Q R S: pi) :
    trans P (Ain n) R ->
    trans Q (Aout n m) S ->
    trans (Par P Q) Atau (Par (pop m 0 R) S)
  where "P -( a )> Q" := (trans P a Q).

Example test_nil:
  Res Nil == Nil .
Proof.
  apply CSym. apply CNilRes. Qed.

Example random:
  Par (In 7 Nil) (Out 7 4 Nil) -(Atau)> Par (pop 4 0 Nil) (Nil).
Proof. 
 apply COM1 with (n:= 7). apply IN. apply OUT. Qed.
Example butstuff: 
  Par (Res (Out 7 0 Nil)) (In 9 Nil) -(About 6)> Par Nil (push (In 9 Nil)).
Proof.
 apply PAR2 with (n:= 6). left. reflexivity. apply RES1. apply OUT. Qed.

Example test_nil_par:
  Par Nil (In 0 Nil) == In 0 Nil.
Proof.
  apply CSym. 
  apply CParRef.
  apply CParNil.
  apply CRef. Qed.

Example test_rep:
  Rep (In 0 Nil) ==  Par (Rep (In 0 Nil)) (In 0 Nil).
Proof.
  apply CRep. apply CRef. Qed.






