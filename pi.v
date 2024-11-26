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
  | CNilPar (P Q : pi): cong P Q -> cong P (Par Q Nil)
  | CNilRes:  cong Nil (Res Nil)
  | CParRef (P Q R : pi):  cong P (Par Q R) -> cong P (Par Q P)
  | CParAsoc (P Q R S : pi): cong P (Par Q (Par R S)) -> cong P (Par (Par Q R) S)
  | CRep (P Q : pi): cong Q (Rep P) -> cong Q (Par (Rep P) P)
  | CRepNil : cong Nil (Rep Nil)
  | CRepRep (P Q : pi): cong Q (Rep P) -> cong Q (Rep (Rep P))
  | CRepPar (P Q R: pi): cong P (Rep (Par Q R)) -> cong P (Par(Rep Q) (Rep R))
  where "P == Q" := (cong P Q).


Example test:
  Res Nil == Nil.
Proof.
  apply CSym. apply CNilRes. Qed.