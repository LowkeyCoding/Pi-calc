Require Import Coq.Init.Nat.
Inductive pi : Type := 
 | Nil
 | Rep (P : pi)
 | Res (P : pi)
 | Par (P Q : pi)
 | In (n : nat) (P : pi)
 | Out (n m : nat) (P : pi).

Fixpoint swap (n : nat) (P : pi) : pi :=
  match P with
  | Nil => Nil
  | Rep Q => Rep (swap n Q)
  | Res Q => Res (swap (n+1) Q)
  | Par Q R => Par (swap n Q) (swap n R)
  | In a Q => In (if (a =? n) then (n+1) 
              else (if a =? (n+1) then n else a)) (swap (n+1) Q)
  | Out a b Q => Out (if a =? n then (n+1) else (if a =? (n+1) then n else a)) (if b =? n then (n+1) else (if b =? (n+1) then n else b)) (swap n Q)
  end.

Example swap_thing:
  swap 0 (Res (Out 1 0 (Nil))) = Res(Out 2 0 (Nil)). 
Proof. simpl. reflexivity. Qed.

Example swap_thing1:
  swap 0 (Out 1 7 (Nil)) = Out 0 7 (Nil).
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
  | CRef    (P : pi)        : cong P P 
  | CSym    (P Q : pi)      : cong P Q -> cong Q P
  | CTrans  (P Q R : pi)    : cong P Q -> cong Q R -> cong P R 
  | CParNil (P Q : pi)      : cong P Q -> cong P (Par Q Nil)
  | CNilRes                 : cong Nil (Res Nil)
  | CExt    (P Q R: pi)     : cong P (Res (Par (push Q) R))  -> cong P (Par Q (Res R ))
  | CParSym (P Q R : pi)    : cong P (Par Q R) -> cong P (Par R Q)
  | CParAsoc (P Q R S : pi) : cong P (Par Q (Par R S)) -> cong P (Par (Par Q R) S)
  | CRep (P Q : pi)         : cong Q (Rep P) -> cong Q (Par (Rep P) P)
  | CRepNil                 : cong Nil (Rep Nil)
  | CRepRep (P Q : pi)      : cong Q (Rep P) -> cong Q (Rep (Rep P))
  | CRepPar (P Q R: pi)     : cong P (Rep (Par Q R)) -> cong P (Par(Rep Q) (Rep R))
  | CParExtra (P Q R S: pi) : cong P R -> cong Q S -> cong (Par P Q) (Par R S)
  | CResExtra (P Q : pi)    : cong P Q -> cong (Res P) (Res Q)
  where "P == Q" := (cong P Q).

Reserved Notation "P --> Q" (at level 70). 
Inductive utrans: pi -> pi -> Prop :=
  | RCOM (n m: nat) (P Q : pi) : 
    utrans (Par (Out n m P) (In n Q)) (Par P (pop m 0 Q))
  | RPAR (P Q R : pi) : 
    utrans P Q -> utrans (Par P R) (Par Q R)
  | RRES (P Q : pi) : 
    utrans P Q -> utrans (Res P) (Res Q)
  | RCON (P Q R S: pi) : 
    P == Q -> 
    utrans Q S ->
    R == S ->
    utrans P R
  where "P --> Q" := (utrans P Q).

Inductive act : Set :=
  | Atau: act
  | Aout: nat -> nat -> act
  | Ain:  nat -> act
  | About: nat ->  act.

Reserved Notation "P -( a )> Q" (at level 70).
Inductive trans: pi -> act -> pi -> Prop := 
  | OUT   (n m : nat) (P: pi): trans (Out n m P) (Aout n m) P
  | IN    (n : nat) (P: pi): trans (In n P) (Ain n) P
  | PAR1  (n m : nat) (P Q R: pi): 
    trans P (Aout n m) R -> trans (Par P Q) (Aout n m) (Par R Q)
  | PAR12 (P Q R: pi): 
    trans P (Atau) R -> trans (Par P Q) (Atau) (Par R Q)
  | PAR2  (a : act) (n : nat) (P Q R : pi):
     a = (About n) \/ a = (Ain n) ->
     trans P a R -> trans (Par P Q) a (Par R (push Q))
  | RES1  (n : nat) (P R : pi):
    trans P (Aout (n + 1) 0 ) R -> trans (Res P) (About n) R
  | RES21 (n m : nat) (P Q : pi) :
     trans P (Aout (n + 1) (m + 1)) Q -> 
     trans (Res P) (Aout n m) (Res Q)
  | RES22 (P Q : pi) :
    trans P (Atau) Q -> 
    trans (Res P) (Atau) (Res Q)
  | RES3 (a: nat -> act) (n : nat) (P Q : pi) :
    a = Ain \/ a = About ->
    trans P (a (n+1)) Q -> trans (Res P) (a n) (Res (swap 0 Q))
  | COM11  (n m : nat) (P Q R S : pi) :
    trans P (Ain n) R ->
    trans Q (Aout n m) S ->
    trans (Par P Q) Atau (Par (pop m 0 R) S)
  | COM12  (n m : nat) (P Q R S : pi) :
    trans P (Aout n m) R ->
    trans Q (Ain n) S ->
    trans (Par P Q) Atau (Par R (pop m 0 S))
  | COM21  (n : nat) (P Q R S : pi) :
    trans (Par P Q) Atau (Res (Par R S)) ->
    trans P (Ain n) R ->
    trans Q (About n) S 
  | COM22  (n : nat) (P Q R S : pi) :
    trans P (About n) R ->
    trans Q (Ain n) S ->
    trans (Par P Q) Atau (Res (Par R S))
  | REP   (a : act) (P Q: pi) : 
    trans (Par P (Rep P)) a Q -> trans (Rep P) a Q
  where "P -( a )> Q" := (trans P a Q).

Theorem tau_proc :
  forall (J K : pi ),
    (J -(Atau)> K) -> (exists L : pi, J --> L).
Proof.
  intros.
  Admitted.


Theorem test : 
  forall (J K : pi),
    (J --> K) -> (exists L : pi, J -(Atau)> L /\ K == L).
Proof.
  intros.
  induction H.
  - exists (Par P (pop m 0 Q)).
    split.
    apply COM12 with (n:= n).
    apply OUT.
    apply IN.
    reflexivity.
  - induction IHutrans.
    exists (Par x R). 
    split.
    apply PAR12.
    destruct H0 as [H1 H2].
    apply H1.
    apply CParExtra.
    destruct H0 as [H1 H2].
    apply H2.
    apply CRef.
  - induction IHutrans.
     exists (Res x).
     split.
     apply RES22.
     destruct H0 as [H1 H2].
     apply H1.
     destruct H0 as [H1 H2].
     apply CResExtra.
     apply H2.
  - induction IHutrans.
    induction H.
    * exists x.
      destruct H2 as [H3 H4].
      split.
      apply H3.
      apply CTrans with(Q:= S).
      apply H1.
      apply H4.
   * exists x.
      destruct IHcong.
      destruct H2 as [H3 H4].
      apply RCON with (Q:= P) (S:=S).
      apply CSym. 
      apply H.
      apply H0.
      apply CRef.
      split.
      Admitted.

Example test_nil:
  Res Nil == Nil .
Proof.
  apply CSym. apply CNilRes. Qed.

Example com11test:
  Par (In 7 Nil) (Out 7 4 Nil) -(Atau)> Par (pop 4 0 Nil) (Nil).
Proof. 
 apply COM11 with (n:= 7). apply IN. apply OUT. Qed.

Example com12test:
  Par (Out 7 4 Nil) (In 7 Nil) -(Atau)> Par (Nil) (pop 4 0 Nil).
Proof.
  apply COM12 with (n:= 7). apply OUT. apply IN. Qed.
Example butstuff: 
  Par (Res (Out 7 0 Nil)) (In 9 Nil) -(About 6)> Par Nil (push (In 9 Nil)).
Proof.
 apply PAR2 with (n:= 6). left. reflexivity. apply RES1. apply OUT. Qed.

Example test_nil_par:
  Par Nil (In 0 Nil) == In 0 Nil.
Proof.
  apply CSym. 
  apply CParSym.
  apply CParNil.
  apply CRef. Qed.

Example test_rep:
  Rep (In 0 Nil) ==  Par (Rep (In 0 Nil)) (In 0 Nil).
Proof.
  apply CRep. apply CRef. Qed.