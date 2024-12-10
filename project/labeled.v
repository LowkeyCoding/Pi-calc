Require Import PI.pi.
Require Import PI.debruijn.

Inductive act : Set :=
  | Aout: nat -> nat -> act
  | Ain:  nat -> act
  | About: nat ->  act.

Inductive trans: pi -> act -> pi -> Prop := 
  | OUT   (n m : nat) (P: pi): trans (Out n m P) (Aout n m) P
  | IN    (n : nat) (P: pi): trans (In n P) (Ain n) P
  | PAR1  (n m : nat) (P Q R: pi): 
    trans P (Aout n m) R -> trans (Par P Q) (Aout n m) (Par R Q)
  | PAR2  (a : act) (n : nat) (P Q R : pi):
     a = (About n) \/ a = (Ain n) ->
     trans P a R -> trans (Par P Q) a (Par R (push Q))
  | RES1  (n : nat) (P R : pi):
    trans P (Aout (n + 1) 0 ) R -> trans (Res P) (About n) R
  | RES21 (n m : nat) (P Q : pi) :
     trans P (Aout (n + 1) (m + 1)) Q -> 
     trans (Res P) (Aout n m) (Res Q)
  | RES3 (a: nat -> act) (n : nat) (P Q : pi) :
    a = Ain \/ a = About ->
    trans P (a (n+1)) Q -> trans (Res P) (a n) (Res (swap 0 Q))
  | REP   (a : act) (P Q: pi) : 
    trans (Par P (Rep P)) a Q -> trans (Rep P) a Q
  with tau_trans : pi -> pi -> Prop :=
  | RES22 (P Q : pi) :
    tau_trans P Q -> 
    tau_trans (Res P) (Res Q)
  | PAR12 (P Q R: pi): 
    tau_trans P R -> tau_trans (Par P Q) (Par R Q)
  | COM11  (n m : nat) (P Q R S : pi) :
    trans P (Ain n) R ->
    trans Q (Aout n m) S ->
    tau_trans (Par P Q) (Par (pop m 0 R) S)
  | COM12  (n m : nat) (P Q R S : pi) :
    trans P (Aout n m) R ->
    trans Q (Ain n) S ->
    tau_trans (Par P Q) (Par R (pop m 0 S))
  | COM21  (n : nat) (P Q R S : pi) :
    trans P (Ain n) R ->
    trans Q (About n) S ->
    tau_trans (Par P Q) (Res (Par R S)) 
  | COM22  (n : nat) (P Q R S : pi) :
    trans P (About n) R ->
    trans Q (Ain n) S ->
    tau_trans (Par P Q) (Res (Par R S)).

Notation "P -()> Q" := (tau_trans P Q) (at level 70).
Notation "P -( a )> Q" := (trans P a Q) (at level 70).