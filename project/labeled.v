Require Import PI.pi.
Require Import PI.debruijn.

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