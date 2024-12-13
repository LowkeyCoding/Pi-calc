Require Import PI.pi.
Require Import PI.debruijn.

Inductive fitrans: pi -> nat -> pi -> Prop := 
  | IN   (n : nat) (P: pi): 
    fitrans (In n P) n P
  | PAR2 (n : nat) (P Q R : pi):
    fitrans P n R -> fitrans (Par P Q) n (Par R (push Q))
  | RES3 (n : nat) (P Q : pi) :
    fitrans P (n+1) Q -> fitrans (Res P) n (Res (swap Q))
  with fotrans : pi -> nat -> nat -> pi -> Prop :=
    | OUT   (n m : nat) (P: pi): 
      fotrans (Out n m P) n m P
    | PAR1  (n m : nat) (P Q R: pi): 
      fotrans P n m R -> fotrans (Par P Q) n m (Par R Q)
    | RES21 (n m : nat) (P Q : pi) :
      fotrans P (n+1) (m+1) Q -> 
      fotrans (Res P) n m (Res Q)
  with btrans : pi -> nat -> pi -> Prop :=
    | RES1B  (n : nat) (P R : pi):
      fotrans P  (n + 1) 0  R -> btrans (Res P) n R
    | PAR2B  (n : nat) (P Q R : pi):
      btrans P  n R -> btrans (Par P Q) n (Par R (push Q))
    | RES3B (n : nat) (P Q : pi) :
      btrans P (n+1) Q -> btrans (Res P) n (Res (swap Q))
  with tau_trans : pi -> pi -> Prop :=
    | RES22 (P Q : pi) :
      tau_trans P Q -> 
      tau_trans (Res P) (Res Q)
    | PAR12 (P Q R: pi): 
      tau_trans P R -> tau_trans (Par P Q) (Par R Q)
    | COM11  (n m : nat) (P Q R S : pi) :
      fitrans P n R ->
      fotrans Q n m S ->
      tau_trans (Par P Q) (Par (pop m R) S)
    | COM12  (n m : nat) (P Q R S : pi) :
      fotrans P n m R ->
      fitrans Q n S ->
      tau_trans (Par P Q) (Par R (pop m S))
    | COM21  (n : nat) (P Q R S : pi) :
      fitrans P n R ->
      btrans Q n S ->
      tau_trans (Par P Q) (Res (Par R S)) 
    | COM22  (n : nat) (P Q R S : pi) :
      btrans P n R ->
      fitrans Q n S ->
      tau_trans (Par P Q) (Res (Par R S)).

Notation "P -()> Q" := (tau_trans P Q) (at level 70).
Notation "P -( n , m )> Q" := (fotrans P n m Q) (at level 70).
Notation "P -( n )> Q" := (fitrans P n Q) (at level 70).
Notation "P -[ n ]> Q" := (btrans P n Q) (at level 70).

  