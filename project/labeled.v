Require Import PI.pi.
Require Import PI.debruijn.

Inductive fil : pi -> nat -> pi -> Prop := 
  | FI (P : pi) (n : nat) : 
    fil (In n P) n P
  | FIP (P Q  R: pi) (n : nat) :
    fil P n R -> 
    fil (Par P Q) n (Par R (push Q))
  | FIRS (P Q R : pi) (n : nat) :
    fil P (n+1) Q -> 
    fil (Res P) n (Res (swap Q)) (* (1) Correct bu causes issues *)
  | FIRP (P Q R : pi) (n : nat) :
    fil (Par P (Rep P)) n R -> fil (Rep P) n R.

Inductive fol : pi -> nat -> nat -> pi -> Prop :=
  | FO (P : pi) (n m : nat) :
    fol (Out n m P) n m P
  | FOP (P Q R : pi) (n m : nat) :
    fol P n m R -> 
    fol (Par P Q) n m (Par R Q)
  | FORS (P Q: pi) (n m : nat) :
    fol P (n+1) (m+1) Q -> 
    fol (Res P) n m (Res Q)
  | FORP (P Q : pi) (n m : nat) :
    fol (Par P (Rep P)) n m Q -> 
    fol (Rep P) n m Q.

Inductive bol : pi -> nat -> pi -> Prop :=
  | BRSC (P Q: pi) (n : nat) :
    fol P  (n + 1) 0  Q -> 
    bol (Res P) n Q
  | BRSU (P Q : pi) (n : nat) :
    bol P n Q ->  
    bol (Res P) n (Res (swap Q))
  | BPL (P Q R : pi ) (n : nat) :
    bol P n R ->
    bol (Par P Q) n (Par R (push Q))
  | BRP (P Q : pi) (n : nat) :
    bol (Par P (Rep P)) n Q -> 
    bol (Rep P) n Q.

Inductive tsl : pi -> pi -> Prop := 
  | TSFR (P Q R S : pi) (n m : nat):
    fil P n R ->
    fol Q n m S ->
    tsl (Par P Q) (Par (pop m R) S)
  | TSFL (P Q R S : pi) (n m : nat):
    fol P n m R ->
    fil Q n S ->
    tsl (Par P Q) (Par R (pop m S))
  | TSBR (P Q R S : pi) (n : nat) :
    fil P n R ->
    bol Q n S ->
    tsl (Par P Q ) (Res (Par R S))
  | TSBL (P Q R S : pi) (n m : nat):
    bol P n R ->
    fil Q n S ->
    tsl (Par P Q ) (Res (Par R S))
  | TPR (P Q R : pi) :
    tsl P R ->
    tsl (Par P Q) (Par R  Q)
  | TPL (P Q R : pi) :
    tsl Q R ->
    tsl (Par P Q) (Par P R)
  | TRS (P R : pi) :
    tsl P R -> 
    tsl (Res P) (Res R)
  | TRP (P R: pi) :
    tsl (Par P (Rep P)) R -> 
    tsl (Rep P) R.

Notation "P -( n )> Q" := (fil P n Q) (at level 70).
Notation "P -( n , m )> Q" := (fol P n m Q) (at level 70).
Notation "P -[ n ]> Q" := (bol P n Q) (at level 70).
Notation "P -()> Q" := (tsl P Q) (at level 70).