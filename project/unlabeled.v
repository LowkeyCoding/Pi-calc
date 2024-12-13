Require Import PI.pi.
Require Import PI.cong.
Require Import PI.debruijn.

Reserved Notation "P --> Q" (at level 70). 
Inductive utrans: pi -> pi -> Prop :=
  | RCOM (n m: nat) (P Q : pi) : 
    utrans (Par (Out n m P) (In n Q)) (Par P (pop m Q))
  | RPAR (P Q R : pi) : 
    utrans P Q -> utrans (Par P R) (Par Q R)
  | RRES (P Q : pi) : 
    utrans P Q -> utrans (Res P) (Res Q)
  | RCON (P Q R S: pi) : 
    P === Q -> 
    utrans Q S ->
    R === S ->
    utrans P R
  where "P --> Q" := (utrans P Q).