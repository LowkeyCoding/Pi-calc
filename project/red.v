Require Import PI.pi.
Require Import PI.cong.
Require Import PI.debruijn.

Reserved Notation "P --> Q" (at level 70). 
Inductive red: pi -> pi -> Prop :=
  | RCOM (n m: nat) (P Q : pi) : 
    red (Par (Out n m P) (In n Q)) (Par P (pop m Q))
  | RPAR (P Q R : pi) : 
    red P Q -> red (Par P R) (Par Q R)
  | RRES (P Q : pi) : 
    red P Q -> red (Res P) (Res Q)
  | RCON (P Q R S: pi) : 
    P === Q -> 
    red Q S ->
    R === S ->
    red P R
  where "P --> Q" := (red P Q).