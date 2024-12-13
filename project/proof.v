Require Import PI.cong.
Require Import PI.debruijn.
Require Import PI.labeled.
Require Import PI.unlabeled.
Require Import PI.pi.
Require Import Coq.Classes.RelationClasses.
Require Import Coq.Init.Nat.

Lemma one : 
  forall (P Q R S T : pi),
    (P === Q /\  Q -()> S /\ R === S) ->
    (exists T : pi, P -()> T /\ R === T).
Proof.
  Admitted.

Lemma two :
  forall (P Q P' Q' : pi) (n m : nat),
    (P -(n , m)> P' /\ Q -(n)> Q') ->
    Par P Q --> Par P' (pop m Q').
Proof.
  Admitted.


Lemma three :
  forall (P Q P' Q' : pi) (n : nat),
    (P -(n)> P' /\ Q -[n]> Q') ->
    Par P Q --> Res (Par P'  Q').
Proof.
    Admitted.


Theorem equiv_trans :
  forall (P P' : pi),
    (P --> P' -> (exists R : pi, P -()> R /\ P' === R)) /\
    (P -()> P' -> P --> P').
Proof.
  intros.
  split.
  - intros.
    induction H.
    + exists (Par P (pop m Q)).
      split.
      apply TSFL with 
        (n := n).
      apply FO.
      apply FI.
      reflexivity.
    + induction IHutrans.
      exists (Par x R).
      destruct H0 as [H1 H2].
      split.
      * apply TPR. 
        apply H1.
      * apply CParExtra. 
        apply H2.   
        reflexivity.
    +induction IHutrans.
      exists (Res x).
      destruct H0 as [H1 H2].
      split.
      * apply TRS. 
        apply H1.
      * apply CResExtra. 
        apply H2.
     +induction IHutrans.
        apply one with (Q := Q) (S := x).
        apply x. (*Hmmmmmmmmmmm*)
        split.
        apply H.
        destruct H2 as [H2 H3].
        split.
        * apply H2.
        * apply CTrans with (Q:= S).
          apply H1.
          apply H3.
  - intros.
    induction H.
      + apply RCON with (Q := Par Q P) (S := Par S (pop m R)).
        apply CParSym.
        reflexivity.
        apply two with (n:=n) (m:=m) (P := Q) (Q:=P) (P' := S) (Q' := R).
        split.
        apply H0.
        apply H.
        apply CParSym.
        reflexivity.
      + apply two with (n:=n) (m:=m) (P := P) (Q:=Q) (P' := R) (Q' := S).
        split.
        * apply H.
        * apply H0.
      + apply three with (n:=n).
        split.
        * apply H.
        * apply H0.
      + apply RCON with 
        (Q := Par Q P)
        (S := Res (Par S R)). 
        * apply CParSym.
          reflexivity.
        * apply three with (n:=n).
          split.
          apply H0.
          apply H.
        * apply CResExtra.
          apply CParSym.
          reflexivity.
      + apply RPAR.
        apply IHtsl.
      + apply RCON with
        (Q := Par Q P)
        (S := Par R P).
        * apply CParSym.
          reflexivity.
        * apply RPAR.
          apply IHtsl.
        * apply CParSym.
          reflexivity.
      + apply RRES.
        apply IHtsl.
      + apply RCON with 
        (Q := (Par P (Rep P)))
        (S := R).
        * apply CParSym.
          apply CRep.
          reflexivity.
        * apply IHtsl.
        * reflexivity.
  Qed.