Require Import PI.cong.
Require Import PI.debruijn.
Require Import PI.labeled.
Require Import PI.unlabeled.
Require Import PI.pi.
Require Import Coq.Classes.RelationClasses.
Require Import Coq.Init.Nat.

Lemma one : 
  forall (P Q R Z T : pi),
    (P === Q /\  Q -()> Z /\ R === Z) ->
    (exists T : pi, P -()> T /\ R === T).
Proof.
  Admitted.

Lemma two :
  forall (P Q P' Q' : pi) (n m : nat),
    P -(Aout n m)> P' /\ Q -(Ain m)> Q' ->
    Par P Q --> Par P' Q'.
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
    * exists (Par P (pop m 0 Q)).
      split.
      apply COM12 with (n:= n).
      apply OUT.
      apply IN.
      reflexivity.
    * induction IHutrans.
      exists (Par x R).
      destruct H0 as [H1 H2].
      split.
      apply PAR12. (*branch 1 *)
      apply H1.
      apply CParExtra. 
      apply H2.   (* branch 2 *)
      reflexivity.
    * induction IHutrans.
      exists (Res x).
      destruct H0 as [H1 H2].
      split.
      apply RES22. (* Branch 1 *)
      apply H1.
      apply CResExtra. 
      apply H2. (* branch 2 *)
     * induction IHutrans.
        apply one with (Q := Q) (Z := x).
        apply x. (*Hmmmmmmmmmmm*)
        split.
        apply H.
        destruct H2 as [H2 H3].
        split.
        apply H2.
        apply CTrans with (Q:= S).
        apply H1.
        apply H3.
  - intros.
    induction H.
      * apply RRES.
        apply IHtau_trans.
      * apply RPAR.
        apply IHtau_trans.
      * Admitted.
      