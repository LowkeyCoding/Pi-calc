Require Import PI.cong.
Require Import PI.debruijn.
Require Import PI.labeled.
Require Import PI.unlabeled.
Require Import PI.pi.
Require Import Coq.Classes.RelationClasses.

Theorem tau_proc :
  forall (J K : pi ),
    (J -(Atau)> K) -> (exists L : pi, J --> L).
Proof.
  intros.
  Admitted.


Theorem test : 
  forall (J K : pi),
    (J --> K) -> (exists L : pi, J -(Atau)> L /\ K === L).
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
  Res Nil === Nil .
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
  Par Nil (In 0 Nil) === In 0 Nil.
Proof.
  apply CSym. 
  apply CParSym.
  apply CParNil.
  apply CRef. Qed.

Example test_rep:
  Rep (In 0 Nil) ===  Par (Rep (In 0 Nil)) (In 0 Nil).
Proof.
  apply CRep. apply CRef. Qed.