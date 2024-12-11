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
  intros.
  destruct H as [H1 H2].
  destruct H2 as [H2 H3].
  induction H2.
  Admitted.

Lemma two :
  forall (P Q P' Q' : pi) (n m : nat),
    (P -(n , m)> P' /\ Q -(n)> Q') ->
    Par P Q --> Par P' (pop m 0  Q').
Proof.
  intros.
  destruct H as [H1 H2].
  induction H1.
  - induction H2. 
    + apply RCOM.
    + apply RCON with (Q:= Par (Par (Out n m P) P0) Q) (S := Par (Par P (pop m 0 R)) Q). 
      apply CParAsoc.
      reflexivity.
      apply RPAR.
      apply IHfitrans.
      simpl.
      apply CParAsoc.      
      apply CParExtra.
      reflexivity.
      apply CParExtra.
      reflexivity.
      apply CPushPop.
      reflexivity.
    + 
    
    apply RCON with 
        (Q := Res (Par (push 0 (Out n m P)) P0)) 
        (S := Res (Par (push 0 P) (pop (m+1) 0 Q))).
      * apply CSym.
        apply CExt.
        reflexivity.
      * simpl.
        apply RRES.
        assert (P0 === (In (n+1) Q)).
        apply

        apply RCOM with 
          (n := n +1)
          (m := m +1)
          (P := push 0 P)
          (Q := Q).

        


Lemma three :
  forall (P Q P' Q' : pi) (n : nat),
    (P -(Ain n)> P' /\ Q -(About n)> Q') ->
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
    + exists (Par P (pop m 0 Q)).
      split.
      apply COM12 with (n:= n).
      apply OUT.
      apply IN.
      reflexivity.
    + induction IHutrans.
      exists (Par x R).
      destruct H0 as [H1 H2].
      split.
      * apply PAR12. 
        apply H1.
      * apply CParExtra. 
        apply H2.   
        reflexivity.
    +induction IHutrans.
      exists (Res x).
      destruct H0 as [H1 H2].
      split.
      * apply RES22. 
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
      + apply RRES.
        apply IHtau_trans.
      + apply RPAR.
        apply IHtau_trans.
      + apply RCON with (Q := Par Q P) (S := Par S (pop m 0 R)).
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
      + apply RCON with (Q := Par Q P) (S := Res (Par S R)). 
        * apply CParSym.
          reflexivity.
        * apply three with (n:=n).
          split.
          apply H0.
          apply H.
        * apply CResExtra.
          apply CParSym.
          reflexivity.
  Qed.