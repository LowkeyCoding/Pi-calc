Require Import PI.cong.
Require Import PI.debruijn.
Require Import PI.labeled.
Require Import PI.unlabeled.
Require Import PI.pi.
Require Import Coq.Classes.RelationClasses.
Require Import Coq.Init.Nat.


Lemma push_pop_id: 
  forall (P : pi)(n c : nat),
  (c_pop n c (c_push 0 P)) === P.
Proof.
  intros P.
  induction P.
  - reflexivity.
  - 
  Admitted.


Lemma swap_pop1_pop:
  forall (P : pi) (n : nat),
    (c_pop n 1 (swap P)) === c_pop n 0 P.
Proof.
  intros P.
  induction P.
  - reflexivity.
  - Admitted. 

Lemma CongruentTau : 
  forall (P Q R S T : pi),
    (P === Q /\  Q -()> S /\ R === S) ->
    (exists T : pi, P -()> T /\ R === T).
Proof.
  Admitted.


Lemma PushIn :
  forall (P R : pi) (n : nat),
    P -(n)> R ->
    P -(n + 1)> R.
Proof.
  Admitted.

Lemma PushOut :
  forall (P R : pi) (n m: nat),
    P -(n , m)> R -> 
    push P -(n + 1, m + 1)> R.
Proof.
  Admitted.

Lemma ComResIn :
  forall (P Q R: pi) (n m : nat),
    Q -( n )> R ->
    Par (Out n m P) Q --> Par P (pop m R) ->
    Res (Par (Out n (m+1) (push P)) Q) --> Res (Par (push P) (pop (m+1) R)).
Proof.
  Admitted.

Lemma ComResOut :
  forall (P Q R S: pi) (n m : nat),
    P -(n+1, m+1)> R /\
    Q -(n+1)> S /\
    Par P Q --> Par R (pop (m+1) S) ->
    Res (Par P (push Q)) --> Res (Par R (push (pop m S))).
Proof.
  Admitted.

Lemma FreeCommunication :
  forall (P Q P' Q' : pi) (n m : nat),
    (P -(n , m)> P' /\ Q -(n)> Q') ->
    Par P Q --> Par P' (pop m Q').
Proof.
  intros.
  destruct H as [H1 H2].
  induction H1.
  induction H2.
  - apply RCOM.
  - apply RCON with 
    (Q:= Par (Par (Out n m P) P0) Q)
    (S:= Par (Par P (pop m R)) Q).
    + apply CParAsoc.
      reflexivity.
    + apply RPAR.
      apply IHfil.
    + apply CParAsoc.
      apply CParComp.
      reflexivity.
      apply CParComp.
      reflexivity.
      fold c_pop.
      apply push_pop_id.
  - apply RCON with 
      (Q := Res (Par ((Out (n+1) (m+1) (push P))) P0)) 
      (S := Res (Par (push P) (pop (m+1) Q))).
    + apply CSym.
      apply CExtPar.
      reflexivity.
    + apply ComResIn with 
        (n := n +1)
        (m := m)
        (P := P)
        (Q := P0)
        (R := Q).
      apply H2.
      apply IHfil.
    + apply CSym.
      apply CExtPar.
      fold c_pop.
      apply CResComp.
      apply CParComp.
      reflexivity.
      unfold pop.
      apply CSym.
      simpl.
      apply swap_pop1_pop with
        (n:= m + 1).
    - apply RCON with 
      (Q := Par (Out n m P) (Par P0 (Rep P0)))
      (S := Par P (pop m R) ).
      + apply CParComp.
        reflexivity.
        apply CParSym.
        apply CRep.
        reflexivity.
      + apply IHfil.
      + reflexivity.
    - apply RCON with
      (Q := Par (Par P Q) Q0)
      (S := Par (Par R (pop m Q')) Q0).
      + apply CSym.
        apply CParAsoc.
        apply CSym.
        apply CParAsoc.
        apply CParComp.
        reflexivity.
        apply CParSym.
        reflexivity.
      + apply RPAR.
        apply IHfol.
        apply H2.
      + apply CSym.
        apply CParAsoc.
        apply CSym.
        apply CParAsoc.
        apply CParComp.
        reflexivity.
        apply CParSym.
        reflexivity.
    - apply RCON with
      (Q := Res (Par P (push Q)))
      (S := Res (Par Q0 (push (pop m Q')))).
      + apply CSym.
        apply CParSym.
        apply CExtPar.
        apply CResComp.
        apply CParSym.
        reflexivity.
      + apply ComResOut with
          (n := n).
        split.
        apply H1.
        split.
        apply PushIn. (* Holy Fuckaroo *)
        apply H2.
        apply IHfol.
        apply PushIn. (* Holy Fuckaroo Electric bogaloo *)
        apply H2.
      + apply CSym.
        apply CParSym.
        apply CExtPar.
        apply CResComp.
        apply CParSym.
        reflexivity.
    - apply RCON with 
        (Q := Par (Par P (Rep P)) Q)
        (S := Par Q0 (pop m Q')).
      + apply CParComp.
        apply CParSym.
        apply CRep.
        reflexivity.
        reflexivity.
      + apply IHfol.
        apply H2.
      + reflexivity.
Qed.  
        
      

Lemma BoundCommunication :
  forall (P Q P' Q' : pi) (n : nat),
    (P -(n)> P' /\ Q -[n]> Q') ->
    Par P Q --> Res (Par P'  Q').
Proof.
  intros.
  destruct H as [H1 H2].
  induction H1.
  induction H2.
  - apply RCON with 
      (Q := Res (Par (In (n+1) (c_push 1 P)) P0))
      (S := Res (Par P Q )).
    +
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
      * apply CParComp. 
        apply H2.   
        reflexivity.
    +induction IHutrans.
      exists (Res x).
      destruct H0 as [H1 H2].
      split.
      * apply TRS. 
        apply H1.
      * apply CResComp. 
        apply H2.
     +induction IHutrans.
        apply CongruentTau with (Q := Q) (S := x).
        apply x. 
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
        apply FreeCommunication with (n:=n) (m:=m) (P := Q) (Q:=P) (P' := S) (Q' := R).
        split.
        apply H0.
        apply H.
        apply CParSym.
        reflexivity.
      + apply FreeCommunication with (n:=n) (m:=m) (P := P) (Q:=Q) (P' := R) (Q' := S).
        split.
        * apply H.
        * apply H0.
      + apply BoundCommunication with (n:=n).
        split.
        * apply H.
        * apply H0.
      + apply RCON with 
        (Q := Par Q P)
        (S := Res (Par S R)). 
        * apply CParSym.
          reflexivity.
        * apply BoundCommunication with (n:=n).
          split.
          apply H0.
          apply H.
        * apply CResComp.
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
