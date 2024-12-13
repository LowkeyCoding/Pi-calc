Require Import PI.cong.
Require Import PI.debruijn.
Require Import PI.labeled.
Require Import PI.unlabeled.
Require Import PI.pi.
Require Import Coq.Classes.RelationClasses.
Require Import Coq.Init.Nat.


Theorem n_plus_1_le_0' : forall n : nat, (n + 1 <=? 0) = false.
Proof.
  intros n.
  destruct n; simpl.
  - (* Case n = 0 *) reflexivity.
  - (* Case n = S n' *) reflexivity.
Qed.

Theorem zero_lt_n_plus_1 : forall n : nat, (0 <? n + 1) = true.
Proof.
  intros n.
  destruct n.
  - (* Case n = 0 *)
    simpl. reflexivity.
  - (* Case n = S n' *)
    simpl. reflexivity.
Qed.

Axiom n_pm_1 : forall n : nat, n + 1 - 1 = n.

Lemma pop_z_push_o_id_:
  forall (P : pi)(n c : nat),
    (c_pop (n+1) c (c_push c P)) === P.
Proof.
  intros P.
  unfold pop.
  induction P.
  - reflexivity.
  - simpl.
    intros n c.
    apply CRepExtra.
    apply IHP.
  - simpl.
    intros n c.
    apply CResExtra.
    apply IHP.
  - simpl.
    intros n c.
    apply CParExtra.
    apply IHP1.
    apply IHP2.
  - induction c.
    simpl.
    unfold popN.
    rewrite zero_lt_n_plus_1 with (n :=n).
    rewrite n_pm_1 with (n :=n).
    apply CInExtra.
    apply IHP.
    simpl.

Lemma push_pop_id: 
  forall (P : pi)(n c : nat),
  (c_pop n c (c_push 0 P)) === P.
Proof.
  Admitted.
  (*intros P.
  induction P.
  - reflexivity.
  - simpl.
    intros n c.
    apply CRepExtra.
    apply IHP.
  - simpl.
    intros n c.
    apply CResExtra.
    apply IHP.
  - simpl.
    intros n c.
    apply CParExtra.
    apply IHP1.
    apply IHP2.
  - simpl.
    Admitted.*)



Lemma one : 
  forall (P Q R S T : pi),
    (P === Q /\  Q -()> S /\ R === S) ->
    (exists T : pi, P -()> T /\ R === T).
Proof.
  intros.
  destruct H as [H1 H2].
  destruct H2 as [H2 H3].
Admitted.

Lemma two' :
  forall (P Q P' Q' : pi) (n m : nat),
    (P -(n , m)> P' /\ Q -(n)> Q') ->
    Par P Q --> Par P' (pop m  Q').
Proof.
  intros P Q P' Q'.
  pose (H:= forall (n m : nat), P -( n, m )> P' /\ Q -( n )> Q').
  induction n.
  induction m.
  Admitted.

Lemma two :
  forall (P Q P' Q' : pi) (n m : nat),
    (P -(n , m)> P' /\ Q -(n)> Q') ->
    Par P Q --> Par P' (pop m  Q').
Proof.
  intros.
  destruct H as [H1 H2].
  induction H1.
  - induction H2. 
    + apply RCOM.
    + apply RCON with (Q:= Par (Par (Out n m P) P0) Q) (S := Par (Par P (pop m R)) Q). 
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
      fold c_pop.
      unfold push.
      apply push_pop_id.
    + apply RCON with 
        (Q := Res (Par (push (Out n m P)) P0)) 
        (S := Res (Par (push P) (pop (m+1) Q))).
      * apply CSym.
        apply CExt.
        reflexivity.
      * apply RRES. (* (1) Missing RCOM. RCOM would add pop to Q*) 
        apply RCOM.
        simpl.  
        admit.

        


Lemma three :
  forall (P Q P' Q' : pi) (n : nat),
    (P -(n)> P' /\ Q -[n]> Q') ->
    Par P Q --> Res (Par P'  Q').
Proof.
  intros.
  destruct H as [H1 H2].
  induction H1.
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