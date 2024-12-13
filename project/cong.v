Require Import PI.pi.
Require Import PI.debruijn.
Require Import Coq.Classes.RelationClasses.
Reserved Notation "P === Q" (at level 70).

Inductive cong : pi -> pi -> Prop :=
  | CParNil (P Q : pi)      : cong P Q -> cong P (Par Q Nil)
  | CNilRes                 : cong Nil (Res Nil)
  | CExt    (P Q R: pi)     : cong P (Res (Par (push Q) R))  -> cong P (Par Q (Res R ))
  | CParSym (P Q R : pi)    : cong P (Par Q R) -> cong P (Par R Q)
  | CParAsoc (P Q R S : pi) : cong P (Par Q (Par R S)) -> cong P (Par (Par Q R) S)
  | CRep (P Q : pi)         : cong Q (Rep P) -> cong Q (Par (Rep P) P)
  | CRepNil                 : cong Nil (Rep Nil)
  | CRepRep (P Q : pi)      : cong Q (Rep P) -> cong Q (Rep (Rep P))
  | CRepPar (P Q R: pi)     : cong P (Rep (Par Q R)) -> cong P (Par(Rep Q) (Rep R))
  | CParExtra (P Q R S: pi) : cong P R -> cong Q S -> cong (Par P Q) (Par R S)
  | CResExtra (P Q : pi)    : cong P Q -> cong (Res P) (Res Q)
  | CRepExtra (P Q : pi)    : cong P Q -> cong (Rep P) (Rep Q)
  | CInExtra  (n : nat)(P Q : pi) : cong P Q -> cong (In n P) (In n Q)
  | COutExtra  (n m: nat)(P Q : pi) : cong P Q -> cong (Out n m P) (Out n m Q) 
  (*| CPushPop  (P Q : pi) (n : nat) : cong P Q -> cong (pop n (push P)) Q 
  | CPopSwap  (P Q : pi ) (n m : nat) : cong (pop m n P) Q -> cong (pop m (n+1) (swap n P)) Q *)
  where "P === Q" := (cong P Q).

Axiom CRef : 
  forall (P : pi),
    P === P.

Instance cref : Reflexive cong.
Proof.
  unfold Reflexive.
  apply CRef.
Qed.

Axiom CSym :
  forall (P Q : pi),
    P === Q -> Q === P.

Instance csym : Symmetric cong.
Proof.
  unfold Symmetric.
  apply CSym.
Qed.

Axiom CTrans :
  forall (P Q R : pi),
    P === Q -> Q === R -> P === R.

Instance ctrans : Transitive cong.
Proof.
  unfold Transitive.
  apply CTrans.
Qed.

