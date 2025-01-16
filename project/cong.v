Require Import PI.pi.
Require Import PI.debruijn.
Require Import Coq.Classes.RelationClasses.
Reserved Notation "P === Q" (at level 70).

Inductive cong : pi -> pi -> Prop :=
  (* Replication *)
  | CRep (P Q : pi): 
    cong Q (Rep P) -> cong Q (Par (Rep P) P)
  | CRepNil: 
    cong Nil (Rep Nil)
  (* Parralel composition *)
  | CParNil (P Q : pi): 
    cong P Q -> cong P (Par Q Nil)
  | CParSym (P Q R : pi): 
    cong P (Par Q R) -> cong P (Par R Q)
  | CParAsoc (P Q R S : pi):
    cong P (Par Q (Par R S)) -> cong P (Par (Par Q R) S)
  (* Extension *)
  | CExtNil: 
    cong Nil (Res Nil)
  | CExtPar (P Q R: pi): 
    cong P (Res (Par (push Q) R))  -> cong P (Par Q (Res R ))
  where "P === Q" := (cong P Q).

(* Compatibility *)
Axiom CParComp :
  forall (P Q R S: pi),
    P === R -> Q === S -> (Par P Q) === (Par R S).

Axiom CResComp :
  forall (P Q : pi),
    P === Q -> (Res P) === (Res Q).


(* Equivalence relation *)
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