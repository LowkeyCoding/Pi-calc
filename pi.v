Require Import Coq.Init.Nat.

Inductive pi : Type := 
 | par (p : pi) (q : pi)
 | Nil
 | rep (p : pi)
 | Out (n : nat) (m : nat) (p : pi)
 | In (n : nat) (p : pi)
 | res (p : pi).

Axiom SC_Nil_par : forall {p : pi},
  p = par (p) (Nil).

Axiom SC_Nil_res :
  Nil = res (Nil).


Axiom SC_par_reflex : forall {p q : pi},
  par (p) (q) = par (q) (p).

Axiom SC_par_Asoc : forall {p q r : pi},
  par (p) (par (q) (r)) = par (par (p) (q)) (r).

Axiom SC_rep : forall {p : pi}, 
  rep (p) = par (rep (p)) (p).

Axiom SC_rep_Nil :  
  rep (Nil) = Nil.


Axiom SC_rep_Duo : forall {p : pi},
  rep (p) = rep (rep (p)).


Axiom SC_rep_par : forall {p q : pi},
  rep (par (p) (q)) =  par(rep (p)) (rep(q)).


Fixpoint swap (p : pi) : pi :=
  match p with
  | Nil => Nil
  | rep q => rep (swap q)
  | res q => res (swap q)
  | par (q) (r) => par (swap q) (swap r)
  | In 0 q => In 1 (swap q)
  | In 1 q => In 0 (swap q)
  | Out 0 0 q => Out 1 1 (swap q)
  | Out 1 1 q => Out 0 0 (swap q)
  | Out 0 1 q => Out 1 0 (swap q)
  | Out 1 0 q => Out 0 1 (swap q)
  | Out 0 n q => Out 1 n (swap q)
  | Out n 0 q => Out n 1 (swap q)
  | Out 1 n q => Out 0 n (swap q)
  | Out n 1 q => Out n 0 (swap q)
  | In n q => In n (swap q)
  | Out n m q => Out n m (swap q)
  end.

Example swap_thing:
  swap (res (Out 1 0 (Nil))) = res(Out 0 1 (Nil)). 
Proof. simpl. reflexivity. Qed.

Example swap_thing1:
  swap (res (Out 1 7 (Nil))) = res(Out 0 7 (Nil)).
Proof. simpl. reflexivity. Qed.

Fixpoint push (p : pi) : pi := 
  match p with 
  | Nil => Nil
  | par (q) (r) => par (push q) (push r)
  | res q => res (push q)
  | In n q => In (n+1) (push q)
  | Out n m q => Out (n+1) (m+1) (push q)
  | rep q => rep (push q)
  end.

(*Notation "'popN' n t c" :=
  (if (leb n c) then n - 1 else (if (eqb n c) then t else n))(at level 200).
*)

Definition popN (n t c : nat) : nat :=
  (if (ltb c n) then n - 1 else (if (eqb n c) then t else n)) .

Fixpoint pop (n c: nat) (p : pi) : pi :=
 match p with
  | Nil => Nil
  | par q r => par (pop n c q) (pop n c r)
  | rep q => rep (pop n c q) 
  | Out m o q => Out (popN m n c) (popN o n c) (pop n c q)
  | In m q => In (popN m n c) (pop (n+1) (c+1) q)
  | res q => res (pop (n+1) (c+1) q)
  end.

Example pop_thing1:
  pop 4 0 (res (Out 1 0 (Nil))) = res(Out 5 0 (Nil)). 
Proof. simpl. unfold popN. simpl. reflexivity. Qed.


Example pop_thing2:
  pop 4 0 (In 0 (res (Out 1 0 (Nil)))) = In 4 (res(Out 1 0 (Nil))). 
Proof. simpl. unfold popN. simpl. reflexivity. Qed.

