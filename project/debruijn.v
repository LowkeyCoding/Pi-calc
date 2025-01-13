Require Import Coq.Init.Nat.
Require Import PI.pi.

Fixpoint c_swap (n : nat) (P : pi) : pi :=
  match P with
  | Nil => Nil
  | Rep Q => Rep (c_swap n Q)
  | Res Q => Res (c_swap (n+1) Q)
  | Par Q R => Par (c_swap n Q) (c_swap n R)
  | In a Q => In (if (a =? n) then (n+1) 
              else (if a =? (n+1) then n else a)) (c_swap (n+1) Q)
  | Out a b Q => Out (if a =? n then (n+1) else (if a =? (n+1) then n else a)) (if b =? n then (n+1) else (if b =? (n+1) then n else b)) (c_swap n Q)
  end.

Definition swap (P: pi) : pi := c_swap 0 P.

Example swap_thing:
  swap (Res (Out 1 0 (Nil))) = Res(Out 2 0 (Nil)). 
Proof. simpl. reflexivity. Qed.

Example swap_thing1:
  swap (Out 1 7 (Nil)) = Out 0 7 (Nil).
Proof. simpl. reflexivity. Qed.


Fixpoint c_push (n : nat) (P : pi) : pi := 
  match P with 
  | Nil => Nil
  | Par Q R => Par (c_push n Q) (c_push n R)
  | Res Q => Res (c_push (n+1) Q)
  | In m Q => In (if leb n m then (m+1) else m) (c_push (n+1) Q)
  | Out m l Q => Out (if leb n m then (m+1) else m) (if leb n l then (l+1) else l) (c_push n Q)
  | Rep Q => Rep (c_push n Q)
  end.

Definition pushN (n m : nat) : nat := (if (ltb m n) then m else m+1 ).
Definition push (P : pi) : pi := c_push 0 P.

(*Notation "'popN' n t c" :=
  (if (leb n c) then n - 1 else (if (eqb n c) then t else n))(at level 200).
*)

Definition popN (n t c : nat) : nat :=
  (if (ltb c n) then n - 1 else (if (eqb n c) then t else n)).

Fixpoint c_pop (n c: nat) (P : pi) : pi :=
 match P with
  | Nil => Nil
  | Par Q R => Par (c_pop n c Q) (c_pop n c R)
  | Rep Q => Rep (c_pop n c Q) 
  | Out m o Q => Out (popN m n c) (popN o n c) (c_pop n c Q)
  | In m Q => In (popN m n c) (c_pop (n+1) (c+1) Q)
  | Res Q => Res (c_pop (n+1) (c+1) Q)
  end.

Definition pop (n : nat) (P : pi) : pi := c_pop n 0 P.

Example pop_thing1:
  pop 4 (Res (Out 1 0 (Nil))) = Res(Out 5 0 (Nil)). 
Proof. simpl. unfold popN. simpl. reflexivity. Qed.


Example pop_thing2:
  pop 4 (In 0 (Res (Out 1 0 (Nil)))) = In 4 (Res(Out 1 0 (Nil))). 
Proof. simpl. unfold popN. simpl. reflexivity. Qed.