Require Import Coq.Init.Nat.
Require Import PI.pi.
Fixpoint swap (n : nat) (P : pi) : pi :=
  match P with
  | Nil => Nil
  | Rep Q => Rep (swap n Q)
  | Res Q => Res (swap (n+1) Q)
  | Par Q R => Par (swap n Q) (swap n R)
  | In a Q => In (if (a =? n) then (n+1) 
              else (if a =? (n+1) then n else a)) (swap (n+1) Q)
  | Out a b Q => Out (if a =? n then (n+1) else (if a =? (n+1) then n else a)) (if b =? n then (n+1) else (if b =? (n+1) then n else b)) (swap n Q)
  end.

Example swap_thing:
  swap 0 (Res (Out 1 0 (Nil))) = Res(Out 2 0 (Nil)). 
Proof. simpl. reflexivity. Qed.

Example swap_thing1:
  swap 0 (Out 1 7 (Nil)) = Out 0 7 (Nil).
Proof. simpl. reflexivity. Qed.


Fixpoint push (n : nat) (P : pi) : pi := 
  match P with 
  | Nil => Nil
  | Par Q R => Par (push n Q) (push n R)
  | Res Q => Res (push (n+1) Q)
  | In m Q => In (if leb n m then (m+1) else m) (push (n+1) Q)
  | Out m l Q => Out (if leb n m then (m+1) else m) (if leb n l then (l+1) else l) (push n Q)
  | Rep Q => Rep (push n Q)
  end.

(*Notation "'popN' n t c" :=
  (if (leb n c) then n - 1 else (if (eqb n c) then t else n))(at level 200).
*)

Definition popN (n t c : nat) : nat :=
  (if (ltb c n) then n - 1 else (if (eqb n c) then t else n)) .

Fixpoint pop (n c: nat) (P : pi) : pi :=
 match P with
  | Nil => Nil
  | Par Q R => Par (pop n c Q) (pop n c R)
  | Rep Q => Rep (pop n c Q) 
  | Out m o Q => Out (popN m n c) (popN o n c) (pop n c Q)
  | In m Q => In (popN m n c) (pop (n+1) (c+1) Q)
  | Res Q => Res (pop (n+1) (c+1) Q)
  end.

Example pop_thing1:
  pop 4 0 (Res (Out 1 0 (Nil))) = Res(Out 5 0 (Nil)). 
Proof. simpl. unfold popN. simpl. reflexivity. Qed.


Example pop_thing2:
  pop 4 0 (In 0 (Res (Out 1 0 (Nil)))) = In 4 (Res(Out 1 0 (Nil))). 
Proof. simpl. unfold popN. simpl. reflexivity. Qed.