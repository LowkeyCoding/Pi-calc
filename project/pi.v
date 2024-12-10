Inductive pi : Type := 
 | Nil
 | Rep (P : pi)
 | Res (P : pi)
 | Par (P Q : pi)
 | In (n : nat) (P : pi)
 | Out (n m : nat) (P : pi).