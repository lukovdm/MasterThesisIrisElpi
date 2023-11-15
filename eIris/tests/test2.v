Definition my_forall {A} (P : A -> Prop) : Prop := forall x, P x.

Reserved Notation "∀ x .. y , P"
  (at level 10, x binder, y binder, P at level 200,
  format "'[  ' '[  ' ∀  x  ..  y ']' ,  '/' P ']'").

Local Notation "∀ x .. y , P" :=
    (my_forall (fun x => .. (my_forall (fun y => P)) ..)).

Context (P : nat -> Prop).
Check my_forall (fun x => P x).
Check my_forall P.

Print sigT.