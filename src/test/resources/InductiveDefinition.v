
Require Import Omega.

Inductive Tree {A} :=
  Leaf(value: A)
| Node(l r : @ Tree A).

Fixpoint size {A} (t: @ Tree A) : nat :=
match t with
  Leaf _ => 1
| Node l r => 1 + (size l) + (size r)
end.

Lemma size_left: forall A (l r: @ Tree A), size (Node l r) > size l.
Proof.
  intros; induction l; simpl; omega.
Qed.
