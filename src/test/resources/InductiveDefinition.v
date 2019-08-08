Require Import Omega.

Inductive Tree {A} :=
  Leaf(value: A)
| Node(l r : @ Tree A).

Fixpoint map {A B} (t: @ Tree A) (f: A -> B) : @ Tree B :=
match t with
  Leaf a => Leaf (f a)
| Node l r => Node (map l f) (map r f)
end.

Definition compose {A B C : Set}
(g : B -> C) (f : A -> B) (x : A) :=
  g (f x).

Lemma commute : forall {A B C : Set} (t: @ Tree A) (f: A -> B) (g: B -> C),
map t (compose g f) = map (map t f) g.
Proof.
  intros A B C t f g.
  induction t.
  - unfold map.
    unfold compose.
    reflexivity.
  - simpl.
    rewrite IHt1.
    rewrite IHt2.
    reflexivity.
Qed.

Fixpoint size {A} (t: @ Tree A) : nat :=
match t with
  Leaf _ => 1
| Node l r => 1 + (size l) + (size r)
end.

Lemma size_left: forall A (l r: @ Tree A), size (Node l r) > size l.
Proof.
  intros; induction l; simpl; omega.
Qed.

