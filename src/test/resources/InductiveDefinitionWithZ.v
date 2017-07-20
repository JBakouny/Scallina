
Require Import Omega.

Inductive Tree {A} :=
  Leaf(value: A)
| Node(l r : @ Tree A).

Fixpoint size {A} (t: @ Tree A) : Z :=
match t with
  Leaf _ => 1
| Node l r => 1 + (size l) + (size r)
end.

