
Require Import Coq.Arith.PeanoNat.


Inductive List :=
  Cons (head: nat) (tail: List)
| Nil.

Inductive AbsQueue :=
  Queue (front: List) (read: List).

Fixpoint size (list: List) : nat :=
match list with
  Nil => 0
| Cons _ xs => 1 + (size xs)
end.

Fixpoint concat(l1 l2: List) : List :=
match l1 with
  Nil => l2
| Cons x xs => Cons x (concat xs l2)
end.

Fixpoint reverse(l: List) : List :=
match l with
  Nil => Nil
| Cons x xs => concat (reverse xs) (Cons x Nil)
end.

Definition asList (queue: AbsQueue) : List :=
match queue with
  Queue front rear => concat front (reverse rear)
end.

Definition amortizedQueue (front rear: List) : AbsQueue :=
  if (size rear) <=? (size front) then
    Queue front rear
  else
    Queue (concat front (reverse rear)) Nil.

Definition enqueue (queue: AbsQueue) (elem: nat) : AbsQueue :=
match queue with
  Queue front rear => amortizedQueue front (Cons elem rear)
end.

Definition tail (queue: AbsQueue) : option AbsQueue :=
match queue with
  Queue (Cons f fs) rear => Some (amortizedQueue fs rear)
| Queue Nil _ => None
end.

Definition front (queue: AbsQueue) : option nat :=
match queue with
  Queue (Cons f _) _ => Some f
| Queue Nil _ => None
end.
