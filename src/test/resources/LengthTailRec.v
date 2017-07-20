
Require Import List.
Require Import Omega.

Fixpoint lenTailrec {A} (xs : list A) (n : nat) : nat :=
match xs with
| nil => n
| _ :: ys => lenTailrec ys (1 + n)
end.


Lemma lenTailrec_increases:
forall (A : Type) (xs : list A) big small n,
big > small -> lenTailrec xs small >= n -> lenTailrec xs big >= n.
Proof.
intros A xs.
induction xs.
- simpl; intuition.
- simpl.
  intros.
  apply IHxs with (small := S small).
  + intuition.
  + apply H0.
Qed.

Lemma lenTailrec_result: forall (A : Type) (xs : list A) n, lenTailrec xs n >= n.
Proof.
intros A xs.
induction xs.
- simpl.
  intuition.
- simpl.
  intros n.
  apply lenTailrec_increases with (small := n).
  + intuition.
  + apply IHxs.
Qed.

(*
Lemma lenTailrec_increases: forall xs a b, a > b -> lenTailrec xs a >= lenTailrec xs b.
Proof.
intros xs.
induction xs.
- simpl.
  intuition.
- simpl.
  intros.
  apply IHxs.
  omega.
Qed.

*)