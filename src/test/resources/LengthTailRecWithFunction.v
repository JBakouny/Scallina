Require Import List.
Require Import Arith.
Require Import Recdef.
Require Import Omega.

Function lenTailrec {A} (xs : list A) (n : nat) { measure (fun xs => length(xs)) xs } : nat :=
match xs with
| nil => n
| _ :: ys => lenTailrec ys (1 + n)
end.
Proof.
  intros.
  simpl.
  omega.
Qed.