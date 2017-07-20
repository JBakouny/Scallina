Require Import ZArith.

Fixpoint lenTailrec {A} (xs : list A) (n : Z) : Z :=
match xs with
| nil => n
| cons _ ys => lenTailrec ys (1 + n)
end.

