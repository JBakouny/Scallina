Require Import List.

Fixpoint map {A B} (l: list A) (f: A -> B) : list B :=
match l with
  nil => nil
| x :: xs => (f x) :: (map xs f)
end.