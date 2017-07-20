

Definition pred (n : nat) : nat :=
  match n with
    | 0 => n
    | S u => u
  end.

Fixpoint add (n m : nat) : nat :=
  match n with
  | 0 => m
  | S p => S (p + m)
  end.

Fixpoint mul (n m : nat) : nat :=
  match n with
  | 0 => 0
  | S p => m + p * m
  end.


