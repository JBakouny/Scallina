Inductive Nat := Zero | S (n : Nat).

Definition pred (n : Nat) : Nat :=
  match n with
    | Zero => n
    | S u => u
  end.

Fixpoint add (n m : Nat) : Nat :=
  match n with
  | Zero => m
  | S p => S (add p m)
  end.

Fixpoint mul (n m : Nat) : Nat :=
  match n with
  | Zero => Zero
  | S p => add m (mul p m)
  end.

Fixpoint sub (n m : Nat) : Nat :=
  match n, m with
  | S k, S l => sub k l
  | _, _ => n
  end.

