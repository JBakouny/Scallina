Require Import Coq.Lists.List.
Require Import Coq.Arith.Arith.

Definition f (x : nat) : nat := x * 3.

Definition l : list nat := 7 :: nil.

Definition testMap := map f l.

Definition g (x : nat) : bool := if x <? 2 then true else false.

Definition testFilter := filter g l.

Definition f2 (x : nat) : list nat := (x * 2) :: (x * 3) :: nil.

Definition testFlatMap := flat_map f2 l.


