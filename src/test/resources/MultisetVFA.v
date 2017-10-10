Require Import Coq.Arith.Arith.
Require Import Coq.Lists.List.

Definition value : Type := nat.

Definition multiset : Type := value -> nat.

Definition empty : multiset :=
   fun x => 0.

Definition union (a b : multiset) : multiset :=
   fun x => (a x) + (b x).

Definition singleton (v: value) : multiset :=
   fun x => if x =? v then 1 else 0.


Fixpoint contents (al: list value) : multiset :=
  match al with
  | a :: bl => union (singleton a) (contents bl)
  | nil => empty
  end.

