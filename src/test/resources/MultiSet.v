(*
Inspired from:
https://www.cs.princeton.edu/~appel/vfa/Multiset.html
*)

Require Import Coq.Arith.Arith.
Require Import Coq.Lists.List. 

Definition empty : nat -> nat :=
   fun x => 0.

Definition union (a b : nat -> nat) : nat -> nat :=
   fun x => (a x) + (b x).

Definition singleton (v: nat) : nat -> nat :=
   fun x => if x =? v then 1 else 0.

Fixpoint contents (al: list nat) : nat -> nat :=
  match al with
  | a :: bl => union (singleton a) (contents bl)
  | nil => empty
  end.

Fixpoint list_delete (al: list nat) (v: nat) : list nat :=
  match al with
  | x::bl => if x =? v then bl else x :: list_delete bl v
  | nil => nil
  end.

Definition multiset_delete (m: nat -> nat) (v: nat) :=
   fun (x : nat) => if x =? v then pred(m x) else m x.

