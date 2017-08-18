(*

Inspired from:
https://www.cs.princeton.edu/~appel/vfa/Selection.html

*)

Require Import Coq.Arith.Arith.
Require Import Coq.Lists.List.

Fixpoint select (x: nat) (l: list nat) : nat * list nat :=
match l with
|  nil => (x, nil)
|  h::t => if x <=? h 
               then let (j, l2) := select x t in (j, h::l2)
               else let (j, l2) := select h t in (j, x::l2)
end.

Fixpoint selsort (l: list nat) (n: nat) {struct n} : list nat :=
match l, n with
| x::r, S n2 => let (y,r2) := select x r
               in y :: selsort r2 n2
| nil, _ => nil
| _::_, 0 => nil  (* Oops!  Ran out of fuel! *)
end.

Definition selection_sort (l: list nat) := selsort l (length l).
