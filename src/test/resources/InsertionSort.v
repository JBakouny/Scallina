(*

Inspired from:
https://www.cs.princeton.edu/~appel/vfa/Sort.html

*)

Require Import Coq.Arith.Arith.
Require Import Coq.Lists.List. 

Fixpoint insert (i:nat) (l: list nat) : list nat := 
  match l with
  | nil => i::nil
  | h::t => if i <=? h then i::h::t else h :: insert i t
 end.

Fixpoint sort (l: list nat) : list nat :=
  match l with
  | nil => nil
  | h::t => insert h (sort t)
end.

