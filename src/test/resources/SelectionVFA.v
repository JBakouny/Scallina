
(*
From Software Foundations, volume 3:
Verified Functional Algorithms by Andrew W. Appel.

Selection Sort:
https://softwarefoundations.cis.upenn.edu/vfa-current/Selection.html


Changes to the original code:
- Add type information to all function parameters.
- Add function return types.
- Replace names containing non-ASCII characters by equivalent names with ASCII-only characters.
- Add parenthesis to enforce the needed precedence where needed.
- Split the implementation and its proof into two distinct files.
*)

Require Import Coq.Arith.Arith.
Require Import Coq.Lists.List.

Fixpoint select (x: nat) (l: list nat) : nat * (list nat) :=
match l with
|  nil => (x, nil)
|  h::t => if x <=? h 
               then let (j, l1) := select x t in (j, h::l1)
               else let (j,l1) := select h t in (j, x::l1)
end.


Fixpoint selsort (l : list nat) (n : nat) {struct n} : list nat :=
match l, n with
| x::r, S n1 => let (y,r1) := select x r
               in y :: selsort r1 n1
| nil, _ => nil
| _::_, 0 => nil
end.



Definition selection_sort (l : list nat) : list nat := selsort l (length l).

