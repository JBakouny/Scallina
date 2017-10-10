

Require Import Coq.Arith.Arith.
Require Import Coq.Lists.List.

Fixpoint select (x: nat) (l: list nat) : nat * list nat :=
match l with
|  nil => (x, nil)
|  h::t => if x <=? h 
               then let (j, l') := select x t in (j, h::l')
               else let (j,l') := select h t in (j, x::l')
end.


Fixpoint selsort l n {struct n} :=
match l, n with
| x::r, S n' => let (y,r') := select x r
               in y :: selsort r' n'
| nil, _ => nil
| _::_, O => nil  (* Oops!  Ran out of fuel! *)
end.



Definition selection_sort l := selsort l (length l).

