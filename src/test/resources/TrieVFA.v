Require Import Coq.Arith.Arith.
Require Import Coq.Lists.List.

Fixpoint loop (input: list nat) (c: nat) (table: total_map bool) : nat :=
  match input with
  | nil => c
  | a::al => if table a
                  then loop al (c+1) table
                  else loop al c (t_update table a true)
 end.

Definition collisions (input: list nat) : nat := 
       loop input 0 (t_empty false).


