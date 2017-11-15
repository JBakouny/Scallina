
Require Import Coq.Lists.List.
Require Import Coq.Arith.Arith.
Require Import Recdef.

Function merge {A} (less: A -> A -> bool) (z: (list A) * (list A)) 
{ measure (fun z => length (fst z) + length (snd z)) z } : list A :=
 let (l1, l2) := z in
 match l1 with
 | nil => l2
 | x1::l1_ =>
   match l2 with
   | nil => l1
   | x2::l2_ =>
     if less x1 x2 then x1 :: merge less (l1_, l2)
     else x2 :: merge less (l1, l2_)
   end
 end.

Proof.
 - intros.
   auto.
 - intros.
   simpl.
   apply Lt.lt_n_S.
   apply Plus.plus_lt_compat_l.
   auto.
Qed.