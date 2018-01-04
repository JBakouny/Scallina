
Require Export Coq.Lists.List.
Require Export Coq.Arith.Arith.
Require Export Recdef.
Load FutureUtils.

Fixpoint split {A} (l: list A) : (list A) * (list A) :=
match l with
  nil => (nil, nil)
| x :: nil => (x :: nil, nil)
| x :: y :: xs => let (l1, l2) := (split xs) in (x :: l1, y :: l2)
end.

Function merge (z: (list nat) * (list nat)) 
{ measure (fun z => length (fst z) + length (snd z)) z } : list nat :=
 let (l1, l2) := z in
 match l1 with
 | nil => l2
 | x1::l1_ =>
   match l2 with
   | nil => l1
   | x2::l2_ =>
     if x1 <=? x2 then x1 :: merge (l1_, l2)
     else x2 :: merge (l1, l2_)
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

Fixpoint msort (l : list nat) (n : nat) {struct n} : Future (list nat) :=
match l, n with
  nil, _ => future nil
| x :: nil, _ => future (x :: nil)
| x :: y :: _, S n1 => let (l1, l2) := split l in
                       fut_flat_map 
                       (fun (r1 : list nat) =>
                         fut_map
                         (fun (r2 : list nat) => merge (r1,r2))
                         (msort l2 n1)
                       )
                       (msort l1 n1)
| _ :: _ :: _, 0 => future nil
end.

Definition mergeSort (l : list nat) : Future (list nat) := msort l (length l).
