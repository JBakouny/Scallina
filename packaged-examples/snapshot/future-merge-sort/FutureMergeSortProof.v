Load FutureMergeSort.


Function sort (l : list nat)
{ measure (fun l => length l) l } : list nat :=
match l with
  nil => nil
| x :: nil => x :: nil
| x :: y :: _ => let (l1, l2) := split l in
                 merge (sort l1, sort l2)
end.


(*

Work in progress...

*)