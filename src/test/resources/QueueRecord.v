(*
Inspired from:
https://github.com/parametricity-coq/paramcoq/blob/master/test-suite/ListQueue.v
*)

Require Import Coq.Lists.List.

Record Queue :=
Build_Queue {
  T : Type;
  empty : T;
  push : nat -> T -> T;
  pop : T -> option (nat * T)
}.


Definition ListQueue := Build_Queue
  (list nat) 
  nil 
  (fun (x : nat) (l : list nat) => x :: l)
  (fun l => 
    match rev l with
      | nil => None 
      | hd :: tl => Some (hd, rev tl) end)
.

Definition DListQueue := Build_Queue
  ((list nat) * (list nat)) 
  (nil, nil)
  (fun (x : nat) (l : (list nat) * (list nat)) => 
    let (back, front) := l in 
    (x :: back,front))
  (fun l =>
    let (back, front) := l in 
    match front with 
      | nil => 
         match rev back with
            | nil => None
            | hd :: tl => Some (hd, (nil, tl))
         end
      | hd :: tl => Some (hd, (back, tl))
    end)
.

Fixpoint insertElems (Q: Queue) (q: Q.(T)) (n: nat) : Q.(T) :=
match n with
  0 => q
| S m => Q.(push) n (insertElems Q q m)
end.

Definition createQueue (Q: Queue) (n: nat) : Q.(T) := insertElems Q Q.(empty) n.

Definition createListQueue(n: nat) := createQueue ListQueue n.

Definition createDListQueue(n: nat) := createQueue DListQueue n.

