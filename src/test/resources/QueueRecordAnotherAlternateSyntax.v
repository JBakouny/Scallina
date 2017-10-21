(*
Inspired from:
https://github.com/parametricity-coq/paramcoq/blob/master/test-suite/ListQueue.v
*)

Require Import Coq.Lists.List.

Record Queue :=
Build_Queue {
  T : Type;
  push : nat -> T -> T;
  pop : T -> option (nat * T);
  empty : T
}.

Arguments Build_Queue {T} _ _ _.

Definition ListQueue := Build_Queue
  (fun (x : nat) (l : list nat) => x :: l)
  (fun l => 
    match rev l with
      | nil => None 
      | hd :: tl => Some (hd, rev tl) end)
  nil
.

Definition DListQueue := Build_Queue
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
  (nil, nil)
.

Fixpoint insertElems (Q: Queue) (q: Q.(T)) (n: nat) : Q.(T) :=
match n with
  0 => q
| S m => Q.(push) n (insertElems Q q m)
end.

Definition createQueue (Q: Queue) (n: nat) : Q.(T) := insertElems Q Q.(empty) n.

Definition createListQueue(n: nat) := createQueue ListQueue n.

Definition createDListQueue(n: nat) := createQueue DListQueue n.

