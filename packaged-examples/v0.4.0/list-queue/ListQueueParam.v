
(*
From the Coq Parametricity plugin:
https://github.com/parametricity-coq/paramcoq/blob/master/test-suite/ListQueue.v

Download the latest version of the Parametricity plugin here:
https://github.com/CohenCyril/paramcoq


Changes to the original code required by Scallina's coding conventions:
- Add type information to all function parameters.
- Add function return types.
- Add parenthesis to enforce a given precedence where needed.
- Remove the type coercion from "t :> Type".
- Replace "cons" by "::".
- Inline all used-defined Coq notations.
- Implement the "loop" function: a non-depdently typed version of "nat_rect".

Changes done to the original code not required by Scallina:
- Implement record attributes using anynomous functions.
Scallina only requires that record instance attributes be implemented
using the same signature with which they were defined in the Record.
- Inline all monadic operators on Option.
This was done for the readability of the source Coq code.
*)


Require Import List.


Record Queue := {
  t : Type;
  empty : t;
  push : nat -> t -> t;
  pop : t -> option (nat * t) 
}.


Definition ListQueue : Queue := {|
  t := list nat; 
  empty := nil; 
  push := fun x l => x :: l;
  pop := fun l => 
    match rev l with
      | nil => None 
      | hd :: tl => Some (hd, rev tl) end
|}.

Definition DListQueue : Queue := {|
  t := (list nat) * (list nat); 
  empty := (nil, nil);
  push := fun x l => 
    let (back, front) := l in 
    (x :: back,front);
  pop := fun l =>
    let (back, front) := l in 
    match front with 
      | nil => 
         match rev back with
            | nil => None
            | hd :: tl => Some (hd, (nil, tl))
         end
      | hd :: tl => Some (hd, (back, tl))
    end
|}.

(*
A non-dependently typed version of nat_rect.
*)
Fixpoint loop {P : Type}
  (op : nat -> P -> P) (n : nat) (x : P) : P :=
  match n with
  | 0 => x
  | S n0 => op n0 (loop op n0 x)
  end.

(*
This method pops two elements from the queue q and
then pushes their sum back into the queue.
*)
Definition sumElems(Q : Queue)(q: option Q.(t)) : option Q.(t) :=
match q with
| Some q1 =>
  match (Q.(pop) q1) with
  | Some (x, q2) =>
    match (Q.(pop) q2) with
    | Some (y, q3) => Some (Q.(push) (x + y) q3)
    | None => None
    end
  | None => None
  end
| None => None
end.

(*
This programs creates a queue of n+1 consecutive numbers (from 0 to n)
and then returns the sum of all the elements of this queue.
*)
Definition program (Q : Queue) (n : nat) : option nat :=
(* q := 0::1::2::...::n *)
let q :=
  loop Q.(push) (S n) Q.(empty)
in
let q0 :=
  loop
  (fun _ (q0: option Q.(t)) => sumElems Q q0)
  n
  (Some q)
in
match q0 with
| Some q1 =>
  match (Q.(pop) q1) with 
  | Some (x, q2) => Some x
  | None => None
  end
| None => None
end
.



