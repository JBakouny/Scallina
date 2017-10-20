
(*
From the Coq Parametricity plugin:
https://github.com/parametricity-coq/paramcoq/blob/master/test-suite/ListQueue.v

Download the latest version of the Parametricity plugin here:
https://github.com/CohenCyril/paramcoq


Changes to the original code:
- Add type information to all function parameters.
- Add function return types.
- Add parenthesis to enforce the needed precedence where needed.
- Remove the type coercion from "t :> Type".
- Implement record attributes using anynomous functions.
This is not a requirement of Scallina, but it is what is mostly used in the origial code.
- Replace "cons" by "::".
- Inline all used-defined Coq notations.
- Create a non-depdently typed custom nat_rect function to use in the program.
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

Definition bind_option {A B}
(x : option A)
(f : A -> option B) : option B := 
  match x with 
   | Some x => f x
   | None => None
  end.

Definition bind_option2 {A B C}
(x : option (A * B))
(f : A -> B -> option C) : option C :=
bind_option x
  (fun (yz : A * B) =>
   let (y, z) := yz in f y z).


Definition option_map {A B}
(o : option A) (f : A -> B)
: option B :=
  match o with
    | Some a => Some (f a)
    | None => None
  end.


Fixpoint nat_rect {P : Type}
  (op : nat -> P -> P) (n : nat) (x : P) : P :=
  match n with
  | 0 => x
  | S n0 => op n0 (nat_rect op n0 x)
  end.

Definition sumElems(Q : Queue)(q0: option Q.(t)) : option Q.(t) :=
bind_option q0
(fun (q1 : Q.(t)) =>
 let x_q1 := Q.(pop) q1
 in
 bind_option2 x_q1
  (fun (x : nat) (q2 : Q.(t)) =>
   let y_q3 := Q.(pop) q2
   in
   bind_option2 y_q3
    (fun (y : nat) (q3 : Q.(t)) =>
      let sum := x + y
      in Some (Q.(push) sum q3)
    )
  )
)
.

Definition program (Q : Queue) (n : nat) : option nat :=
(* q := 0::1::2::...::n *)
let q : Q.(t) :=
  nat_rect Q.(push) (S n) Q.(empty)
in
let q0 : option Q.(t) :=
  nat_rect
    (fun _ (q0: option Q.(t)) => sumElems Q q0)
    n
    (Some q)
in
bind_option q0
  (fun (q1 : Q.(t)) => option_map (Q.(pop) q1) fst)
.



