
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

Definition bind_option {A B} (f : A -> option B) (x : option A) : 
  option B := 
  match x with 
   | Some x => f x
   | None => None
  end.

Definition bind_option2 {A B C} (f : A -> B -> option C) 
   (x : option (A * B)) : option C :=
bind_option
  (fun yz : A * B =>
   let (y, z) := yz : A * B in f y z) x.

Fixpoint fold {P : Type} (f : P)
  (f0 : nat -> P -> P) (n : nat) :=
  match n with
  | 0 => f
  | S n0 => f0 n0 (fold f f0 n0)
  end.

Definition program (Q : Queue) (n : nat) :=
let q :=
  fold (empty Q) (push Q) (S n) in
let q0 :=
  fold
    (Some q)
    (fun (_ : nat) (q0 : option Q.(t)) =>
     bind_option
       (fun q1 : Q.(t) =>
        bind_option2
          (fun (x : nat) (q2 : Q.(t)) =>
           bind_option2
             (fun (y : nat) (q3 : Q.(t)) =>
              Some (push Q (x + y) q3))
             (pop Q q2)) (pop Q q1)) q0) n in
bind_option
  (fun q1 : Q.(t) => option_map fst (pop Q q1))
  q0
.
