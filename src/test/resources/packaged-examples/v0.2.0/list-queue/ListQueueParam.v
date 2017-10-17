
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