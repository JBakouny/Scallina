Require Import Coq.Lists.List.


Record Queue := {
  t : Type;
  empty : t;
  push (x: nat) (l: t): t;
  pop (l: t): option (nat * t) 
}.


Definition ListQueue : Queue := {|
  t := list nat;
  empty := nil;
  push x l := x :: l;
  pop l :=
    match rev l with
      | nil => None
      | hd :: tl => Some (hd, rev tl)
    end
|}.

Definition DListQueue : Queue := {|
  t := (list nat) * (list nat); 
  empty := (nil, nil);
  push x l := 
    let (back, front) := l in 
    (x :: back,front);
  pop l :=
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

