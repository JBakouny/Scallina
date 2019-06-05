Require Import List.
Require Import Nat.

Open Scope type_scope.

Inductive RandomAccessList E :=
| Empty
| Cons (one : bool) (e: E) (s : RandomAccessList (E * E)).

Arguments Empty {E}.
Arguments Cons {E} _ _ _.

Fixpoint length {E} (l : RandomAccessList E) : nat := match l with
| Empty => 0
| Cons one e s => 2 * (length s) + (if one then 1 else 0)
end.

Fixpoint get {E} (i : nat) (l : RandomAccessList E) : option E := match l with
| Empty => None
| Cons one e s =>
if (one) then
  if (eqb i 0) then Some e
  else
    match get (div (i - 1) 2) s with
    | None => None
    | Some (x1, x2) => 
    Some (if eqb (modulo i 2) 1 then x1 else x2)
    end
else
  match get (div i 2) s with
  | None => None
  | Some (x1, x2) =>  
  Some (if eqb (modulo i 2) 0 then x1 else x2)
  end
end.

Fixpoint add {E} (x : E) (l : RandomAccessList E) : RandomAccessList E :=
match l with 
| Empty => Cons true x Empty
| Cons one e s =>
  if one then
    Cons false x (add (x, e) s)
  else
    Cons true x s
end.
