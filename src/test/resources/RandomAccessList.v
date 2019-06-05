Require Import List.
Require Import Arith.

Inductive Tree T :=
| Leaf (v : T)
| Node (v : T) (l : Tree T) (r : Tree T).

Arguments Leaf {T}.
Arguments Node {T} _ _ _.

Inductive RAList T :=
| RaNil
| RaCons (t: Tree T) (e: nat) (l: RAList T).

Arguments RaNil  {T}.
Arguments RaCons {T} _ _ _.

Definition head {T} (l : RAList T) : option T :=
match l with
| RaNil => None
| RaCons t _ _ =>
  match t with
  | Leaf x => Some x
  | Node x _ _ => Some x
  end
end.

Definition cons {T} (x : T) (l : RAList T) : RAList T :=
match l with
| RaNil => RaCons (Leaf x) 0 l
| RaCons t s RaNil => RaCons (Leaf x) 0 l
| RaCons t1 h1 (RaCons t2 h2 q) =>
  if h1 =? h2 then RaCons (Node x t1 t2) (1 + h1) q
  else RaCons ( Leaf x ) 0 l
end.

Definition tail {T} (l : RAList T) : RAList T :=
match l with
| RaNil => RaNil
| RaCons t h q =>
  match t with
  | Leaf _ => q
  | Node _ t1 t2 =>
  RaCons t1 ( h - 1) ( RaCons t2 ( h - 1) q )
  end
end.

